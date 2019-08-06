module Language.PureScript.CoreFn.Optimizer (optimizeCoreFn) where

import Protolude hiding (Type)

import Data.List (lookup)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (maybe)
import qualified Data.Set as S
import Data.Set (Set)
import Language.PureScript.AST.Literals
import Language.PureScript.AST.SourcePos
import Language.PureScript.CoreFn.Ann
import Language.PureScript.CoreFn.Binders
import Language.PureScript.CoreFn.Expr
import Language.PureScript.CoreFn.Module
import Language.PureScript.CoreFn.Traversals
import Language.PureScript.Names (Ident(UnusedIdent), Qualified(Qualified))
import Language.PureScript.Label
import Language.PureScript.Types
import qualified Language.PureScript.Constants as C

-- |
-- CoreFn optimization pass.
--
optimizeCoreFn :: Module Ann -> Module Ann
optimizeCoreFn m = m {moduleDecls = optimizeModuleDecls $ moduleDecls m}

optimizeModuleDecls :: [Bind Ann] -> [Bind Ann]
optimizeModuleDecls = map transformBinds
  where
  (transformBinds, _, _) = everywhereOnValues identity transformExprs identity
  -- Recursively apply optimizers until no changes are made.
  transformExprs = go (1000 :: Int)
  -- TODO: A log would be helpful if this case is hit.
  go 0 x = x
  go i x = maybe x (go (i - 1)) $
    (         optimizeAbsAppToLet
    `thenTry` optimizeUnusedPartialFn
    `thenTry` optimizeClosedRecordUpdate
    ) x
  thenTry f g x = maybe (g x) (\y -> g y <|> pure y) (f x)

optimizeClosedRecordUpdate :: Expr Ann -> Maybe (Expr Ann)
optimizeClosedRecordUpdate (ObjectUpdate a@(_, _, Just t, _) r updatedFields) =
  case closedRecordFields t of
    Nothing -> Nothing
    Just allFields -> Just (Literal a (ObjectLiteral (map f allFields)))
      where f (Label l) = case lookup l updatedFields of
              Nothing -> (l, Accessor (nullSourceSpan, [], Nothing, Nothing) l r)
              Just e -> (l, e)
optimizeClosedRecordUpdate _ = Nothing

-- | Return the labels of a closed record, or Nothing for other types or open records.
closedRecordFields :: Type a -> Maybe [Label]
closedRecordFields (TypeApp _ (TypeConstructor _ C.Record) row) =
  collect row
  where
    collect :: Type a -> Maybe [Label]
    collect (REmpty _) = Just []
    collect (RCons _ l _ r) = collect r >>= return . (l :)
    collect _ = Nothing
closedRecordFields _ = Nothing

-- | See https://github.com/purescript/purescript/issues/3157
optimizeUnusedPartialFn :: Expr a -> Maybe (Expr a)
optimizeUnusedPartialFn (Let _
  [NonRec _ UnusedIdent _]
  (App _ (App _ (Var _ (Qualified _ UnusedIdent)) _) originalCoreFn)) =
  Just originalCoreFn
optimizeUnusedPartialFn _ = Nothing

-- | (\a -> m) b ==> let a = b in m
optimizeAbsAppToLet :: Expr a -> Maybe (Expr a)
optimizeAbsAppToLet (App an1 (Abs _ a m) b) = Just (Let an1 [NonRec an1 a b] m)
optimizeAbsAppToLet _ = Nothing

-- | let U; a = b; V in m ==> let U; V[b/a] in m[b/a]
-- |   * If 'a' is used only once and not in a recursive group.
-- optimizeInlineLet :: Expr a -> Maybe (Expr a)
-- generalise to n bindings...
-- optimizeInlineLet (Let _ [NonRec _ a b] m) = if a sites in m <= 1 then substitute b a m

type Scoped a = (Set Ident, Map Ident Int, a)

scopeExpr :: Expr a -> Expr (Scoped a)
scopeExpr (Literal an1 x) =
  let (bound, free, y) = scopeLiteral x
  in  Literal (bound, free, an1) y
scopeExpr (Constructor an1 tName cName fNames) =
  Constructor (S.empty, M.empty, an1) tName cName fNames
scopeExpr (Accessor an1 prop x) =
  let y = scopeExpr x
      (_, free, _) = extractAnn y
  in  Accessor (S.empty, free, an1) prop y
scopeExpr (ObjectUpdate an1 obj xs) =
  let obj' = scopeExpr obj
      (_, objFree, _) = extractAnn obj'
      (ysFree, ys) = scopeLabeledExprs xs
  in  ObjectUpdate (S.empty, M.unionWith (+) objFree ysFree, an1) obj' ys
scopeExpr (Abs an1 v x) =
  let y = scopeExpr x
      (_, xFree, _) = extractAnn y
      bound = S.singleton v
  in  Abs (bound, xFree `M.withoutKeys` bound, an1) v y
scopeExpr (App an1 f x) =
  let g = scopeExpr f
      (_, gFree, _) = extractAnn g
      y = scopeExpr x
      (_, yFree, _) = extractAnn y
  in  App (S.empty, M.unionWith (+) gFree yFree, an1) g y
scopeExpr (Var an1 e@(Qualified m v)) =
  case m of
    Nothing -> Var (S.empty, M.singleton v 1, an1) e
    Just _  -> Var (S.empty, M.empty, an1) e
scopeExpr (Case an1 cs xs) =
  let (dsFree, ds) = scopeExprs cs
      (ysFree, ys) = scopeCaseAlternatives xs
  in  Case (S.empty, M.unionWith (+) dsFree ysFree, an1) ds ys
scopeExpr (Let an1 bs m) =
  let (csBound, csFree, cs) = scopeBinds bs
      n = scopeExpr m
      (_, nFree, _) = extractAnn n
  in  Let (csBound, M.unionWith (+) (nFree `M.withoutKeys` csBound) csFree, an1) cs n

scopeLiteral ::
  Literal (Expr a) -> Scoped (Literal (Expr (Scoped a)))
scopeLiteral l =
  case l of
    NumericLiteral x -> (S.empty, M.empty, NumericLiteral x)
    StringLiteral x  -> (S.empty, M.empty, StringLiteral x)
    CharLiteral x    -> (S.empty, M.empty, CharLiteral x)
    BooleanLiteral x -> (S.empty, M.empty, BooleanLiteral x)
    ArrayLiteral  xs ->
      let (free, ys) = scopeExprs xs
      in  (S.empty, free, ArrayLiteral ys)
    ObjectLiteral xs ->
      let (free, ys) = scopeLabeledExprs xs
      in  (S.empty, free, ObjectLiteral ys)

scopeExprCons ::
  Expr a -> Map Ident Int -> (Map Ident Int, Expr (Scoped a))
scopeExprCons x a = (M.unionWith (+) xFree a, y)
  where
  y             = scopeExpr x
  (_, xFree, _) = extractAnn y

scopeExprs :: [Expr a] -> (Map Ident Int, [Expr (Scoped a)])
scopeExprs = foldr f (M.empty, [])
  where
  f x (aFree, a) =  let (aFree', y) = scopeExprCons x aFree
                    in  (aFree', y:a) 

scopeLabeledExprs ::
  [(b, Expr a)] -> (Map Ident Int, [(b, Expr (Scoped a))])
scopeLabeledExprs = foldr f (M.empty, [])
  where
  f (s, x) (aFree, a) = let (aFree', y) = scopeExprCons x aFree
                        in  (aFree', (s, y):a)

scopeCaseAlternative :: CaseAlternative a -> Scoped (CaseAlternative (Scoped a))
scopeCaseAlternative (CaseAlternative bs xs) =
  let (ysFree, ys) =
        case xs of
          Left gs -> let (aFree, as) = scopeExprs (map fst gs)
                         (bFree, bs) = scopeExprs (map snd gs)
                     in  (M.unionWith (+) aFree bFree, Left (zip as bs))
          Right x -> let y = scopeExpr x
                         (_, yFree, _) = extractAnn y
                     in  (yFree, Right y)
      (csBound, cs) = scopeBinders bs
  in  (S.empty, ysFree `M.withoutKeys` csBound, CaseAlternative cs ys)

scopeCaseAlternatives :: [CaseAlternative a] -> (Map Ident Int, [CaseAlternative (Scoped a)])
scopeCaseAlternatives = foldr f (M.empty, [])
  where
  f x (aFree, a) = let (_, yFree, y) = scopeCaseAlternative x
                   in  (M.unionWith (+) aFree yFree, y:a)

scopeBinder :: Binder a -> Binder (Scoped a)
scopeBinder (NullBinder an1) = NullBinder (S.empty, M.empty, an1)
scopeBinder (LiteralBinder an1 x) =
  let (lBound, _, y) = scopeLiteralBinder x
  in  LiteralBinder (lBound, M.empty, an1) y
scopeBinder (VarBinder an1 v) = VarBinder (S.singleton v, M.empty, an1) v
scopeBinder (ConstructorBinder an1 t c xs) =
  let (ysBound, ys) = scopeBinders xs
  in  ConstructorBinder (ysBound, M.empty, an1) t c ys
scopeBinder (NamedBinder an1 v x) =
  let y = scopeBinder x
      (ysBound, _, _) = extractBinderAnn y
  in  NamedBinder (S.singleton v `S.union` ysBound, M.empty, an1) v y

scopeBinderCons ::
  Binder a -> Set Ident -> (Set Ident, Binder (Scoped a))
scopeBinderCons x a = (S.union xBound a, y)
  where
  y              = scopeBinder x
  (xBound, _, _) = extractBinderAnn y

scopeBinders :: [Binder a] -> (Set Ident, [Binder (Scoped a)])
scopeBinders = foldr f (S.empty, [])
  where
  f x (aBound, a) = let (aBound', y) = scopeBinderCons x aBound
                    in  (aBound', y:a)

scopeLabeledBinders ::
  [(b, Binder a)] -> (Set Ident, [(b, Binder (Scoped a))])
scopeLabeledBinders = foldr f (S.empty, [])
  where
  f (s, x) (aBound, a) = let (aBound', y) = scopeBinderCons x aBound
                         in  (aBound', (s, y):a)

scopeLiteralBinder ::
  Literal (Binder a) -> Scoped (Literal (Binder (Scoped a)))
scopeLiteralBinder l =
  case l of
    NumericLiteral x -> (S.empty, M.empty, NumericLiteral x)
    StringLiteral x  -> (S.empty, M.empty, StringLiteral x)
    CharLiteral x    -> (S.empty, M.empty, CharLiteral x)
    BooleanLiteral x -> (S.empty, M.empty, BooleanLiteral x)
    ArrayLiteral  xs ->
      let (bound, ys) = scopeBinders xs
      in  (bound, M.empty, ArrayLiteral ys)
    ObjectLiteral xs ->
      let (bound, ys) = scopeLabeledBinders xs
      in  (bound, M.empty, ObjectLiteral ys)

scopeBinds :: [Bind a] -> Scoped [Bind (Scoped a)]
scopeBinds = foldr f (S.empty, M.empty, [])
  where
  f (NonRec an1 v x) (aBound, aFree, a) =
    let y = scopeExpr x
        (_, yFree, _) = extractAnn y
        sv = S.singleton v
        bound = S.union sv aBound
        free = aFree `M.withoutKeys` sv
    in  (bound, free, NonRec (bound, free, an1) v y : a)
  f (Rec bs) (aBound, aFree, a) =
    let (xsFree, xs) = scopeExprs (map snd bs)
        bsBound = S.fromList (map (snd . fst) bs)
        g (an1, v) e = let (_, eFree, _) = extractAnn e
                       in  (((S.singleton v, eFree, an1), v), e)
    in  ( S.union bsBound aBound
        , M.unionWith (+) (aFree `M.withoutKeys` bsBound)
                          (xsFree `M.withoutKeys` bsBound)
        , Rec (zipWith g (map fst bs) xs) : a
        )

-- TODO: hygiene!

-- | subsitute a b m = m[b/a]
substitute :: Ident -> Expr (Scoped a) -> Expr (Scoped a)
substitute a b m =
  where
  (_, mFree, _) = extractAnn m
