{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | This optimization tries to remove unnecessary comparisons, e.g.
--
--   case x <# y of
--     True -> .. case x <# y of ..
-- or
--   case 3 <=# x of
--     True -> .. case 1 <# x of ..
--
-- To do that we record the relations between variables as we go through
-- the case expressions and perform a simple interval analysis.
--
module GhcPlugins.Comparisons.Pass ( transformProgram ) where

import GhcPlugins

import PrimOp
import TysPrim

import Control.Applicative ( (<$>), (<|>) )
import Control.Exception ( assert )
import Data.List ( foldl', mapAccumL )
import Data.Maybe ( fromMaybe, isJust )

transformProgram :: Bool -> ModGuts -> CoreM ModGuts
transformProgram debug guts = return guts { mg_binds = transform (mg_binds guts) }
  where
    transform = snd . mapAccumL (optimizeBind debug) emptySubst

optimizeBind :: Bool -> Subst -> CoreBind -> (Subst, CoreBind)
optimizeBind debug subst (NonRec var expr) = (subst', NonRec var' expr')
  where
    expr' = tryToSimplify debug emptyNumEnv subst' expr
    (subst', var') = substBndr subst var
optimizeBind debug subst (Rec list) = (subst', Rec list')
  where
    (subst', list') = mapAccumL f subst list
    f s (b, e) = let (s', b') = substBndr s b
                 in (s', (b', tryToSimplify debug emptyNumEnv s' e))

tryToSimplify :: Bool -> NumEnv -> Subst -> CoreExpr -> CoreExpr
tryToSimplify debug numenv subst expr =
  fromMaybe expr' (trueOrFalseExpr <$> tryEval debug numenv subst expr')
  where
    expr' = optimizeExpr debug numenv subst expr

optimizeExpr :: Bool -> NumEnv -> Subst -> CoreExpr -> CoreExpr
optimizeExpr debug numenv subst (Case expr bndr ty alts)
  = Case (tryToSimplify debug numenv subst expr) bndr ty
  $ map (optimizeAlt debug numenv subst expr) alts
optimizeExpr debug numenv subst (App expr arg)
  = App (tryToSimplify debug numenv subst expr) (tryToSimplify debug numenv subst arg)
optimizeExpr debug numenv subst (Lam bndr expr)
  = Lam bndr' (tryToSimplify debug numenv subst' expr)
  where
    (subst', bndr') = substBndr subst bndr
optimizeExpr debug numenv subst (Let bndr expr)
  = Let bndr' (tryToSimplify debug numenv subst' expr)
  where
    (subst', bndr') = optimizeBind debug subst bndr
optimizeExpr debug numenv subst (Cast expr coer)
  = Cast (tryToSimplify debug numenv subst expr) (substCo subst coer)
optimizeExpr debug numenv subst (Tick tickid expr) =
  Tick (substTickish subst tickid) (tryToSimplify debug numenv subst expr)
optimizeExpr _ _     subst (Type ty) = Type (substTy subst ty)
optimizeExpr _ _     subst (Coercion co) = Coercion (substCo subst co)
optimizeExpr _ _     subst (Var var) = lookupSubst subst var
optimizeExpr _ _     _     (Lit lit) = Lit lit

-- Here is where we get information about variables, i.e., if we have
--   case x <# y of
--     True -> [1]
--     False -> [2]
-- we optimize [1] under the assumption thaat x <# y and [2] assuming the
-- opposite. We're currently handling only very simple expressions (like in the
-- above example).
optimizeAlt :: Bool -> NumEnv -> Subst -> CoreExpr -> CoreAlt
  -> (AltCon, [CoreBndr], CoreExpr)
optimizeAlt debug numenv subst (App (App (Var opid) expr1) expr2)
            alt@(DataAlt datacon, args, expr)
  | Just relop <- idToRelOp opid
  = case (expr1, expr2, datacon == trueDataCon) of
      (Var id1, Var id2, branch) ->
        let numenv' = addRelation numenv id1 (negIf branch relop) id2
        in (DataAlt datacon, args', tryToSimplify debug numenv' subst' expr)
      (Var var, Lit lit, branch) ->
        let numenv' = updateIntrVarLit numenv var (negIf branch relop) lit
        in (DataAlt datacon, args', tryToSimplify debug numenv' subst' expr)
      (Lit lit, Var var, branch) ->
        let numenv' = updateIntrLitVar numenv lit (negIf branch relop) var
        in (DataAlt datacon, args', tryToSimplify debug numenv' subst' expr)
      _ -> alt
  where
    negIf b op = if b then op else negRelOp op
    (subst', args') = substBndrs subst args
optimizeAlt debug numenv subst _ (altcon, args, expr) =
  (altcon, args', tryToSimplify debug numenv subst' expr)
  where
    (subst', args') = substBndrs subst args

lookupSubst :: Subst -> Var -> CoreExpr
lookupSubst = lookupIdSubst (text "Comparisons.lookupSubst")

trueOrFalseId :: Bool -> Id
trueOrFalseId True  = trueDataConId
trueOrFalseId False = falseDataConId

trueOrFalseExpr :: Bool -> CoreExpr
trueOrFalseExpr = Var . trueOrFalseId

tryEval :: Bool -> NumEnv -> Subst -> CoreExpr -> Maybe Bool
tryEval debug numenv subst expr = case expr of
  App (App (Var opid) e1) e2 -> do
    rel <- idToRelOp opid
    tryEval' numenv rel e1 e2
  _ -> Nothing
  where
    tryEval' env op (Var var1) (Var var2) = do
      var1' <- lookupVar var1
      var2' <- lookupVar var2
      ifDebugTrace debug (ppr var1' <+> ppr op <+> ppr var2')
                         (evalVarVar env var1' op var2')
    tryEval' env op (Var var) (Lit lit) = do
      var' <- lookupVar var
      ifDebugTrace debug (ppr var' <+> ppr op <+> ppr lit)
                         (evalVarLit env var' op lit)
    tryEval' env op (Lit lit) (Var var) = do
      var' <- lookupVar var
      ifDebugTrace debug (ppr lit <+> ppr op <+> ppr var')
                         (evalLitVar env lit op var')
    -- Note that case with two literals should be handled by simplifier and
    -- the builtin rules.
    tryEval' _ _ _ _ = Nothing

    lookupVar var = case lookupSubst subst var of
      Var v -> Just v
      _     -> Nothing

--
-- Evaluating comparisons.
--

-- | Try to evaluate comparison between a variable and a literal.
evalVarLit :: NumEnv -> Var -> RelOp -> Literal -> Maybe Bool
evalVarLit env var relop lit
  | Just i <- litToInteger lit
  = do intr <- lookupIntr env var
       cmpIntrWith relop intr (BetweenEq i i)
  | Just r <- litToRational lit
  = do intr <- lookupIntr env var
       cmpIntrWith relop intr (BetweenEq r r)
  | otherwise = Nothing

-- | The same as above but with arguments swapped ("mirrored" 'RelO').
evalLitVar :: NumEnv -> Literal -> RelOp -> Var -> Maybe Bool
evalLitVar env lit relop var = evalVarLit env var (mirrorRelOp relop) lit

-- | The last where we compare two variables.
evalVarVar :: NumEnv -> Var -> RelOp -> Var -> Maybe Bool
evalVarVar numenv var1 relop var2 = m1 <|> m2 <|> mintr
  where
    -- First try with finding a relation between var1 and var2..
    m1 = checkRelation relations var1 var2 >>= flip evalRelOp relop
    -- .. then between var2 and var1..
    m2 = checkRelation relations var2 var1 >>= flip evalRelOp (mirrorRelOp relop)
    -- .. and finally check compare the intervals.
    mintr = evalIntr numenv var1 relop var2

    relations = neRelations numenv

-- | Returns 'Just True' ('Just False') iff what we know implies that the given
-- 'RelOp' would evaluate to 'True' ('False'). Otherwise return 'Nothing'.
evalRelOp :: NumRelation  -- ^ This is what we know.
          -> RelOp        -- ^ And this what is asked.
          -> Maybe Bool
evalRelOp Greater relop = case relop of
  Gt  -> Just True
  Ge  -> Just True
  Neq -> Just True
  _   -> Just False
evalRelOp GreatEq relop = case relop of
  Ge -> Just True
  Lt -> Just False
  _  -> Nothing
evalRelOp Equal relop = case relop of
  Eq -> Just True
  Ge -> Just True
  Lt -> Just True
  _  -> Just False

-- | Check if the given relation is always true/false based on the intervals
-- associated with the variables.
evalIntr :: NumEnv -> Var -> RelOp -> Var -> Maybe Bool
evalIntr numenv var1 relop var2
  | isIntegerLike ty
  = do i1 <- lookupIntr numenv var1 :: Maybe (Interval Integer)
       i2 <- lookupIntr numenv var2
       cmpIntrWith relop i1 i2
  | isRationalLike ty
  = do i1 <- lookupIntr numenv var1 :: Maybe (Interval Rational)
       i2 <- lookupIntr numenv var2
       cmpIntrWith relop i1 i2
  | otherwise = Nothing
  where
    ty = varType var1

litToInteger :: Literal -> Maybe Integer
litToInteger (MachInt i)    = Just i
litToInteger (MachInt64 i)  = Just i
litToInteger (MachWord i)   = Just i
litToInteger (MachWord64 i) = Just i
litToInteger _              = Nothing

litToRational :: Literal -> Maybe Rational
litToRational (MachFloat r)  = Just r
litToRational (MachDouble r) = Just r
litToRational _              = Nothing

-- | Take two arguments and rearrange them, so that we can convert 'RelOp' to
-- 'NumRelation'. The order of arguments obviously matters.
toNumRelation :: a -> RelOp -> a -> Maybe (a, NumRelation, a)
toNumRelation a relop b = case relop of
  Gt  -> Just (a, Greater, b)
  Ge  -> Just (a, GreatEq, b)
  Eq  -> Just (a, Equal, b)
  Neq -> Nothing
  Le  -> Just (b, GreatEq, a)
  Lt  -> Just (b, Greater, a)

-- | Check if the given type is one of the integer-like primitive types that is
-- handled by our optimization.
isIntegerLike :: Type -> Bool
isIntegerLike ty = case tyConAppTyCon_maybe ty of
  Just con -> con == intPrimTyCon
           || con == int32PrimTyCon
           || con == int64PrimTyCon
           || con == wordPrimTyCon
           || con == word32PrimTyCon
           || con == word64PrimTyCon
  Nothing  -> False

-- | The same as 'isIntegerLike' but for rational types, i.e. 'Float' and
-- 'Double'.
isRationalLike :: Type -> Bool
isRationalLike ty = case tyConAppTyCon_maybe ty of
  Just con -> con == floatPrimTyCon
           || con == doublePrimTyCon
  Nothing  -> False

--
-- Numerical environment.
--

data NumEnv = NumEnv
  { neIntegers  :: VarEnv (Interval Integer)
  , neRationals :: VarEnv (Interval Rational)
  , neRelations :: NumRelations
  }

instance Outputable NumEnv where
  ppr (NumEnv ienv renv rels) = ppr ienv $$ ppr renv $$ ppr rels

emptyNumEnv :: NumEnv
emptyNumEnv = NumEnv emptyVarEnv emptyVarEnv emptyNumRels

addRelation :: NumEnv -> Var -> RelOp -> Var -> NumEnv
addRelation numenv var1 relop var2 =
  updateIntrVarVar numenv' var1 relop var2
    where
      numenv' = addRelationU numenv var1 relop var2

addRelationU :: (Uniquable a) => NumEnv -> a -> RelOp -> a -> NumEnv
-- With current representation there's nothing we can
-- do with not equal.
addRelationU numenv _    Neq   _    = numenv
addRelationU numenv var1 relop var2 = numenv { neRelations = rels }
    where
      -- Returns Nothing only in case of 'Neq'.
      Just (x, r, y) = toNumRelation var1 relop var2
      rels = insertRel (neRelations numenv) x r y

--
-- Relations.
--

-- | We store only three basic relations.
data NumRelation
  = Greater
  | GreatEq
  | Equal

instance Outputable NumRelation where
  ppr Greater = text "Greater"
  ppr GreatEq = text "GreatEq"
  ppr Equal = text "Equal"

-- | The 'NumRelations' basically holds a graph of variable relations.
data NumRelations = NumRels (UniqFM (UniqFM NumRelation))

instance Outputable NumRelations where
  ppr (NumRels graph) = ppr graph

emptyNumRels :: NumRelations
emptyNumRels = NumRels emptyUFM

insertRel :: (Uniquable u) => NumRelations -> u -> NumRelation -> u -> NumRelations
insertRel (NumRels graph1) source_ relation target_ =
  NumRels $! case relation of
    -- It is important to insert two edges in case of 'Equal'. Otherwise some of
    -- the paths (i.e. relations) will be much harder to find. Consider
    --   x > y and y == z
    -- if we store only one equal edge say '(y, Equal, z)', then we don't have
    -- an easy way of finding a path between 'x' and 'z' (without iterating over
    -- all other edges)!
    Equal -> insertRel_ graph2 target Equal source
    _     -> graph2
  where
    graph2 = insertRel_ graph1 source relation target

    source = getUnique source_
    target = getUnique target_

    insertRel_ umap src rel tar =
      let modIns (Just umap') = Just (addToUFM umap' tar rel)
          modIns Nothing      = Just (unitUFM tar rel)
      in alterUFM modIns umap src


checkRelation :: NumRelations -> Var -> Var -> Maybe NumRelation
checkRelation numrels var1 var2 =
  case (searchPath numrels var1 var2, searchPath numrels var2 var1) of
    -- Note that we can have that
    --   x >= y  and  y >= x
    -- and we should conclude that x == y.
    -- It is not possible for > and doesn't matter for ==.
    (Just GreatEq, Just GreatEq) -> Just Equal
    (something,    _           ) -> something

-- | Searhing a path in the graph is inspired by Dijkstra shortest path
-- algorithm. We basically go and greedily explore the 'Equal', 'Greater'
-- and 'GreatEq' edges in this order and record the label of edges along
-- the way. E.g. if we have only 'Equal' edges then the two variables are equal.
searchPath :: NumRelations -> Var -> Var -> Maybe NumRelation
searchPath (NumRels umap) source_ target_ = go initialWl (unitUFM source Equal)
  where
    source = getUnique source_
    target = getUnique target_

    initialWl = getWorklist umap source

    go :: Worklist -> UniqFM NumRelation -> Maybe NumRelation
    go worklist visited = getNext worklist >>= go_
      where
        go_ (parent, rel, child, wl)
          | child == target         = combineRel rel <$> lookupUFM visited parent
          | child `elemUFM` visited = go wl visited
          | otherwise               = go wl' visited'
              where
                wl' = getWorklist umap child `concatWorklist` wl
                visited' = case lookupUFM visited parent of
                  Just prel -> addToUFM visited child (combineRel prel rel)
                  -- The following should never happen. Whenever we add
                  -- something to the worklist, the parent is inserted into
                  -- the visited map.
                  Nothing -> assert False visited

    combineRel :: NumRelation -> NumRelation -> NumRelation
    combineRel Equal   Equal   = Equal
    combineRel Greater _       = Greater
    combineRel _       Greater = Greater
    combineRel _       _       = GreatEq

-- | Worklist for the algorithm searching for a path in the graph. Corresponds
-- to the list of edges with 'Equal', 'Greater' and 'GreatEq' labels
-- respectively.
data Worklist = Wl [(Unique, Unique)] [(Unique, Unique)] [(Unique, Unique)]

emptyWorkList :: Worklist
emptyWorkList = Wl [] [] []

-- | Get a next labeled edge and the remaining worklist or 'Nothing' if the
-- worklist is empty.
getNext :: Worklist -> Maybe (Unique, NumRelation, Unique, Worklist)
getNext (Wl (x:xs) ys zs) = Just (fst x, Equal,   snd x, Wl xs ys zs)
getNext (Wl [] (y:ys) zs) = Just (fst y, Greater, snd y, Wl [] ys zs)
getNext (Wl [] [] (z:zs)) = Just (fst z, GreatEq, snd z, Wl [] [] zs)
getNext _                 = Nothing

-- | Create a worklist from the outgoing edges of the given vertex (i.e.
-- variable).
getWorklist :: UniqFM (UniqFM NumRelation) -> Unique -> Worklist
getWorklist umap1 source
  | Just umap2 <- lookupUFM umap1 source
  = let f p (Wl xs ys zs) = case p of
          (u, Equal)   -> Wl ((source, u) : xs) ys zs
          (u, Greater) -> Wl xs ((source, u) : ys) zs
          (u, GreatEq) -> Wl xs ys ((source, u) : zs)
    in foldr f emptyWorkList (ufmToList umap2)
  | otherwise = emptyWorkList

concatWorklist :: Worklist -> Worklist -> Worklist
concatWorklist (Wl as bs cs) (Wl xs ys zs) = Wl (as ++ xs) (bs ++ ys) (cs ++ zs)

--
-- Relational operators.
--

data RelOp
  = Gt
  | Ge
  | Eq
  | Neq
  | Le
  | Lt

instance Outputable RelOp where
  ppr Gt  = text ">"
  ppr Ge  = text ">="
  ppr Eq  = text "=="
  ppr Neq = text "/="
  ppr Le  = text "<="
  ppr Lt  = text "<"

relOfIntrs :: (Ord a) => Interval a -> Interval a -> Maybe RelOp
relOfIntrs intr1 intr2
  | isJust (gtIntr  intr1 intr2) = Just Gt
  | isJust (geIntr  intr1 intr2) = Just Ge
  | isJust (eqIntr  intr1 intr2) = Just Eq
  | isJust (neqIntr intr1 intr2) = Just Neq
  | isJust (leIntr  intr1 intr2) = Just Le
  | isJust (ltIntr  intr1 intr2) = Just Lt
  | otherwise                    = Nothing

cmpIntrWith :: (Ord a) => RelOp -> Interval a -> Interval a -> Maybe Bool
cmpIntrWith Gt  = gtIntr
cmpIntrWith Ge  = geIntr
cmpIntrWith Eq  = eqIntr
cmpIntrWith Neq = neqIntr
cmpIntrWith Le  = leIntr
cmpIntrWith Lt  = ltIntr

-- | Check if for all possible values of the two intervals, the one from the
-- first one is always greater than/greater or equal/equal/less or equal/less
-- than the one from the second interval.
gtIntr, geIntr, eqIntr, neqIntr, leIntr, ltIntr
  :: (Ord a) => Interval a -> Interval a -> Maybe Bool
gtIntr i1 i2
  | Just l1 <- getLower i1 , Just u2 <- getUpper i2 , l1 > u2
  = Just True
  | Just l2 <- getLower i2 , Just u1 <- getUpper i1 , l2 >= u1
  = Just False
gtIntr _ _ = Nothing

geIntr i1 i2
  | Just l1 <- getLower i1 , Just u2 <- getUpper i2 , l1 >= u2
  = Just True
  | Just l2 <- getLower i2 , Just u1 <- getUpper i1 , l2 > u1
  = Just False
geIntr _ _ = Nothing

-- For these three we can simply reuse the above definitions.
leIntr i1 i2 = geIntr i2 i1
ltIntr i1 i2 = gtIntr i2 i1
neqIntr i1 i2 = not <$> eqIntr i1 i2

eqIntr i1 i2
  -- If we can prove one variable greater than another,
  -- then they clearly can't be equal. Note that if we
  -- have 'Just False' it might be possible that the
  -- variables are in fact equal!
  | Just True <- gtIntr i1 i2 = Just False
  | Just True <- gtIntr i2 i1 = Just False
  -- If we know the exact values of the variables, then
  -- we can easily tell if they are equal or not.
  | Just l1 <- getLower i1, Just u1 <- getUpper i1
  , Just l2 <- getLower i2, Just u2 <- getUpper i2
  = if l1 == u1 && l2 == u2
      then Just $! l1 == l2  -- With above implies that u1 == u2.
      else Nothing
  | otherwise = Nothing

-- | Return 'Just relop' if 'relop' is an operator that we can handle in this
-- optimization.
idToRelOp :: Id -> Maybe RelOp
idToRelOp i = isPrimOpId_maybe i >>= primOpToRelOp

-- | Convert from a 'PrimOp' to 'RelOp' if the given 'PrimOp' can be handled by
-- the optimization. Otherwise return 'Nothing'.
primOpToRelOp :: PrimOp -> Maybe RelOp
primOpToRelOp IntGtOp = Just Gt
primOpToRelOp IntGeOp = Just Ge
primOpToRelOp IntLtOp = Just Lt
primOpToRelOp IntLeOp = Just Le
primOpToRelOp IntEqOp = Just Eq

primOpToRelOp WordGtOp = Just Gt
primOpToRelOp WordGeOp = Just Ge
primOpToRelOp WordLtOp = Just Lt
primOpToRelOp WordLeOp = Just Le
primOpToRelOp WordEqOp = Just Eq

primOpToRelOp FloatGtOp = Just Gt
primOpToRelOp FloatGeOp = Just Ge
primOpToRelOp FloatLtOp = Just Lt
primOpToRelOp FloatLeOp = Just Le
primOpToRelOp FloatEqOp = Just Eq

primOpToRelOp DoubleGtOp = Just Gt
primOpToRelOp DoubleGeOp = Just Ge
primOpToRelOp DoubleLtOp = Just Lt
primOpToRelOp DoubleLeOp = Just Le
primOpToRelOp DoubleEqOp = Just Eq

primOpToRelOp _ = Nothing

-- | Negate the given 'RelOp', e.g.
--   negRelOp <  should give  >=
-- in other words
--   not (x < y)  should give  x >= y
negRelOp :: RelOp -> RelOp
negRelOp Gt  = Le
negRelOp Ge  = Le
negRelOp Eq  = Neq
negRelOp Neq = Eq
negRelOp Le  = Gt
negRelOp Lt  = Ge

-- | Expresses that
--   x < y  iff  y > x
-- etc.
mirrorRelOp :: RelOp -> RelOp
mirrorRelOp Gt  = Lt
mirrorRelOp Ge  = Le
mirrorRelOp Eq  = Eq
mirrorRelOp Neq = Neq
mirrorRelOp Le  = Ge
mirrorRelOp Lt  = Gt

--
-- Interval type.
--

-- | Note that the intervals are always _closed_! Also for integers this means
-- that if we have 'x < 1' we can express that as 'BelowEq 0'.
data Interval a
  = BetweenEq !a !a
  | BelowEq !a
  | AboveEq !a
  | Top

-- FIXME: any reason why Integer and Rational are not Outputable?
instance (Show a) => Outputable (Interval a) where
  ppr (BetweenEq a b) = char '[' <> text (show a) <> comma <+> text (show b) <> char ']'
  ppr (AboveEq a) = char '[' <> text (show a) <> comma <+> text "inf" <> char ']'
  ppr (BelowEq a) = char '[' <> text "inf" <> comma <+> text (show a) <> char ']'
  ppr Top      = char '[' <> text "inf" <> comma <+> text "inf" <> char ']'

-- Generic function to update intervals that works both with Integer and
-- Rational ones.
updateIntrVarLit :: NumEnv -> Var -> RelOp -> Literal -> NumEnv
updateIntrVarLit numenv var relop lit
  | Just i <- litToInteger lit  = updateIntr numenv var relop i
  | Just r <- litToRational lit = updateIntr numenv var relop r
  | otherwise                   = numenv

updateIntrLitVar :: NumEnv -> Literal -> RelOp -> Var -> NumEnv
updateIntrLitVar numenv lit relop var =
  updateIntrVarLit numenv var (mirrorRelOp relop) lit

-- Update/refine intervals based on a new relation between some variables. That
-- is, if we know that 'x' is [0, 10] and 'y' is [8, inf] and then we learn that
-- that 'x' is larger than 'y' we can conclude that 'x' must be [9, 10] and 'y'
-- must be [8, 9].
updateIntrVarVar :: NumEnv -> Var -> RelOp -> Var -> NumEnv
updateIntrVarVar numenv _    Neq   _    = numenv
updateIntrVarVar numenv var1 relop var2
  | isIntegerLike ty
  -- = numenv
  = let mintr1 = lookupIntr numenv x :: Maybe (Interval Integer)
        mintr2 = lookupIntr numenv y
    in refineBoth mintr1 rel mintr2
  | isRationalLike ty
  = let mintr1 = lookupIntr numenv x :: Maybe (Interval Rational)
        mintr2 = lookupIntr numenv y
    in refineBoth mintr1 rel mintr2
  | otherwise
  = numenv
  where
    ty = varType var1
    -- Returns 'Nothing' only for 'Neq'.
    Just (x, rel, y) = toNumRelation var1 relop var2

    -- Try to refine the intervals based on the new relation and insert them
    -- into the 'NumEnv'.
    refineBoth :: (Eq a, Intervalable a)
               => Maybe (Interval a) -> NumRelation -> Maybe (Interval a)
               -> NumEnv
    refineBoth (Just intr1) Greater (Just intr2) =
      case (getUpper intr1, getLower intr2) of
        (Just ux, Just ly) -> updateIntr (updateIntr numenv x Gt ly) y Lt ux
        (Just ux, Nothing) -> updateIntr numenv y Lt ux
        (Nothing, Just ly) -> updateIntr numenv x Gt ly
        _                  -> numenv
    refineBoth (Just intr1) GreatEq (Just intr2) =
      case (getUpper intr1, getLower intr2) of
        (Just ux, Just ly) -> updateIntr (updateIntr numenv x Ge ly) y Le ux
        (Just ux, Nothing) -> updateIntr numenv y Le ux
        (Nothing, Just ly) -> updateIntr numenv x Ge ly
        _                  -> numenv
    refineBoth (Just intr1) Greater Nothing
      | Just ux <- getUpper intr1
      = updateIntr numenv y Lt ux
    refineBoth (Just intr1) GreatEq Nothing
      | Just ux <- getUpper intr1
      = updateIntr numenv y Le ux
    refineBoth Nothing Greater (Just intr2)
      | Just ly <- getLower intr2
      = updateIntr numenv x Gt ly
    refineBoth Nothing GreatEq (Just intr2)
      | Just ly <- getLower intr2
      = updateIntr numenv x Ge ly
    refineBoth (Just intr1) Equal Nothing
      = insertIntr numenv y intr1
    refineBoth Nothing Equal (Just intr2)
      = insertIntr numenv x intr2
    refineBoth _ _ _ = numenv


-- | A class to cover numerical information about both Integers and
-- Rationals in some sane way.
class Intervalable a where
  lookupIntr :: NumEnv -> Var -> Maybe (Interval a)
  insertIntr :: NumEnv -> Var -> Interval a -> NumEnv
  updateIntr :: NumEnv -> Var -> RelOp -> a -> NumEnv
  toIntr     :: Literal -> Maybe (Interval a)
  mkIntr     :: RelOp -> a -> Interval a
  refineIntr :: RelOp -> a -> Interval a -> Interval a

instance Intervalable Integer where
  lookupIntr env var = lookupVarEnv (neIntegers env) var

  insertIntr env var intr =
    env { neIntegers = extendVarEnv (neIntegers env) var intr }

  updateIntr numenv var relop lit = numenv' { neIntegers = newienv }
    where
      newienv = extendVarEnv intrs var newintr

      numenv' = foldl' g numenv (ufmToList intrs)

      g acc (u, intr)
        | Just op <- relOfIntrs newintr intr
        = addRelationU acc uvar op u
        | otherwise
        = acc

      newintr = case lookupVarEnv intrs var of
        Just intr -> refineIntr relop lit intr
        Nothing   -> mkIntr relop lit

      intrs = neIntegers numenv
      uvar = getUnique var

  toIntr (MachInt i)    = Just $ BetweenEq i i
  toIntr (MachInt64 i)  = Just $ BetweenEq i i
  toIntr (MachWord i)   = Just $ BetweenEq i i
  toIntr (MachWord64 i) = Just $ BetweenEq i i
  toIntr _              = Nothing

  mkIntr Gt a  = AboveEq (a + 1)
  mkIntr Ge a  = AboveEq a
  mkIntr Eq a  = BetweenEq a a
  mkIntr Neq _ = Top
  mkIntr Le a  = BelowEq a
  mkIntr Lt a  = BelowEq (a - 1)

  refineIntr Gt a intr = case getLower intr of
    Just l | l <= a    -> setLower (a + 1) intr
           | otherwise -> intr
    Nothing            -> setLower (a + 1) intr
  refineIntr Ge a intr = case getLower intr of
    Just l | l < a     -> setLower a intr
           | otherwise -> intr
    Nothing            -> setLower a intr
  refineIntr Eq a _ = BetweenEq a a
  refineIntr Neq a intr = case (getLower intr, getUpper intr) of
    (Just l, _) | l == a -> setLower (a + 1) intr
    (_, Just u) | u == a -> setUpper (a - 1) intr
    _                    -> intr
  refineIntr Le a intr = case getUpper intr of
    Just u | a < u     -> setUpper a intr
           | otherwise -> intr
    Nothing            -> setUpper a intr
  refineIntr Lt a intr = case getUpper intr of
    Just u | a <= u    -> setUpper (a - 1) intr
           | otherwise -> intr
    Nothing            -> setUpper (a - 1) intr


instance Intervalable Rational where
  lookupIntr env var = lookupVarEnv (neRationals env) var

  insertIntr env var intr =
    env { neRationals = extendVarEnv (neRationals env) var intr }

  updateIntr numenv var relop lit = numenv' { neRationals = newrenv }
    where
      newrenv = extendVarEnv intrs var newintr

      numenv' = foldl' g numenv (ufmToList intrs)

      g acc (u, intr)
        | Just op <- relOfIntrs newintr intr
        = addRelationU acc uvar op u
        | otherwise
        = acc

      newintr = case lookupVarEnv intrs var of
        Just intr -> refineIntr relop lit intr
        Nothing   -> mkIntr relop lit

      intrs = neRationals numenv
      uvar = getUnique var

  toIntr (MachFloat r)  = Just $ BetweenEq r r
  toIntr (MachDouble r) = Just $ BetweenEq r r
  toIntr _              = Nothing

  mkIntr Gt a  = AboveEq a
  mkIntr Ge a  = AboveEq a
  mkIntr Eq a  = BetweenEq a a
  mkIntr Neq _ = Top
  mkIntr Le a  = BelowEq a
  mkIntr Lt a  = BelowEq a

  refineIntr Gt a intr = case getLower intr of
    Just l | l < a     -> setLower a intr
           | otherwise -> intr
    Nothing            -> setLower a intr
  refineIntr Ge a intr = case getLower intr of
    Just l | l < a     -> setLower a intr
           | otherwise -> intr
    Nothing            -> setLower a intr
  refineIntr Eq a _ = BetweenEq a a
  refineIntr Neq _ intr = intr
  refineIntr Le a intr = case getUpper intr of
    Just u | a < u     -> setUpper a intr
           | otherwise -> intr
    Nothing            -> setUpper a intr
  refineIntr Lt a intr = case getUpper intr of
    Just u | a <= u    -> setUpper a intr
           | otherwise -> intr
    Nothing            -> setUpper a intr


getLower :: Interval a -> Maybe a
getLower (BetweenEq l _) = Just l
getLower (AboveEq l)     = Just l
getLower _               = Nothing

getUpper :: Interval a -> Maybe a
getUpper (BetweenEq _ u) = Just u
getUpper (BelowEq u)     = Just u
getUpper _               = Nothing

setLower :: a -> Interval a -> Interval a
setLower a (AboveEq _)     = AboveEq a
setLower a (BelowEq u)     = BetweenEq a u
setLower a (BetweenEq _ u) = BetweenEq a u
setLower a Top             = AboveEq a

setUpper :: a -> Interval a -> Interval a
setUpper a (AboveEq l)     = BetweenEq l a
setUpper a (BelowEq _)     = BelowEq a
setUpper a (BetweenEq l _) = BetweenEq l a
setUpper a Top             = BelowEq a

--
-- Some helper functions
--

ifDebugTrace :: (Outputable a) => Bool -> SDoc -> Maybe a -> Maybe a
ifDebugTrace True cmp (Just r)
  = pprTrace "Comparisons: optimized known comparison:"
             (cmp <+> text "is" <+> ppr r)
             (Just r)
ifDebugTrace _ _ r = r
