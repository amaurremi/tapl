---------------------------------------------------------------------
-- Constraint-Based Type Inference Algorithm With Let Polymorphism --
---------------------------------------------------------------------

module LetPolymorphism where

import Types

type TypeScheme = ([Id], Type)

-- Type Checking and Constraint Generation

-- todo wrap fresh variables in State monad
typeCheck :: Г -> Fresh -> Term -> Maybe (Type, Constraint, Fresh)
-- (CT-VAR)
typeCheck env fs (Var x)               = do
    tpe <- x `lookup` env
    return (tpe, [], fs)
-- (CT-ABS)
typeCheck env fs (Lambda x tpe1 body)  = do
    (tpe2, c, fs) <- typeCheck ((x, tpe1) : env) fs body
    return ((TyArr tpe1 tpe2), c, fs)
-- (CT-APP)
typeCheck env fs (App t1 t2)           = do
    (tpe1, c1, fs1) <- typeCheck env fs t1
    (tpe2, c2, fs2) <- typeCheck env fs1 t2
    let x : fs3 = fs2
        ret     = TyId x
    return (ret, (tpe1, TyArr tpe2 ret) : c2 ++ c1, fs3)
-- (CT-ZERO)
typeCheck env fs Zero                  =
    Just $ (TyNat, [], fs)
-- (CT-SUCC) & (CT-PRED)
typeCheck env fs (Succ t1)             =
    succPred env fs t1
-- (CT-ISZERO)
typeCheck env fs (IsZero t1)           = do
    (tpe, cs, fs') <- typeCheck env fs t1
    return (TyBool, (tpe, TyNat) : cs, fs')
-- (CT-TRUE) & (CT-FALSE)
typeCheck env fs (Boolean _)           =
    Just (TyBool, [], fs)
-- (CT-IF)
typeCheck env fs (IfThenElse t1 t2 t3) = do
    (tpe1, c1, fs1) <- typeCheck env fs t1
    (tpe2, c2, fs2) <- typeCheck env fs1 t2
    (tpe3, c3, fs3) <- typeCheck env fs2 t3
    return (tpe2, (tpe1, TyBool) : (tpe2, tpe3) : c1 ++ c2 ++ c3, fs3)
typeCheck env fs (Let x t body) = do
    (tpe1, c1, fs1) <- typeCheck env fs t
    (tpe2, c2, fs2) <- typeCheck ((x, tpe1) : env) fs1 body
    return (tpe2, [], fs2)

succPred :: Г -> [Int] -> Term -> Maybe (Type, Constraint, Fresh)
succPred env fs t1 = do
  (tpe, cs, fs') <- typeCheck env fs t1
  return (TyNat, (tpe, TyNat) : cs, fs')

-- Unification

subst :: Id -> Type -> Type -> Type
subst id sub t@(TyId id') = if id == id' then sub else t
subst id sub (TyArr s t)  = TyArr (subst id sub s) (subst id sub t)
subst _ _ t               = t

substExp :: Id -> Type -> Term -> Term
substExp id sub (Lambda x tpe term)   = Lambda x (subst id sub tpe) $ substExp id sub term
substExp id sub (App t1 t2)           = App (substExp id sub t1) $ substExp id sub t2
substExp id sub (Pred t)              = Pred $ substExp id sub t
substExp id sub (Succ t)              = Succ $ substExp id sub t
substExp id sub (IsZero t)            = IsZero $ substExp id sub t
substExp id sub (IfThenElse t1 t2 t3) = IfThenElse (substExp id sub t1) (substExp id sub t2) (substExp id sub t3)
substExp _ _ t                        = t

unify :: Constraint -> Constraint
unify [] = []
unify ((s, t) : cs) =
    if s == t
    then unify cs
    else let resultS = unifyFv s t cs
             resultT = unifyFv t s cs
         in case resultS of
            Just result -> result
            Nothing     -> case resultT of
                           Just result' -> result'
                           Nothing -> case (s, t) of
                                      (TyArr s1 s2, TyArr t1 t2) -> (s1, t1) : (s2, t2) : unify cs
                                      _ -> error "unification failed"

    where fv :: Type -> [Id]
          fv s@(TyId x)  = [x]
          fv (TyArr s t) = fv s ++ fv t
          fv _           = []

          unifyFv :: Type -> Type -> Constraint -> Maybe Constraint
          unifyFv s t cs = case s of
                  TyId x -> if not $ x `elem` fv t
                            then Just $ (s, t) : (unify $ map (\(t1, t2) -> (subst x t t1, subst x t t2)) cs)
                            else Nothing
                  _      -> Nothing

main = test testExp1 typeCheck