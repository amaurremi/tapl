module Unification where

import Types

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