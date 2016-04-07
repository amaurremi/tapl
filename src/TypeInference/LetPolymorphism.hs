---------------------------------------------------------------------
-- Constraint-Based Type Inference Algorithm With Let Polymorphism --
---------------------------------------------------------------------

module LetPolymorphism (typeCheck) where

import Types
import Test
import Unification
import Data.List (splitAt)

-- Type Checking and Constraint Generation

-- todo wrap fresh variables in State monad
-- all cases for this function, except CT-VAR and CT-LET, are analogous to the typeCheck function in `SimpleTypeInference`
typeCheck :: Г -> Fresh -> Term -> Maybe (Type, Constraint, Fresh)
-- (CT-VAR)
typeCheck env fs (Var x)               = do
    tpe <- x `lookup` env
    let (sTpe, sFs) = removeScheme tpe fs
    return (sTpe, [], sFs)
        where removeScheme :: Type -> Fresh -> (Type, Fresh)
              removeScheme (Scheme (ids, t)) fs =
                let (freshIds, fs') = splitAt (length ids) fs
                    makeType        = map TyId
                    noSchemeType    = substConstraintType t $ zip (makeType ids) $ makeType freshIds
                in (noSchemeType, fs')
              removeScheme t fs                 = (t, fs)
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
-- (CT-LET)
typeCheck env fs (Let x t body) = do
    -- calculate a type and set of associated constraints for the right-hand side `t`
    (tpe, c, fs1) <- typeCheck env fs t
    -- find a most general solution to the constraints
    let sigma         = unify c
        -- apply sigma to the rhs type to obtain principal type
        principalType = substConstraintType tpe sigma
        -- apply sigma to the environment
        principalEnv  = map (\(x, xType) -> (x, substConstraintType xType sigma)) env
        -- generalize variables in `principalType` to obtain its principal type scheme
        typeScheme    = (generalize principalType principalEnv, principalType)
        extendedEnv   = (x, Scheme typeScheme) : principalEnv
    (tpe2, c2, fs2) <- typeCheck extendedEnv fs1 body
    return (tpe2, [], fs2)

generalize :: Type -> Г -> [Id]
generalize t@(TyId id) env   = if mentioned id env then [] else [id]
generalize (TyArr t1 t2) env = generalize t1 env ++ generalize t2 env
generalize _ _               = []

-- does a type variable appear in an environment?
mentioned :: Id -> Г -> Bool
mentioned id = any (elem id . fv) . map snd

succPred :: Г -> [Int] -> Term -> Maybe (Type, Constraint, Fresh)
succPred env fs t1 = do
  (tpe, cs, fs') <- typeCheck env fs t1
  return (TyNat, (tpe, TyNat) : cs, fs')

main = test testExp1 typeCheck