-----------------------------------------------------------------------
-- Constraint-Based Type Inference Algorithm Described in Chapter 22 --
-----------------------------------------------------------------------

module SimpleTypeInference where

import Types
import Test

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

main = test testExp1 typeCheck