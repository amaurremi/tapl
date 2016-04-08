module Test where

import Types
import Unification

type TypeCheckFunction = Г -> Fresh -> Term -> Maybe (Type, Constraint, Fresh)

test :: Term -> TypeCheckFunction -> IO ()
test exp typeCheck = case typeCheck [] [8,9..] exp of
            Just (ret, constraints, _) -> do
                let unified = unify constraints
                putStrLn $ "expression: " ++ show exp
                putStrLn $ "return type: " ++ show ret
                putStrLn $ "constraints:\n" ++ showConstraints constraints
                putStrLn $ "unified:\n" ++ showConstraints unified
                putStrLn $ "typed expression: " ++ (show $ substConstraintTerm exp unified)
            Nothing                    ->
                putStrLn "type error"

-- Test expressions

testExp1 = App (Lambda "x1" (TyId 1) $ Var "x1") Zero
testExp2 = Lambda "x1" (TyArr (TyId 1) (TyId 2)) $ App (Var "x1") Zero
testExp3 = Lambda "x1" (TyId 1) $ Lambda "x2" (TyId 2) $ Lambda "x3" (TyId 3) $ App (App (Var "x1") (Var "x3")) (App (Var "x2") (Var "x3"))
testExp4 = Lambda "x1" (TyArr (TyId 1) (TyId 1)) $ Lambda "x2" (TyId 1) $ Let "x3" (Var "x1") $ App (Var "x3") (Var "x2")
-- testExp5 should fail when used without let polymorphism
testExp5 = let xType     = TyId 1
               f         = "x1"
               fApp      = App (Var f)
               a         = "x2"
               aVar      = Var a
               double    = "x3"
               doubleApp = App (Var double)
               a1        = "x4"
               a1Var     = Var a1
               x1        = "x5"
               x1Var     = Var x1
               x2        = "x6"
               x2Var     = Var x2
               b         = "x7"
               bVar      = Var b
           in Let double (Lambda f (TyArr xType xType) $ Lambda a xType $ fApp $ fApp aVar) $
              Let a1 (App (doubleApp $ Lambda x1 TyNat $ Succ $ Succ x1Var) $ Succ Zero) $
              Let b (App (doubleApp $ Lambda x2 TyBool $ x2Var) $ Boolean False) $
              IfThenElse a1Var bVar bVar
