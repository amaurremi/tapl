module Types where

data Type = TyBool
          | TyNat
          | TyArr Type Type
          | TyId Id
          | Scheme TypeScheme   -- used for let polymorphism
          deriving Eq

instance Show Type where
    show TyBool = "bool"
    show TyNat  = "nat"
    show (TyArr t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show (TyId n) = "X" ++ show n
    show (Scheme (ids, t)) = "∀ " ++ unwords (map show ids) ++ " . " ++ show t

type TypeScheme = ([Id], Type)

data Term = Var VarName
          | Lambda VarName Type Term
          | App Term Term
          | Boolean Bool
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | IfThenElse Term Term Term
          | Let VarName Term Term

instance Show Term where
    show Zero                  = "0"
    show (Lambda x tpe term)   = "λ" ++ x ++ " : " ++ show tpe ++ " . " ++ show term
    show (App t1 t2)           = "(" ++ show t1 ++ ") (" ++ show t2 ++ ")"
    show (Boolean b)           = show b
    show (Succ t)              = "1 + " ++ show t
    show (Pred t)              = show t ++ " - 1"
    show (IsZero t)            = "zero? " ++ show t
    show (IfThenElse t1 t2 t3) = "if (" ++ show t1 ++ ") then " ++ show t2 ++ " else " ++ show t3
    show (Var x)               = x

type Constraint = [(Type, Type)]

showConstraints :: Constraint -> String
showConstraints = unlines . map (\(t1, t2) -> show t1 ++ " = " ++ show t2)

type VarName = String

type Id = Int

type Fresh = [Id]

type Г = [(VarName, Type)]