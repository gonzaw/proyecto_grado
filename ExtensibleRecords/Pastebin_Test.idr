import Data.Vect

%default total

-- Coso de HMember
data ElemBool : Eq t => t -> Vect n t -> Bool -> Type where
  ElemBoolNil : Eq t => ElemBool {t=t} a [] False
  ElemBoolCons : Eq t => ElemBool {t=t} x1 xs b -> ElemBool x1 (x2 :: xs) ((x1 == x2) || b)
    
data IsSet : Eq t => Vect n t -> Type where
  IsSetNil : Eq t => IsSet {t=t} []
  IsSetCons : Eq t => ElemBool {t=t} x xs False -> IsSet xs -> IsSet (x :: xs)
    
fun_1 : Eq t => (x : t) -> (xs : Vect n t) -> (b : Bool ** ElemBool x xs b)
fun_1 x [] = (False ** ElemBoolNil)
fun_1 x1 (x2 :: xs) = 
  let (b ** prfRec) = fun_1 x1 xs
  in (((x1 == x2) || b) ** (ElemBoolCons prfRec))  
    
fun_2 : Eq t => (xs : Vect n t) -> IsSet xs 
fun_2 [] = IsSetNil
fun_2 (x :: xs) = 
    let prfRec = fun_2 xs
        (False ** isNotMember) = fun_1 x xs
    in IsSetCons isNotMember prfRec
    
example : IsSet [1,1]
example = fun_2 [1,1]
