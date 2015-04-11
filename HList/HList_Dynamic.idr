{-
  Lista heterogenea definida utilizando las listas y vectores que ya trae Idris.
  Se definen como un tipo List HValue, donde HValue contiene cualquier posible valor heterogeneo (como Dynamic en Haskell
-}

import Data.Vect

%default total

-- Tipo que permite crear un dato totalmente generico, teniendo el tipo A : Type implicito
data HValue : Type where
	HVal: {A : Type} -> (x : A) -> HValue

-- Definicion de listas y vectores heterogeneos
HList : Type
HList = List HValue

HVect: Nat -> Type
HVect n = Vect n HValue
   
-- Ejemplos   
hListExample : HList
hListExample = the HList [HVal (1,2), HVal "Hello", HVal 42]    

-- Funciones de listas heterogeneas          
hListLength : HList -> Nat
hListLength = List.length

hVectLength : HVect n -> Nat
hVectLength = Vect.length
    
  


  
        
