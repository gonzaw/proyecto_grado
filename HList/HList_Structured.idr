{-
  Lista heterogenea que se define por una funcion de tipo P : (x : Type) -> Type.
  'x' puede ser Type1, o cualquier otro tipo (como Nat). Esta funcion describe la estructura que deben tener los valores, dado un valor 
  implicito en cada casilla.
  Por ejemplo, HList (\x : Type => x) o HList id indica que los valores no tienen restriccion, asi que se pueden ingresar valores de 
  cualquier tipo con kind Type.
  Otro ejemplo, HList (\x : Type => (x,x)) indica que solo se admiten valores del estilo (a,b), con a y b pertenecientes a un tipo x 
  cualquiera
  Un ultimo ejemplo seria HList (\n : Nat => Vect n Nat), que permite vectores de naturales de cualquier tamanio
  
  Esto tiene la restriccion de, por ejemplo, no poder utilizar vectores de largo arbitrario y tipo arbitrario. Para ello se necesitaria crear
  un nuevo tipo de lista heterogenea donde la funcion de tipo P este parametrizada por 2 tipos y no uno solo
-}

import Data.Vect

%default total

using (x : Type, P : x -> Type)        
    data HList : (P : x -> Type) ->  Type where
        Nil : HList P
        (::) : {head : x} -> P head -> HList P -> HList P   

-- Tipo de listas heterogeneas mas comun
HListCommon : Type
HListCommon = HList id

hListExample : HListCommon
hListExample = 1 :: "1" :: (1,2) :: Nil

-- Ejemplos de listas con estructuras mas restringidas
hListTuple : HList (\x => (x, x))
hListTuple = (1,1) :: ("1","2") :: Nil

hListList : HList (\x => List x)
hListList = [1,2,3] :: ["2","Hi","42"] :: Nil

hListVect : HList (\n : Nat => Vect n Nat)	
hListVect =  [1,2] :: [1,3,4,5] :: Nil
