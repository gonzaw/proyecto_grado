{-
  En este archivo se van a intentar definir records extensibles.
  
  Basicamente, se definen los records como una lista heterogenea de labels. Un label tiene un titulo y un tipo. Un record, para un label,
  debe tener un valor de ese tipo. A su vez, se definen relaciones que indican cuando un label es identico a otro (cuando tienen el mismo
  titulo), y cuando un label esta repetido en un vector de labels. Se utiliza una metodologia similar a las pruebas de Data.Vect.Elem
-}
import Data.Vect

%default total

-- Un label contiene un titulo y un tipo
data Label : Type where
  MkLabel : String -> Type -> Label

getLblTitle : Label -> String
getLblTitle (MkLabel s _) = s

getLblType : Label -> Type
getLblType (MkLabel _ ty) = ty

-- Relacion de equivalencia entre labels
data SameLabel : Label -> Label -> Type where
  IsSame : SameLabel (MkLabel s t1) (MkLabel s t2)

notTheSameLabel : Not (s = w) -> Not (SameLabel (MkLabel s t1) (MkLabel w t2))
notTheSameLabel sneqw IsSame = sneqw Refl

-- Funcion de decision sobre igualdad de labels
isSameLabel : (l1 : Label) -> (l2 : Label) -> Dec (SameLabel l1 l2)
isSameLabel (MkLabel s1 t1) (MkLabel s2 t2)  with (decEq s1 s2)
  isSameLabel (MkLabel s t1) (MkLabel s t2) | Yes Refl = Yes IsSame
  isSameLabel (MkLabel s1 t1) (MkLabel s2 t2) | No s1neqs2 = No (notTheSameLabel s1neqs2)

-- Relacion de inclusion. "InLabel l ls" indica que el label "l" ya existe en el vector de labels "ls". Esta repetido si ya existe
-- otro label con un titulo igual
data InLabel : Label -> Vect n Label -> Type where
  InHere : SameLabel l1 l2 -> InLabel l1 (l2 :: ls)
  InThere : InLabel l ls -> InLabel l (y :: ls)

-- Ninguna label puede estar en un vector vacio
noEmptyInLabel : {l : Label} -> InLabel l [] -> Void
noEmptyInLabel (InHere isSame) impossible

-- Un label que no esta en la cabeza ni cola de la lista no esta en la lista
neitherInHereNorInThere : {x, y : Label} -> {xs : Vect n Label} -> Not (SameLabel x y) -> Not (InLabel x xs) -> Not (InLabel x (y :: xs))
neitherInHereNorInThere xneqy xnrepxs (InHere IsSame) = xneqy IsSame
neitherInHereNorInThere xneqy xnrepxs (InThere xinxs) = xnrepxs xinxs

-- Funcion de decision que indica si un label esta repetido en una lista de labels o no
isInLabel : (l : Label) -> (ls : Vect n Label) -> Dec (InLabel l ls)
isInLabel l [] = No noEmptyInLabel
isInLabel l (x :: xs) with (isSameLabel l x)
  isInLabel l (x :: xs) | Yes prf = Yes (InHere prf)
  isInLabel l (x :: xs) | No lneqx with (isInLabel l xs)
    isInLabel l (x :: xs) | No lneqx | Yes lrepxs = Yes (InThere lrepxs)
    isInLabel l (x :: xs) | No lneqx | No lnrepxs = No (neitherInHereNorInThere lneqx lnrepxs)

-- Records
-- Un record contiene una lista de labels no repetidos (no se repiten si tienen titulos distintos). A cada label se le asocia un valor
-- del tipo correspondiente.
-- El titulo del label puede pasarse implicitamente, siempre que se defina en el tipo y se pueda inferir
data Record : Vect k Label -> Type where
    NulRec : Record []
    Rec : {t : Type} -> {s : String} -> (val : t) -> Record ts -> (prf : Not (InLabel (MkLabel s t) ts)) -> Record ((MkLabel s t)::ts)

-- Funcion que ayuda a obtener pruebas automaticas
getNo : (res : Dec p) -> case res of { Yes _ => () ; No _ => Not p }
getNo (Yes prf) = ()
getNo (No contra) = contra

-- LabelType l ls ty indica que el label "l" de la lista "ls" tiene el tipo "ty"
data LabelType : Label -> Vect k Label -> Type -> Type where
  First : LabelType (MkLabel s ty) ((MkLabel s ty) :: xs) ty
  Later : LabelType l ls ty -> LabelType l (x :: ls) ty

-- Dado un label, obtiene el elemento de un record
getElement' : (l : Label) ->  LabelType l ls t -> Record ls -> t
getElement' (MkLabel s t) First (Rec val _ _) = val
getElement' l (Later prfLater) (Rec _ rec _) = getElement' l prfLater rec

getElement : (l : Label) -> Record ls -> 
               {default tactics { search } prf : LabelType l ls t} -> t
getElement l rec {prf} = getElement' l prf rec

-- Tira error de compilacion, no se puede unificar el tipo "t" de val con "getLblType l"
{-getElement : (l : Label) -> {auto prf : InLabel l ls} -> Record ls -> (getLblType l)
getElement l {prf=prf} NulRec = void $ noEmptyInLabel prf
getElement l {prf=(InHere prfSame)} (Rec val rec lnrepls) = val
getElement l {prf=(InThere prfThere)} (Rec val rec lnrepls) = getElement l {prf=prfThere} rec -}


namespace Ej1
  --Ejemplos simples de records extensibles
  Age : Label
  Age = MkLabel "Age" Nat

  AgeWrong : Label
  AgeWrong = MkLabel "Age" String

  Name : Label
  Name = MkLabel "Name" String

  -- Este ejemplo compila, y devuelve un record con un unico valor
  example1 : Record [Age]
  example1 = Rec 2 NulRec prf
    where
      -- La definicion de tipo de esta prueba puede sacarse
      prf : Not (InLabel Age [])
      prf = getNo (isInLabel Age [])
    
  -- Este ejemplo tambien compila. Esto muestra como agregar campos a records
  example2 : Record [Name, Age]
  example2 = Rec "John" example1 prf
    where
      prf = getNo (isInLabel Name [Age])

  -- Este caso no compila. Se esta intentando agregar un label "AgeWrong" con el mismo titulo que "Age" (aunque tienen tipos distintos, uno
  -- Nat y otro String). La busqueda automatica de la prueba falla con esto    
  {-example3 : Record [AgeWrong, Age]
  example3 = Rec "Wrong" example1 prf
    where
      prf = getNo (isInLabel AgeWrong [Age])-}


  -- Ejemplo de obtener datos de un record
  ex2Age : Nat
  ex2Age = getElement Age example2
  
  ex2Name : String
  ex2Name = getElement Name example2
  
  -- Es typesafe. Por ejemplo, este caso de abajo tira error de compilacion
  {-ex1Name : String
  ex1Name = getElement Name example1-}
