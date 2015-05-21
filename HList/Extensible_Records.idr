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

-- Relacion de equivalencia entre labels. Un label es identico a otro si tienen el mismo titulo, sin importar sus tipos
data SameLabel : Label -> Label -> Type where
  IsSame : SameLabel (MkLabel s t1) (MkLabel s t2)

notTheSameLabel : Not (s = w) -> Not (SameLabel (MkLabel s t1) (MkLabel w t2))
notTheSameLabel sneqw IsSame = sneqw Refl

-- Funcion de decision sobre igualdad de labels
isSameLabel : (l1 : Label) -> (l2 : Label) -> Dec (SameLabel l1 l2)
isSameLabel (MkLabel s1 t1) (MkLabel s2 t2)  with (decEq s1 s2)
  isSameLabel (MkLabel s t1) (MkLabel s t2) | Yes Refl = Yes IsSame
  isSameLabel (MkLabel s1 t1) (MkLabel s2 t2) | No s1neqs2 = No (notTheSameLabel s1neqs2)

-- Repeated Label
-- Relacion de inclusion. "RepLabel l ls" indica que el label "l" esta repetido en el vector de labels "ls". Esta repetido si ya existe
-- otro label con un titulo igual
data RepLabel : Label -> Vect n Label -> Type where
  RepHere : SameLabel l1 l2 -> RepLabel l1 (l2 :: ls)
  RepThere : RepLabel l ls -> RepLabel l (y :: ls)

-- Ninguna label puede estar repetida en un vector vacio
noEmptyRepLabel : {l : Label} -> RepLabel l [] -> Void
noEmptyRepLabel (RepHere isSame) impossible

-- Un label que no esta en la cabeza ni cola de la lista no esta en la lista
neitherRepHereNorRepThere : {x, y : Label} -> {xs : Vect n Label} -> Not (SameLabel x y) -> Not (RepLabel x xs) -> Not (RepLabel x (y :: xs))
neitherRepHereNorRepThere xneqy xnrepxs (RepHere IsSame) = xneqy IsSame
neitherRepHereNorRepThere xneqy xnrepxs (RepThere xinxs) = xnrepxs xinxs

-- Funcion de decision que indica si un label esta repetido en una lista de labels o no
isRepeatedLabel : (l : Label) -> (ls : Vect n Label) -> Dec (RepLabel l ls)
isRepeatedLabel l [] = No noEmptyRepLabel
isRepeatedLabel l (x :: xs) with (isSameLabel l x)
  isRepeatedLabel l (x :: xs) | Yes prf = Yes (RepHere prf)
  isRepeatedLabel l (x :: xs) | No lneqx with (isRepeatedLabel l xs)
    isRepeatedLabel l (x :: xs) | No lneqx | Yes lrepxs = Yes (RepThere lrepxs)
    isRepeatedLabel l (x :: xs) | No lneqx | No lnrepxs = No (neitherRepHereNorRepThere lneqx lnrepxs)

-- Records
-- Un record contiene una lista de labels no repetidos (no se repiten si tienen titulos distintos). A cada label se le asocia un valor
-- del tipo correspondiente.
-- El titulo del label puede pasarse implicitamente, siempre que se defina en el tipo y se pueda inferir
data Record : Vect k Label -> Type where
    NulRec : Record []
    Rec : {t : Type} -> {s : String} -> (val : t) -> Record ts -> (prf : Not (RepLabel (MkLabel s t) ts)) -> Record ((MkLabel s t)::ts)

-- Funcion que ayuda a obtener pruebas automaticas
getNo : (res : Dec p) -> case res of { Yes _ => () ; No _ => Not p }
getNo (Yes prf) = ()
getNo (No contra) = contra

namespace Ej1
  -- Un ejemplo
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
      prf : Not (RepLabel Age [])
      prf = getNo (isRepeatedLabel Age [])
    
  -- Este ejemplo tambien compila. Esto muestra como agregar campos a records
  example2 : Record [Name, Age]
  example2 = Rec "John" example1 prf
    where
      prf = getNo (isRepeatedLabel Name [Age])

  -- Este caso no compila. Se esta intentando agregar un label "AgeWrong" con el mismo titulo que "Age" (aunque tienen tipos distintos, uno
  -- Nat y otro String). La busqueda automatica de la prueba falla con esto    
  {-example3 : Record [AgeWrong, Age]
  example3 = Rec "Wrong" example1 prf
    where
      prf = getNo (isRepeatedLabel AgeWrong [Age])-}
