{-
  En este archivo genero algunos ejemplos de listas heterogeneas utilizando la libreria Data.HVect que ya viene con Idris
-}


import Data.HVect
import Data.Vect
import Data.Fin

%default total

hVectEx1 : HVect [String, List Nat, Nat, (Nat, Nat)]
hVectEx1 = ["Hello",[1,2,3],42,(0,10)]

-- La funcion "index" obtiene el valor de la lista en un indice en particular
fstEx : String
fstEx = index 0 hVectEx1
-- fstEx = "Hello"

sndEx : Nat
sndEx = Data.HVect.index 2 hVectEx1
-- sndEx = 42

-- La funcion "deleteAt" elimina un elemento de la lista en un indice en particular
hVectEx2 : HVect [String,Nat,(Nat,Nat)]
hVectEx2 = deleteAt 1 hVectEx1
-- hVectEx2 = ["Hello, 42, (0,10)]

{-
  La funcion "replaceAt" reemplaza un elemento en la lista en un determinado indice.
  Puede cambiar el tipo de ese elemento si es necesario
-}
hVectEx3 : HVect [String, String, Nat, (Nat, Nat)]
hVectEx3 = replaceAt 1 "77" hVectEx1
-- hVectEx3 = ["Hello", "77", 42, (0, 10)]

-- La funcion "updateAt" funciona como "replaceAt", pero toma una funcion que transforma tal elemento en ese indice
hVectEx4 : HVect [String, List Nat, Nat, String]
hVectEx4 = updateAt 3 (\(a,b) => show a ++ show b) hVectEx1
-- hVectEx4 = ["Hello", [1,2,3], 42, "010"]

{-
  Este ejemplo utiliza la funcion "get". Esta funcion obtiene un valor de la lista heterogenea de forma automatica.
  Esto solo funciona si los tipos no son ambiguos. Si la funcion que llama a "get" necesita un Nat, y se tiene
  HVect [Nat,String,List Nat], el interprete automaticamente infiere que se quiere el 1er valor de la lista, ya que es el
  unico valor con tipo Nat. Si se tienen varios valores con el mismo tipo en la lista, por ejemplo HVect [Nat,Nat], "get"
  va a utilizar el primero que encuentre
-}
hValEx1 : Nat
hValEx1 = Prelude.List.length $ get hVectEx1
-- hValEx1 = 3

{-
  Este ejemplo muestra que pasa cuando se utiliza "get" y se requiere un valor con un tipo que esta repetido en la lista heterogenea
  En este ejemplo, hVectEx3 tiene tipo HVect [String, String, Nat, (Nat, Nat)], y la funcion (++) necesita un valor de tipo String.
  Pero en este caso existen 2 valores con tipo String en la lista, "Hello" y "77". En este caso, el theorem prover de idris crea
  automaticamente una prueba de que existe el valor en la lista, y apenas encuentre el 1ero para. Por lo tanto encuentra "Hello", nota
  que tiene el mismo tipo y lo utiliza. Por lo tanto hValEx2 tiene el valor "Hello World!"
-}
hValEx2 : String
hValEx2 = (get hVectEx3) ++ " World!"
-- hValEx2 = "Hello World!"

{-
  La funcion "put" funciona como "get", pero modifica un valor. Analiza automaticamente cual elemento de la lista se debe modificar, viendo 
  su tipo. Si hay varios del mismo tipo, toma el primero que encuentra, al igual que "get"
-}
hVectEx5 : HVect [String, List Nat, Nat, (Nat, Nat)]
hVectEx5 = put (the Nat 3) hVectEx1
-- hVectEx5 =  ["Hello", [1,2,3], 3, (0,10)]

hVectEx6 : HVect [String, String, Nat, (Nat, Nat)]
hVectEx6 = put "Test" hVectEx3 
-- hVectEx6 = ["Test", "77", 42, (0, 10)]

{-
  "update" funciona igual que "get" y "put", pero toma una funcion y modifica el valor
-}
hVectEx7 : HVect [String, Nat, Nat, (Nat, Nat)]
hVectEx7 = update sum hVectEx1
-- hVectEx7 = ["Hello", 6, 42, (0,10)]

      {- Otras funciones de ejemplo -}
      
hLength : HVect xs -> Nat
hLength [] = 0
hLength (x :: xs) = 1 + hLength xs

      {- Ejemplo de uso de HVect: Extensible Records-}

{-
  Esta funcion toma 2 listas heterogeneas dummy (con cualquier valor) y crea un nuevo tipo HVect que es la concatenacion de ambos
-}  
ExtendHVect : {xs : Vect n Type} -> {ys : Vect m Type} -> HVect xs -> HVect ys -> Type
ExtendHVect {xs=xs} {ys=ys} _ _ = HVect (xs ++ ys)

  -- Person
  
data Name = NameC String
data Age =  AgeC Nat

getName : {default tactics { search 100; } p : Elem Name ts} -> HVect ts -> Name
getName {p=p} person = get {p=p} person

getAge : {default tactics { search 100; } p : Elem Age ts} -> HVect ts -> Age
getAge {p=p} person = get {p=p} person

Person : Type
Person = HVect [Name, Age]

dummyPerson : Person
dummyPerson = [NameC "",AgeC 0]

personEx : Person
personEx = [NameC "John",AgeC 25]

  -- Student

data Grade = GradeC Nat

dummyGradeVect : HVect [Grade]
dummyGradeVect = [GradeC 0]

getGrade :  {default tactics { search 100; } p : Elem Grade ts} -> HVect ts -> Grade
getGrade {p=p} student = get {p=p} student

Student : Type
Student = ExtendHVect dummyPerson dummyGradeVect

studentEx : Student
studentEx = [NameC "Mario",AgeC 20,GradeC 100]

studGrade : Grade
studGrade = getGrade studentEx
-- studGrade = GradeC 100

-- Aunque defini el tipo Student sin conocer lo que tiene Person, puedo igual llamar a getAge
studAge : Age
studAge = getAge studentEx
-- studAge = AgeC 20


{- 
   Luego del 08/04
   Investigacion sobre listas heterogeneas con elementos de tipos distintos
-}

-- Prueba explicita
namespace NR_Exp
  data HVect : Vect k Type -> Type where
    Nil : NR_Exp.HVect []
    (::) : t -> Not (Elem t ts) -> NR_Exp.HVect ts -> NR_Exp.HVect (t::ts)

  -- Ejemplo de lista heterogenea sin tipos repetidos, donde se debe pasar la prueba de forma explicita
  natStringPrf : Not (Elem Nat [String])    
  natStringPrf (There elemNatNil) = noEmptyElem elemNatNil
  
  stringPrf : Not (Elem String [])
  stringPrf elemStrNil = noEmptyElem elemStrNil

  -- Representa la lista [1,"Test"]
  hVectExample : NR_Exp.HVect [Nat, String]
  hVectExample = (::) 1 natStringPrf $ (::) "Test" stringPrf []
  
