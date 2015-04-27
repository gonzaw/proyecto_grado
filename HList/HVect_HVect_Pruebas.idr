{-
  En este archivo incluyo algunas pruebas que hice con listas heterogeneas, pero que por algun motivo no funcionaron
-}

import Data.HVect
import Data.Vect
import Data.Fin

%default total

-- Investigacion de pruebas implicitas/automaticas de listas heterogeneas con tipos no repetidos

-- Prueba implicita
namespace NR_Imp
  -- En este caso estuve probando utilizar "auto" para crear la prueba implicita. Pero no funciono, ya que Idris nunca podria generar
  -- la prueba
  data HVect : Vect k Type -> Type where
    Nil : NR_Imp.HVect []
    (::) : t ->  {auto prf : Not (Elem t ts)} -> NR_Imp.HVect ts -> NR_Imp.HVect (t::ts)
  
  -- Por ejempo, esto de abajo siempre tiraria error de typechecking
  {-hVectExample : NR_Imp.HVect [String]
  hVectExample = ["test"] -}

 -- Debajo voy a seguir una guia para crear pruebas de Idris
 -- http://www.davidchristiansen.dk/2014/05/21/idris-dec-techniques/
 -- Uno de los ejemplos que menciona, adaptado a este problema, no compila, tirando este error:
 -- "When elaborating type of Main.proofTest, getProof: Can't resolve type class DeqEq Type"
 -- 
 {-proofTest : Not (Elem Nat [String,String])
 proofTest = getProof
  where getProof : {prf : Not (Elem Nat [String,String])} -> 
                   {auto yep : isElem Nat [String,String] = No prf} -> Not (Elem Nat [String, String])
        getProof {prf} = prf -}
         
 -- Sin embargo, esto de abajo si funciona. Es porque el tipo Nat tiene definido una instancia de DeqEq
 proofTest : Not (Elem 1 [2,3])
 proofTest = getProof
  where getProof : {prf : Not (Elem 1 [2,3])} -> 
                   {auto yep : isElem 1 [2,3] = No prf} -> Not (Elem 1 [2, 3])
        getProof {prf} = prf
 
 -- Al parecer, es necesario que los tipos a utilizar tengan una instancia de DeqEq. 
 -- Aca hay una lista de los tipos que tienen definida tal instancia: 
 --    https://github.com/idris-lang/Idris-dev/blob/3d818586c3b674982c38627803388b9e4ded743f/libs/prelude/Decidable/Equality.idr
 -- No se puede utilizar con "Type" porque Type es un tipo sin limites, abarca todo posible tipo. Pero con uno como Nat/Bool si se
 -- puede, ya que son datatypes que se puede demostrar que uno es igual a otro
 
 -- Este ejemplo de abajo corresponde al ultimo del blog
 getNo : (res : Dec p) -> case res of { Yes _ => () ; No _ => Not p }
 getNo (Yes prf) = ()
 getNo (No contra) = contra

 -- Funciona con valores comunes, como una lista de Nat
 proofTest2 : Not (Elem 1 [2,3])
 proofTest2 = getNo (isElem 1 [2,3])

 -- Pero no funciona con tipos mismos, por el mismo problema de arriba (no encuentra instancia de DeqEq)
 {-dec_elem_bad : Not (Elem Nat [String])
 dec_elem_bad = getNo (isElem Nat [String])-}

 -- No puedo usar "getNo" por el mismo problema, no lo puedo usar con tipos. Esta lista heterogenea de abajo no compila
 {-testHVect : NR_Imp.HVect [Nat, String]
 testHVect = (::) 1 {prf = prf2} $ (::) "Test" {prf = prf2} []
   where 
     prf2 = getNo (isElem Nat [String])
     prf1 = getNo (isElem String []) -}



-- Investigacion de Tacticas
-- Debajo estan mis intentos de investigar tacticas, o algun tipo de reflection para generar las pruebas automaticas

--Ejemplo de tactica que funciona
normPlus : List (TTName, Binder TT) -> TT -> Tactic
normPlus ctxt `((=) {Nat} {Nat} ~x ~y) = normPlus ctxt x `Seq` normPlus ctxt y
normPlus ctxt `(S ~n) = normPlus ctxt n
normPlus ctxt `(plus ~n (S ~m)) = Seq (Rewrite `(plusSuccRightSucc ~n ~m)) (normPlus ctxt m)
normPlus _ _ = Skip

-- Esto de abajo me tira error de typechecking.
-- Utilizando la tactica de arriba, tenia pensado hacer pattern matching sobre el goal "Not (Elem t ts)", para poder crear una 
-- tactica que encuentre su prueba.
-- Leyendo codigo de Idris sobre reflection, parece ser que para hacer el pattern matching con esa "quotation" (como lo describe Idris)
-- es necesario que se haga una instancia de Quotable:
-- https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Language/Reflection.idr 
{-notFindElem : List (TTName, Binder TT) -> TT -> Tactic
notFindElem ctxt `(Not (Elem ~t ~ts)) = Skip
notFindElem _ _ = Skip -}

-- Esta es la instancia definida. Tira el siguiente error de typechecking:
-- Can't unify Type (Type of ts) with Vect k Type (Expected type)
-- Me parece que se debe a que no se pueden usar tipos dependientes en esta instancia de Quotable.
{-instance (Quotable t TT, Quotable ts TT) => Quotable (Elem t ts) TT where
  quotedTy = `(Elem ~(quotedTy {t}) ~(quotedTy {ts}))
  quote Here = `(Elem.Here {t=~(quotedTy {t})} {ts=~(quotedTy {ts})})
  quote (There elm) = `(Elem.There {t=~(quotedTy {t})} {ts=~(quotedTy {ts})} ~(quote elm))-}
  
 -- Esta tactica es un intento de implementar una que pruebe que un elemento no este en una lista.
 -- Sin embargo no se pudo encontrar la forma de utilizarlo (el codigo mismo corresponde a una tactica "findElem" que prueba que
 -- un elemento si esta en una lista)
 {-notFindElem : (n : Nat) -> List (TTName, Binder TT) -> TT -> Tactic
 notFindElem Z ctxt goal = Refine "Here" `Seq` Solve
 notFindElem (S n) ctxt goal = GoalType "Elem" (Try (Refine "Here" `Seq` Solve) (Refine "There" `Seq` (Solve `Seq` findElem n ctxt goal)))
 -}

-- Esta prueba de abajo fue un intento de crear la prueba con el sistema de prueba de teoremas interactivo de idris. Sin embargo
-- no pude realizar tal prueba con las tacticas limitadas de Idris
{-proofTest : Not (Elem Nat [String,String,String,String,String])
proofTest = ?proofTest_rhs-} 

-- Para poder intentar crear tal prueba con el sistema interactivo de Idris, se intento agregar el tag %elim al tipo Elim mismo
-- Este tag permite utilizar tacticas destructivas, es decir, tacticas que te permitan hacer pattern matching. En este caso te permitirian
-- realizar pattern matching sobre "Here" o "There"
-- Esta definicion de abajo es identica a Elem de Data.Vect, pero el solo hecho de agregar %elim tira error de typechecking:
-- "Can't unify Nat (Type of carg__2_ with Vect k Type (Expected type)"
-- Tal vez tal problema se de porque el tipo Elem depende de un vector, que es un tipo dependiente de un natural. Tal vez tal uso de
-- tipos dependientes no permita definir %elim correctamente
{-namespace NewElem
  %elim
  data Elem : a -> Vect k a -> Type where
       Here : NewElem.Elem x (x::xs)
       There : NewElem.Elem x xs -> NewElem.Elem x (y::xs)-}
