{-
  En este archivo se va a hacer un port de HList de haskell, pensando en records extensibles.
  
  Paper: http://okmij.org/ftp/Haskell/HList-ext.pdf
  
-}

import Data.Vect
import Data.Fin

%default total

namespace HList

  {- Seccion 3 - Typeful heterogeneous lists -}

  -- Definicion sacada de HVect (de idris)  
  data HList : Vect k Type -> Type where
    Nil : HList []
    (::) : t -> HList ts -> HList (t::ts)
    
  infix 5 .*.
  (.*.) : t -> HList ts -> HList (t::ts) 
  (.*.) = (::)
  
  -- List-processing operations
  hAppend : HList t1 -> HList t2 -> HList (t1++t2)
  hAppend Nil = id
  hAppend (v1 :: l1) = (v1 ::) . hAppend l1
  
  data HAppend : HList t1 -> HList t2 -> HList (t1++t2) -> Type where
    HAppendNil : HAppend Nil l2 l2
    HAppendCons : HAppend l1 l2 l3 -> HAppend (v1 :: l1) l2 (v1 :: l3) 
  
  (++) : HList t1 -> HList t2 -> HList (t1++t2)
  (++) = hAppend
  
  {- Seccion 4 - Numeral-based access operations: -}
  hLookupByHNat : (i : Fin k) -> HList ts -> index i ts
  hLookupByHNat FZ (x :: xs) = x
  hLookupByHNat (FS j) (x :: xs) = hLookupByHNat j xs

  data HLookupByHNat : (i : Fin k) -> HList ts -> index i ts -> Type where
    HLookupByHNatFZ : HLookupByHNat FZ (x :: xs) x
    HLookupByHNatFS : HLookupByHNat j xs res -> HLookupByHNat (FS j) (x :: xs) res
  
  hDeleteAtHNat : (i : Fin (S l)) -> HList us -> HList (deleteAt i us)
  hDeleteAtHNat FZ (x :: xs) = xs
  hDeleteAtHNat {l = S m} (FS j) (x :: xs) = x :: hDeleteAtHNat j xs
  hDeleteAtHNat {l = Z}   (FS j) (x :: xs) = absurd j
  hDeleteAtHNat _ [] impossible
  
  data HDeleteAtHNat : (i : Fin (S l)) -> HList us -> HList (deleteAt i us) -> Type where
    HDeleteAtHNatFZ : HDeleteAtHNat FZ (x :: xs) xs
    HDeleteAtHNatFS : {j : Fin (S m)} -> HDeleteAtHNat j xs res -> HDeleteAtHNat (FS j) (x :: xs) (x :: res)
  
  hUpdateAtHNat : (i : Fin k) -> t -> HList ts -> HList (replaceAt i t ts)
  hUpdateAtHNat FZ y (x :: xs) = y :: xs
  hUpdateAtHNat (FS j) y (x :: xs) = x :: hUpdateAtHNat j y xs

  data HUpdateAtHNat : (i : Fin k) -> t -> HList ts -> HList (replaceAt i t ts) -> Type where
    HUpdateAtHNatFZ : HUpdateAtHNat FZ y (x :: xs) (y :: ys)
    HUpdateAtHNatFS : HUpdateAtHNat j y xs res -> HUpdateAtHNat (FS j) y (x :: xs) (x :: res)
      
  -- Referencia para estas operaciones se saca del siguiente link:
  -- https://hackage.haskell.org/package/HList-0.2/docs/src/Data-HList-HArray.html#HSplitByHNats%27
  -- https://hackage.haskell.org/package/HList-0.4.0.0/docs/src/Data-HList-HList.html
  
  hLength : HList ts -> Nat
  hLength [] = 0
  hLength (h :: hs) = 1 + (hLength hs)
  
  data HLength : HList ts -> Nat -> Type where
    HLengthNil : HLength [] 0
    HLengthCons : HLength hs res -> HLength (h :: hs) (1 + res)
  
  data HMaxLength : HList ts -> Nat -> Type where
    IsMax : LTE (hLength l) (S s) -> HMaxLength l s
    
    
  {- Seccion 5 - Extensible records: -}
  
  -- zipWith Pair : Vect k Type -> Vect k Type -> Vect k Type
  -- A diferencia de zip: Vect k t1 -> Vect k t2 -> Vect k (t1,t2)
  hZip : HList ls1 -> HList ls2 -> HList (zipWith Pair ls1 ls2)
  hZip [] [] = []
  hZip (x :: xs) (y :: ys) = (x, y) :: hZip xs ys

  -- Nota: Esta funcion es mas dificil de utilizar, ya que cada vez que se usa se debe probar que lo que se pasa por parametro es
  -- exactamente un "zipWith Pair ls1 ls2"
  hUnZip : HList (zipWith Pair ls1 ls2) -> (HList ls1, HList ls2)
  hUnZip {ls1=[]} {ls2=[]} [] = ([], [])
  hUnZip {ls1=(tx::txs)} {ls2=(ty::tys)} ((x,y) :: ls) = 
    let (uzLeft, uzRight) = hUnZip ls
    in (x :: uzLeft, y :: uzRight)
   
  
  -- Funciones que ayudan a obtener pruebas automaticas
  getNo : (res : Dec p) -> case res of { Yes _ => () ; No _ => Not p }
  getNo (Yes prf) = ()
  getNo (No contra) = contra

  getYes : (res : Dec p) -> case res of { Yes _ => p ; No _ => () }
  getYes (Yes prf) = prf
  getYes (No contra) = ()

  -- Igual a las de arriba, pero obtiene la prueba necesaria sin importar si es Yes o No
  getDec : (res : Dec p) -> case res of { Yes _ => p; No _ => Not p}
  getDec (Yes prf) = prf
  getDec (No contra) = contra

  -- Definicion usada en ExtensibleRecords.idr
  data HMember_1 : lty -> Vect n (lty, Type) -> Type where
    HMember1InHere : HMember_1 lbl ((lbl,ty) :: ls)
    HMember1InThere : HMember_1 lbl1 ls -> HMember_1 lbl1 ((lbl2,ty) :: ls)

  data HLabelSet_1 : Vect n (lty, Type) -> Type where
    HLabelSet1Nil : HLabelSet_1 []
    HLabelSet1Cons : Not (HMember_1 lbl ls) -> HLabelSet_1 ls -> HLabelSet_1 ((lbl,ty) :: ls)

  -- Pruebas y funcion de decision para HMember_1
  noEmptyInLabel_1 : HMember_1 lbl [] -> Void
  noEmptyInLabel_1 (HMember1InHere) impossible
  
  neitherInHereNorInThere_1 : {lbl1, lbl2 : lty} -> {ls : Vect n (lty, Type)} -> Not (lbl1 = lbl2) -> Not (HMember_1 lbl1 ls) 
                             -> Not (HMember_1 lbl1 ((lbl2, ty) :: ls))
  neitherInHereNorInThere_1 l1neql2 l1ninls HMember1InHere = l1neql2 Refl
  neitherInHereNorInThere_1 l1neql2 l1ninls (HMember1InThere l1inls) = l1ninls l1inls

  ifNotInThereThenNotInHere_1 : {lbl1, lbl2 : lty} -> {ls : Vect n (lty, Type)} -> Not (HMember_1 lbl1 ((lbl2, ty) :: ls)) 
                            -> Not (HMember_1 lbl1 ls)
  ifNotInThereThenNotInHere_1 l1nincons l1inls = l1nincons (HMember1InThere l1inls)
  
  isInLabelList_1 : DecEq lty => (lbl : lty) -> (ls : Vect n (lty, Type)) -> Dec (HMember_1 lbl ls)       
  isInLabelList_1 lbl [] = No noEmptyInLabel_1
  isInLabelList_1 lbl1 ((lbl2, ty) :: ls) with (decEq lbl1 lbl2)
    isInLabelList_1 lbl1 ((lbl1, ty) :: ls) | Yes Refl = Yes HMember1InHere
    isInLabelList_1 lbl1 ((lbl2, ty) :: ls) | No l1neql2 with (isInLabelList_1 lbl1 ls)
      isInLabelList_1 lbl1 ((lbl2, ty) :: ls) | No l1neql2 | Yes l1inls = Yes (HMember1InThere l1inls)
      isInLabelList_1 lbl1 ((lbl2, ty) :: ls) | No l1neql2 | No l1ninls = No (neitherInHereNorInThere_1 l1neql2 l1ninls)

  ifNotLabelSetHereThenNeitherThere_1 : Not (HLabelSet_1 ls) -> Not (HLabelSet_1 ((l,ty) :: ls))
  ifNotLabelSetHereThenNeitherThere_1 lsnotls (HLabelSet1Cons lnotm lsyesls) = lsnotls lsyesls  
  
  ifHasRepeatedThenNotLabelSet_1 : HLabelSet_1 ls -> HMember_1 l ls -> Not (HLabelSet_1 ((l,ty) :: ls))      
  ifHasRepeatedThenNotLabelSet_1 lsyesls linls (HLabelSet1Cons lninls lsyesls_2) = lninls linls
  
  -- Esta es la funcion de decision que determina si una lista de labels tiene repetidos o no    
  isLabelSet_1 : DecEq lty => (ls : Vect n (lty, Type)) -> Dec (HLabelSet_1 ls)
  isLabelSet_1 [] = Yes HLabelSet1Nil
  isLabelSet_1 ((l,ty) :: ls) with (isLabelSet_1 ls)
    isLabelSet_1 ((l,ty) :: ls) | No lsnotls = No $ ifNotLabelSetHereThenNeitherThere_1 lsnotls
    isLabelSet_1 ((l,ty) :: ls) | Yes lsyesls with (isInLabelList_1 l ls)
      isLabelSet_1 ((l,ty) :: ls) | Yes lsyesls | No lninls = Yes $ HLabelSet1Cons lninls lsyesls
      isLabelSet_1 ((l,ty) :: ls) | Yes lsyesls | Yes linls = No $ ifHasRepeatedThenNotLabelSet_1 lsyesls linls

  -- Definicion traducida de HList
  data HMember_2 : lty -> Vect n (lty, Type) -> Bool -> Type where
    HMember2Nil : HMember_2 lbl [] False
    HMember2InHere : HMember_2 lbl ((lbl,ty) :: ls) True
    HMember2InThere : HMember_2 lbl1 ls b -> HMember_2 lbl1 ((lbl2,ty) :: ls) b 

  data HLabelSet_2 : Vect n (lty, Type) -> Type where
    HLabelSet2Nil : HLabelSet_2 []
    HLabelSet2Cons : HMember_2 lbl ls False -> HLabelSet_2 ls -> HLabelSet_2 ((lbl,ty) :: ls)

  -- Idem al anterior, pero sin el par (_, Type)
  data HMember_3 : lty -> Vect n lty -> Bool -> Type where
    HMember3Nil : HMember_3 lbl [] False
    HMember3InHere : HMember_3 lbl (lbl :: ls) True
    HMember3InThere : HMember_3 lbl1 ls b -> HMember_3 lbl1 (lbl2 :: ls) b 

  data HLabelSet_3 : Vect n lty -> Type where
    HLabelSet3Nil : HLabelSet_3 []
    HLabelSet3Cons : HMember_3 lbl ls False -> HLabelSet_3 ls -> HLabelSet_3 (lbl :: ls)

  -- Nueva definicion, con desigualdad de valores (es correcta, al igual que la #1)
  data HMember_4 : lty -> Vect n lty -> Bool -> Type where
    HMember4Nil : HMember_4 lbl [] False
    HMember4InHere : HMember_4 lbl (lbl :: ls) True
    HMember4InThere : HMember_4 lbl1 ls True -> HMember_4 lbl1 (lbl2 :: ls) True
    HMember4NotInThere : Not (lbl1 = lbl2) -> HMember_4 lbl1 ls False -> HMember_4 lbl1 (lbl2 :: ls) False

  data HLabelSet_4 : Vect n lty -> Type where
    HLabelSet4Nil : HLabelSet_4 []
    HLabelSet4Cons : HMember_4 lbl ls False -> HLabelSet_4 ls -> HLabelSet_4 (lbl :: ls)

  -- Definiciones Posibles de HEq (la de HList)
  -- Esta de abajo no compilar, o mas bien no se puede definir
  {-data HEq : DecEq ty => ty -> ty -> Bool -> Type where
    HEqual : DecEq ty => HEq v1 v1 True
    HNEqual : DecEq ty => ???-}
    
  -- Por algun motivo raro, estas definiciones compilan y se typechequean bien
  -- La definicion "refl" funciona en todos los casos menos en el ultimo de Nat (HEq Nat (S n1) (S n2) b), por eso lo saque. No se
  -- si es necesario
  class HEq t (v1 : t) (v2 : t) (b : Bool) | t, v1, v2 where
     --refl : if b then v1 = v2 else Not (v1 = v2)
  
  {-
  -- Instancia para naturales, como esta definida en HList   
  instance HEq Nat Z Z True where
    --refl = Refl

  instance HEq Nat Z (S n) False where
    --refl ZisS = absurd ZisS
    
  instance HEq Nat (S n) Z False where
    --refl SisZ = absurd SisZ
    
  instance HEq Nat n1 n2 b => HEq Nat (S n1) (S n2) b where
    --refl : if b then (S n1) = (S n2) else Not ((S n1) = (S n2))
    -}
    
  -- Instancia para naturales, utilizando la instancia "Eq" de Nat
  --instance HEq Nat n1 n2 (n1 == n2) where  
    
  -- Instancia para strings
  --instance HEq String s1 s2 (s1 == s2) where
  
  -- Instancia generica para tipos con "Eq"
  instance Eq t => HEq t v1 v2 (v1 == v2) where
    
  -- Esta es la definicion mas literal basada en HList, que necesita HEq. Aunque en la practica, como no hay reglas de inferencia
  -- como para las typeclasses de Haskell, no funciona muy bien (se necesita pasar la prueba explicita de HEq y HMember_5 de todas
  -- formas)
  data HMember_5 : lty -> Vect n lty -> Bool -> Type where
    HMember5Nil : HMember_5 lbl [] False
    HMember5InHere : HMember_5 lbl (lbl :: ls) True
    HMember5InThere : HEq lty lbl1 lbl2 b1 => HMember_5 lbl1 ls b2 -> HMember_5 lbl1 (lbl2 :: ls) (b1 || b2)
    
  data HLabelSet_5 : Vect n lty -> Type where
    HLabelSet5Nil : HLabelSet_5 []
    HLabelSet5Cons : HMember_5 lbl ls False -> HLabelSet_5 ls -> HLabelSet_5 (lbl :: ls)

  -- Definicion identica a HMember_1, pero solo para vector de labels
  data HMember_6 : lty -> Vect n lty -> Type where
    HMember6InHere : HMember_6 lbl (lbl :: ls)
    HMember6InThere : HMember_6 lbl1 ls -> HMember_6 lbl1 (lbl2 :: ls)

  data HLabelSet_6 : Vect n lty -> Type where
    HLabelSet6Nil : HLabelSet_6 []
    HLabelSet6Cons : Not (HMember_6 lbl ls) -> HLabelSet_6 ls -> HLabelSet_6 (lbl :: ls)
  
  -- Funciones auxiliares
  getNotMember_6 : HLabelSet_6 (lbl :: ls) -> Not (HMember_6 lbl ls)
  getNotMember_6 (HLabelSet6Cons notMember _) = notMember
  
  getRecLabelSet_6 : HLabelSet_6 (lbl :: ls) -> HLabelSet_6 ls
  getRecLabelSet_6 (HLabelSet6Cons _ recLabelSet) = recLabelSet


  -- Pruebas y funcion de decision para HMember_6
  noEmptyInLabel_6 : HMember_6 lbl [] -> Void
  noEmptyInLabel_6 (HMember6InHere) impossible
  
  neitherInHereNorInThere_6 : {lbl1, lbl2 : lty} -> {ls : Vect n lty} -> Not (lbl1 = lbl2) -> Not (HMember_6 lbl1 ls) 
                             -> Not (HMember_6 lbl1 (lbl2 :: ls))
  neitherInHereNorInThere_6 l1neql2 l1ninls HMember6InHere = l1neql2 Refl
  neitherInHereNorInThere_6 l1neql2 l1ninls (HMember6InThere l1inls) = l1ninls l1inls

  ifNotInThereThenNotInHere_6 : {lbl1, lbl2 : lty} -> {ls : Vect n lty} -> Not (HMember_6 lbl1 (lbl2 :: ls)) 
                            -> Not (HMember_6 lbl1 ls)
  ifNotInThereThenNotInHere_6 l1nincons l1inls = l1nincons (HMember6InThere l1inls)
  
  isInLabelList_6 : DecEq lty => (lbl : lty) -> (ls : Vect n lty) -> Dec (HMember_6 lbl ls)       
  isInLabelList_6 lbl [] = No noEmptyInLabel_6
  isInLabelList_6 lbl1 (lbl2 :: ls) with (decEq lbl1 lbl2)
    isInLabelList_6 lbl1 (lbl1 :: ls) | Yes Refl = Yes HMember6InHere
    isInLabelList_6 lbl1 (lbl2 :: ls) | No l1neql2 with (isInLabelList_6 lbl1 ls)
      isInLabelList_6 lbl1 (lbl2 :: ls) | No l1neql2 | Yes l1inls = Yes (HMember6InThere l1inls)
      isInLabelList_6 lbl1 (lbl2 :: ls) | No l1neql2 | No l1ninls = No (neitherInHereNorInThere_6 l1neql2 l1ninls)
      
  ifNotLabelSetHereThenNeitherThere_6 : Not (HLabelSet_6 ls) -> Not (HLabelSet_6 (l :: ls))
  ifNotLabelSetHereThenNeitherThere_6 lsnotls (HLabelSet6Cons lnotm lsyesls) = lsnotls lsyesls  
  
  ifHasRepeatedThenNotLabelSet_6 : HLabelSet_6 ls -> HMember_6 l ls -> Not (HLabelSet_6 (l :: ls))      
  ifHasRepeatedThenNotLabelSet_6 lsyesls linls (HLabelSet6Cons lninls lsyesls_2) = lninls linls
  
  -- Esta es la funcion de decision que determina si una lista de labels tiene repetidos o no    
  isLabelSet_6 : DecEq lty => (ls : Vect n lty) -> Dec (HLabelSet_6 ls)
  isLabelSet_6 [] = Yes HLabelSet6Nil
  isLabelSet_6 (l :: ls) with (isLabelSet_6 ls)
    isLabelSet_6 (l :: ls) | No lsnotls = No $ ifNotLabelSetHereThenNeitherThere_6 lsnotls
    isLabelSet_6 (l :: ls) | Yes lsyesls with (isInLabelList_6 l ls)
      isLabelSet_6 (l :: ls) | Yes lsyesls | No lninls = Yes $ HLabelSet6Cons lninls lsyesls
      isLabelSet_6 (l :: ls) | Yes lsyesls | Yes linls = No $ ifHasRepeatedThenNotLabelSet_6 lsyesls linls
   
  -- Idem que HLabelSet_6, pero para List en vez de Vect
  data HMember_7 : lty -> List lty -> Type where
    HMember7InHere : HMember_7 lbl (lbl :: ls)
    HMember7InThere : HMember_7 lbl1 ls -> HMember_7 lbl1 (lbl2 :: ls)

  data HLabelSet_7 : List lty -> Type where
    HLabelSet7Nil : HLabelSet_7 []
    HLabelSet7Cons : Not (HMember_7 lbl ls) -> HLabelSet_7 ls -> HLabelSet_7 (lbl :: ls)

  -- Pruebas y funcion de decision para HMember_7
  noEmptyInLabel_7 : HMember_7 lbl [] -> Void
  noEmptyInLabel_7 (HMember7InHere) impossible
  
  neitherInHereNorInThere_7 : {lbl1, lbl2 : lty} -> {ls : List lty} -> Not (lbl1 = lbl2) -> Not (HMember_7 lbl1 ls) 
                             -> Not (HMember_7 lbl1 (lbl2 :: ls))
  neitherInHereNorInThere_7 l1neql2 l1ninls HMember7InHere = l1neql2 Refl
  neitherInHereNorInThere_7 l1neql2 l1ninls (HMember7InThere l1inls) = l1ninls l1inls

  ifNotInThereThenNotInHere_7 : {lbl1, lbl2 : lty} -> {ls : List lty} -> Not (HMember_7 lbl1 (lbl2 :: ls)) 
                            -> Not (HMember_7 lbl1 ls)
  ifNotInThereThenNotInHere_7 l1nincons l1inls = l1nincons (HMember7InThere l1inls)
  
  isInLabelList_7 : DecEq lty => (lbl : lty) -> (ls : List lty) -> Dec (HMember_7 lbl ls)       
  isInLabelList_7 lbl [] = No noEmptyInLabel_7
  isInLabelList_7 lbl1 (lbl2 :: ls) with (decEq lbl1 lbl2)
    isInLabelList_7 lbl1 (lbl1 :: ls) | Yes Refl = Yes HMember7InHere
    isInLabelList_7 lbl1 (lbl2 :: ls) | No l1neql2 with (isInLabelList_7 lbl1 ls)
      isInLabelList_7 lbl1 (lbl2 :: ls) | No l1neql2 | Yes l1inls = Yes (HMember7InThere l1inls)
      isInLabelList_7 lbl1 (lbl2 :: ls) | No l1neql2 | No l1ninls = No (neitherInHereNorInThere_7 l1neql2 l1ninls)
      
  ifNotLabelSetHereThenNeitherThere_7 : Not (HLabelSet_7 ls) -> Not (HLabelSet_7 (l :: ls))
  ifNotLabelSetHereThenNeitherThere_7 lsnotls (HLabelSet7Cons lnotm lsyesls) = lsnotls lsyesls  
  
  ifHasRepeatedThenNotLabelSet_7 : HLabelSet_7 ls -> HMember_7 l ls -> Not (HLabelSet_7 (l :: ls))      
  ifHasRepeatedThenNotLabelSet_7 lsyesls linls (HLabelSet7Cons lninls lsyesls_2) = lninls linls
  
  -- Esta es la funcion de decision que determina si una lista de labels tiene repetidos o no    
  isLabelSet_7 : DecEq lty => (ls : List lty) -> Dec (HLabelSet_7 ls)
  isLabelSet_7 [] = Yes HLabelSet7Nil
  isLabelSet_7 (l :: ls) with (isLabelSet_7 ls)
    isLabelSet_7 (l :: ls) | No lsnotls = No $ ifNotLabelSetHereThenNeitherThere_7 lsnotls
    isLabelSet_7 (l :: ls) | Yes lsyesls with (isInLabelList_7 l ls)
      isLabelSet_7 (l :: ls) | Yes lsyesls | No lninls = Yes $ HLabelSet7Cons lninls lsyesls
      isLabelSet_7 (l :: ls) | Yes lsyesls | Yes linls = No $ ifHasRepeatedThenNotLabelSet_7 lsyesls linls

  -- Casos de prueba que pueda generar la prueba automaticamente, de forma inferida (como lo hace HList digamos)
  testHLabelSet_1 : (ls : Vect n (lty, Type)) -> {default tactics { search } prf : HLabelSet_1 ls} -> HLabelSet_1 ls
  testHLabelSet_1 ls {prf=prf} = prf
  
  testHLabelSet_2 : (ls : Vect n (lty, Type)) -> {default tactics { search } prf : HLabelSet_2 ls} -> HLabelSet_2 ls
  testHLabelSet_2 ls {prf=prf} = prf

  testHLabelSet_3 : (ls : Vect n lty) -> {default tactics { search } prf : HLabelSet_3 ls} -> HLabelSet_3 ls
  testHLabelSet_3 ls {prf=prf} = prf

  testHLabelSet_4 : (ls : Vect n lty) -> {default tactics { search } prf : HLabelSet_4 ls} -> HLabelSet_4 ls
  testHLabelSet_4 ls {prf=prf} = prf
  
  testHLabelSet_5 : (ls : Vect n lty) -> {default tactics { search } prf : HLabelSet_5 ls} -> HLabelSet_5 ls
  testHLabelSet_5 ls {prf=prf} = prf
  
  testHLabelSet_6 : (ls : Vect n lty) -> {default tactics { search } prf : HLabelSet_6 ls} -> HLabelSet_6 ls
  testHLabelSet_6 ls {prf=prf} = prf

  -- testHLabelSet 2 y 3 ejecutan bien, pero el predicado es incorrecto
  -- testHLabelSet 1, 4 y 6 no pueden generar la prueba, pero el predicado es correcto
  -- testHLabelSet 5 es correcto (me parece) pero tampoco puede generar la prueba de forma automatica con "search"
  -- NOTA: Usar testHLabelSet_5 con naturales, que tienen definido "HEq" mas arriba
  -- NOTA: HLabelSet_2 y HLabelSet_3 estan mal porque permiten definir predicados mal, como HLabelSet_3 [1,2,1]

  -- Algo interesante de HMember_5, es que funciona. Aca hay ejemplos que hace typechecking:
  -- the (HMember_5 "1" ["2","1","2"] True) $ HMember5InThere HMember5InHere
  -- the (HMember_5 "1" ["2","2"] False) $ HMember5InThere $ HMember5InThere HMember5Nil

  -- Definicion hibrida de record entre la de HList y la que hice anteriormente
  -- Como no pude definir HZip, creo los 2 tipos distintos de Records que indica HList
  
  -- Primera definicion de Record, donde se tiene una lista heterogenea de pares "Label"/"Tipo"
  data Record_1 : Vect n (lty, Type) -> Type where
    MkRecord1 : HLabelSet_6 ls -> HList ts -> Record_1 (zip ls ts)
    
  -- Segunda definicion de Record, donde se tienen 2 listas heterogeneas separadas para labels, y otra para los tipos  
  data Record_2 : Vect n lty -> Vect n Type -> Type where
    MkRecord2 : HLabelSet_6 ls -> HList ts -> Record_2 ls ts
  
  --mkRecord no puede obtener la prueba automatica de HLabelSet_6 ls usando el getYes
  {-mkRecord1 : DecEq lty => {ls : Vect n lty} -> HList ts -> Record_1 (zip ls ts)  mkRecord1 {ls=ls} hs = MkRecord1 prf hs
    where
        prf : HLabelSet_6 ls
        prf = getYes (isLabelSet_6 ls)-}
        
  mkRecord_1 : DecEq lty => {ls : Vect n lty} -> {prf : HLabelSet_6 ls} -> HList ts -> Record_1 (zip ls ts)
  mkRecord_1 {prf=prf} hs = MkRecord1 prf hs
      
  emptyRecord_1 : DecEq lty => Record_1 []
  emptyRecord_1 = MkRecord1 HLabelSet6Nil {ls=[]} []   
      
  mkRecord_2 : DecEq lty => {ls : Vect n lty} -> {prf : HLabelSet_6 ls} -> HList ts -> Record_2 ls ts
  mkRecord_2 {prf=prf} hs = MkRecord2 prf hs
  
  emptyRecord_2 : DecEq lty => Record_2 [] []
  emptyRecord_2 = MkRecord2 HLabelSet6Nil {ls=[]} []
  
  -- ** Version del HList de hackage (actualizado) **
  -- Mas abajo se muestran otras definiciones de Records, pero tomadas de la implementacion mas actualizada de HList (que esta en
  -- hackage)
  -- Link: https://hackage.haskell.org/package/HList
  
  
  -- Proyeccion --
     
  -- En algunos casos se necesita una istancia de "Eq a" en vez de "DecEq a". Pero se puede construir.
  -- Se necesita un wrapper para no tener instancias solapadas ni huerfanas (ej "Eq ()")
  data WrappedEq a = MkWrappedEq a
    
  wrapEq : a -> WrappedEq a
  wrapEq = MkWrappedEq
    
  unWrapEq : WrappedEq a -> a
  unWrapEq (MkWrappedEq a) = a
    
  instance DecEq a => Eq (WrappedEq a) where
    (==) a1 a2 = case (decEq (unWrapEq a1) (unWrapEq a2)) of
                    Yes _ => True
                    No _ => False


  -- #1 - HList que tiene labels en su tipo pero no en runtime (como Record de Extensible_Records.idr)
  -- Se llama HList3 para que este acorde a Record_3
  namespace HList3
    -- Con este tipo se pueden tener los labels a nivel de tipos y no en runtime
    data HList3 : Vect n (lty, Type) -> Type where
      Nil : HList3 []
      (::) : {lbl : lty} -> (val : t) -> HList3 ts -> HList3 ((lbl,t):: ts)
 
    -- Obtiene los labels de una lista de tal HList
    labelsOf : Vect n (lty, Type) -> Vect n lty
    labelsOf = map fst
    
    -- Asi se puede definir un nuevo record similar al de HList en hackage
    data Record_3 : Vect n (lty, Type) -> Type where
      MkRecord3 : HLabelSet_6 (labelsOf ts) -> HList3 ts -> Record_3 ts
    
    -- Prueba de que un vector con tipo "Vect 0 a" es el vector vacio
    vectCeroIsEmpty : (v : Vect 0 a) -> v = []
    vectCeroIsEmpty [] = Refl
    
    -- Funcion auxiliar parecida a "noEmptyElem", pero donde el [] no es explicito
    noEmptyElemImplicit : (xs : Vect 0 t) -> Elem x xs -> Void
    noEmptyElemImplicit xs xinxs = noEmptyElem $ replace (vectCeroIsEmpty xs) xinxs
    
    -- Funcion auxiliar para eliminar un elemento de un vector (uno solo, asume que no se repite, o que se puede llamar
    -- sucesivamente)
    deleteElem : {x : t} -> (xs : Vect (S n) t) -> Elem x xs -> Vect n t
    deleteElem (x :: xs) Here = xs
    deleteElem {n=S n} (x :: xs) (There xinthere) = x :: (deleteElem {n=n} xs xinthere)
    deleteElem {n=Z} (x :: xs) (There xinthere) = absurd $ noEmptyElemImplicit xs xinthere
    
    -- Si se tiene un Elem x xs, con xs de largo "k", entonces si o si "k" debe ser un "S n" (no puede ser 0)
    convertLengthElem : {xs : Vect k t} -> Elem x xs -> (n : Nat ** (xs2 : Vect (S n) t ** Elem x xs2))
    convertLengthElem {k = Z} {xs=xs} xinxs = absurd $ noEmptyElemImplicit xs xinxs
    convertLengthElem {k = S n} {xs=xs} xinxs = (n ** (xs ** xinxs))
    
    -- Aqui se puede definir hProjectByLabels. Esta funcion realiza lo mismo que las typeclasses H2ProjectByLabels, etc de HList
    -- (en hackage)
    hProjectByLabels : DecEq lty => {ts : Vect n (lty, Type)} -> Vect k lty -> HList3 ts ->     
      ((q1 : Nat ** (ls1 : Vect q1 (lty, Type) ** HList3 ls1)),
      (q2 : Nat ** (ls2 : Vect q2 (lty, Type) ** HList3 ls2)) )
    -- Si la lista de labels a proyectar es vacia, entonces a la izq no viene nada y a la der la HList original
    hProjectByLabels [] {n=n} {ts=ts} hs = ((0 ** ([] ** [])), (n ** (ts ** hs)))
    -- Si el HList es vacio, se debe devolver todo vacio
    hProjectByLabels _ [] = ((0 ** ([] ** [])), (0 ** ([] ** [])))
    hProjectByLabels {lty=lty} ls ((::) {lbl=l2} {t=t} {ts=ts2} val hs) = 
      -- Primero debo fijarme si el label del primer elemento del HList pertenece a la lista de labels a proyectar
      case (isElem l2 ls) of
        Yes l2inls => 
          -- Si pertenece, obtengo la lista de labels a proyectar SIN ese label
          let (modLs ** modL2inls) = getProof $ convertLengthElem l2inls
              lsNew = deleteElem modLs modL2inls
          -- Luego realizo la proyeccion de esa nueva lista sobre el resto del HList
              ((n3 ** (subInLs ** subInHs)), (n4 ** (subOutLs ** subOutHs))) = 
                         hProjectByLabels {lty=lty} {ts=ts2} lsNew hs
          -- Al final obtengo esa proyeccion, agregando el valor al HList proyectado (y no al que NO se proyecto)
              rLeft =  (S n3 ** ((l2,t) :: subInLs ** (::) {lbl=l2} val subInHs))
              rRight = (n4 ** (subOutLs ** subOutHs)) 
          in (rLeft, rRight)
        No _ => 
          -- No pertenece, entonces solamente se realiza la proyeccion sobre el resto del HList, y se agrega el valor
          -- actual a la lista de los que NO estan en la proyeccion
          let ((n3 ** (subInLs ** subInHs)), (n4 ** (subOutLs ** subOutHs))) = 
                         hProjectByLabels {lty=lty} {ts=ts2} ls hs
              rLeft =  (n3 ** (subInLs ** subInHs))
              rRight = (S n4 ** ((l2,t) :: subOutLs ** (::) {lbl=l2} val subOutHs))      
          in (rLeft, rRight)
      
    -- Parece que un ejemplo como este no puede funcionar, porque hProjectByLabels devuelve tipos existenciales.
    -- Nunca hace ninguna computacion con los tipos, entonces no puede saber cuales son los HList resultantes
    {-hProjectByLabelsExample : (HList3 [("Edad", Nat)], HList3 [("Nombre", String)])                
    hProjectByLabelsExample =
      let iniHs = the (HList3 [("Edad", Nat), ("Nombre", String)]) $ [23, "Gonzalo"]
          ((n1 ** (ts1 ** inHs)), (n2 ** (ts2 ** outHs))) = hProjectByLabels ["Edad"] iniHs
      in
          (inHs, outHs) -}
          
    -- Ejemplo de hProjectByLabels
    hProjectByLabelsExample2 :  
      ((q1 : Nat ** (ls1 : Vect q1 (String, Type) ** HList3 ls1)),
      (q2 : Nat ** (ls2 : Vect q2 (String, Type) ** HList3 ls2)) )            
    hProjectByLabelsExample2 =
      let iniHs = the (HList3 [("Edad", Nat), ("Nombre", String)]) $ [23, "Gonzalo"]
          ((n1 ** (ts1 ** inHs)), (n2 ** (ts2 ** outHs))) = hProjectByLabels ["Edad"] iniHs
      in
          ((n1 ** (ts1 ** inHs)), (n2 ** (ts2 ** outHs)))
              
    -- NOTA: Este es un hProjectByLabels que usa, y devuelve, pruebas de HLabelSet_6. Estas pruebas son necesarias para
    -- implementar operaciones que devuelven records, como hDeleteAtLabel                
    -- No se pudo implementar (ver comentarios TODO dentro de la funcion por mas informacion)
    {-hProjectByLabels : DecEq lty => {ts : Vect n (lty, Type)} -> Vect k lty -> HList3 ts -> HLabelSet_6 (labelsOf ts) ->    
      ((q1 : Nat ** (ls1 : Vect q1 (lty, Type) ** (HList3 ls1, HLabelSet_6 (labelsOf ls1)))),
      (q2 : Nat ** (ls2 : Vect q2 (lty, Type) ** (HList3 ls2, HLabelSet_6 (labelsOf ls2)))) )
    hProjectByLabels [] _ _ = ((0 ** ([] ** ([], HLabelSet6Nil))), (0 ** ([] ** ([], HLabelSet6Nil))))
    hProjectByLabels _ [] _ = ((0 ** ([] ** ([], HLabelSet6Nil))), (0 ** ([] ** ([], HLabelSet6Nil))))
    hProjectByLabels {lty=lty} ls ((::) {lbl=l2} {t=t} {ts=ts2} val hs) isLabelSet = 
      -- Primero debo fijarme si el label del primer elemento del HList pertenece a la lista de labels a proyectar
      case (isElem l2 ls) of
        Yes l2inls => 
          -- Si pertenece, obtengo la lista de labels a proyectar SIN ese label
          let (modLs ** modL2inls) = getProof $ convertLengthElem l2inls
              lsNew = deleteElem modLs modL2inls
          -- Luego realizo la proyeccion de esa nueva lista sobre el resto del HList
              ((n3 ** (subInLs ** (subInHs, isLabelSetInHs))), (n4 ** (subOutLs ** (subOutHs, isLabelSetOutHs)))) = 
                         hProjectByLabels {lty=lty} {ts=ts2} lsNew hs isLabelSet
          -- Al final obtengo esa proyeccion, agregando el valor al HList proyectado (y no al que NO se proyecto)
              test1 = getRecLabelSet_6 isLabelSet
              test2 = getNotMember_6 isLabelSet
              -- TODO: Hay que ver como encontrar una prueba de "Not (HMember_6 val subInHs)". Sin esa prueba no puedo construir la
              -- prueba para retornar
              rLeft =  (S n3 ** ((l2,t) :: subInLs ** ((::) {lbl=l2} val subInHs, isLabelSet)))
              rRight = (n4 ** (subOutLs ** (subOutHs, isLabelSetOutHs))) 
          --in (rLeft, rRight)
          in ?wat1
        No _ => 
          -- No pertenece, entonces solamente se realiza la proyeccion sobre el resto del HList, y se agrega el valor
          -- actual a la lista de los que NO estan en la proyeccion
          let ((n3 ** (subInLs ** (subInHs, isLabelSetInHs))), (n4 ** (subOutLs ** (subOutHs, isLabelSetOutHs)))) = 
                         hProjectByLabels {lty=lty} {ts=ts2} ls hs isLabelSet
              -- TODO: Idem que arriba. Necesito encontrar una prueba de "Not (HMember_6 val subOutHs)"
              rLeft =  (n3 ** (subInLs ** (subInHs, isLabelSetInHs)))
              rRight = (S n4 ** ((l2,t) :: subOutLs ** (::) {lbl=l2} val subOutHs))      
          --in (rLeft, rRight)
          in ?wat2-}        
          
          
    -- Definicion de "delete" de hackage
    -- NOTA: Esta incompleta porque no se pudo implementar un hProjectByLabels que devolviera un HLabelSet_6
    {-hDeleteByLabels : DecEq lty => {ts1 : Vect n1 (lty, Type)} -> Record_3 ts1 -> lty -> 
      (n2 : Nat ** (ts2 : Vect n2 (lty, Type) ** Record_3 ts2 ))
    hDeleteByLabels (MkRecord3 isLabelSet hs) lbl =
      let (_, (n2 ** (ts2 ** (hs2, isLabelSet2)))) = hProjectByLabels [lbl] hs isLabelSet
      in (n2 ** (ts2 **  MkRecord3 isLabelSet2 hs2)) -}
                  
                  
  -- #2 - Igual que HList3 pero con List en vez de Vect
  namespace HList4
    -- Con este tipo se pueden tener los labels a nivel de tipos y no en runtime
    data HList4 : List (lty, Type) -> Type where
      Nil : HList4 []
      (::) : {lbl : lty} -> (val : t) -> HList4 ts -> HList4 ((lbl,t) :: ts)
 
    -- Obtiene los labels de una lista de tal HList
    labelsOf : List (lty, Type) -> List lty
    labelsOf = map fst
    
    -- Asi se puede definir un nuevo record similar al de HList en hackage
    data Record_4 : List (lty, Type) -> Type where
      MkRecord4 : HLabelSet_7 (labelsOf ts) -> HList4 ts -> Record_4 ts
    
    -- Misma hProjectByLabels definida anteriormente, pero para "List" en vez de "Vect"
    -- NOTA: Por ahora no se usa porque se pudo implementar mas arriba con Vect. Pero esto muestra que con "List" se pueden implementar
    -- records igual.           
    hProjectByLabels: DecEq lty => {ts : List (lty, Type)} -> List lty -> HList4 ts -> 
      ((res1 : List (lty, Type) ** HList4 res1), (res2 : List (lty, Type) ** HList4 res2))
    hProjectByLabels [] _ = (([] ** []),([] ** []))
    hProjectByLabels _ [] = (([] ** []),([] ** [])) 
    hProjectByLabels {lty=lty} ls ((::) {lbl=l2} {t=t} {ts=ts2} val hs) =       
       -- Primero debo fijarme si el label del primer elemento del HList pertenece a la lista de labels a proyectar
      case (elem (wrapEq l2) (map wrapEq ls)) of
         True =>
           -- Si pertenece, obtengo la lista de labels a proyectar SIN ese label
           let lsNew = (map unWrapEq) $ delete (wrapEq l2) (map wrapEq ls)
           -- Luego realizo la proyeccion de esa nueva lista sobre el resto del HList
               ((subInLs ** subInHs), (subOutLs ** subOutHs)) = 
                         hProjectByLabels {lty=lty} {ts=ts2} lsNew hs
           -- Al final obtengo esa proyeccion, agregando el valor al HList proyectado (y no al que NO se proyecto)
           in (((l2,t) :: subInLs ** val :: subInHs), (subOutLs ** subOutHs))
         False => 
           -- No pertenece, entonces solamente se realiza la proyeccion sobre el resto del HList, y se agrega el valor
           -- actual a la lista de los que NO estan en la proyeccion
           let ((subInLs ** subInHs), (subOutLs ** subOutHs)) = 
                         hProjectByLabels {lty=lty} {ts=ts2} ls hs
           in ((subInLs ** subInHs), ((l2,t) :: subOutLs ** val :: subOutHs))
