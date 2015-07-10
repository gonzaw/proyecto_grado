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
  -- No pude implementar hSplit, hSplitByHNats ni hProjectByHNats facilmente
  -- TODO: Queda para despues ver como implementarlas y entenderlas
  -- TODO: Implementar HSplit
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

  -- Definicion textual
  data Label : Nat -> ns -> Type where
    MkLabel : (n : Nat) -> ns -> String -> Label n ns

  firstLabel : ns -> String -> Label 0 ns
  firstLabel = MkLabel 0
  
  nextLabel : {n : Nat} -> Label n ns -> String -> Label (S n) ns
  nextLabel (MkLabel n a _) = MkLabel (S n) a
  
  -- No compila  
  --class HZip x y l | x y -> l, l -> x y where
  --  hZip : x -> y -> l
  --  hUnzip : l -> (x, y)

  --hZip : Vect n ty1 -> Vect n ty2 -> Vect n (ty1,ty2)
  --hUnzip : Vect n (ty1,ty2) -> Vect n ty1 -> Vect n ty2
  --TODO: Hacer lo mismo para HList
  
  
  -- Funciones que ayudan a obtener pruebas automaticas
  getNo : (res : Dec p) -> case res of { Yes _ => () ; No _ => Not p }
  getNo (Yes prf) = ()
  getNo (No contra) = contra

  getYes : (res : Dec p) -> case res of { Yes _ => p ; No _ => () }
  getYes (Yes prf) = prf
  getYes (No contra) = ()

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
    
  -- Esta es la definicion mas literal basada en HList, que necesita HEq
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

  -- testHLabelSet 2 y 3 ejecutan bien, pero el predicado es incorrecto
  -- testHLabelSet 1 y 4 no pueden generar la prueba, pero el predicado es correcto
  -- testHLabelSet 5 es correcto (me parece) pero tampoco puede generar la prueba de forma automatica con "search"
  -- NOTA: Usar testHLabelSet_5 con naturales, que tienen definido "HEq" mas arriba
  -- NOTA: HLabelSet_2 y HLabelSet_3 estan mal porque permiten definir predicados mal, como HLabelSet_3 [1,2,1]

  -- Algo interesante de HMember_5, es que funciona. Aca hay ejemplos que hace typechecking:
  -- the (HMember_5 "1" ["2","1","2"] True) $ HMember5InThere HMember5InHere
  -- the (HMember_5 "1" ["2","2"] False) $ HMember5InThere $ HMember5InThere HMember5Nil

  -- Definicion hibrida de record entre la de HList y la que hice anteriormente
  -- Como no pude definir HZip, creo los 2 tipos distintos de Records que indica HList
  
  -- Primera definicion de HList, donde se tiene una lista heterogenea de pares "Label"/"Tipo"
  data Record_1 : Vect n (lty, Type) -> Type where
    MkRecord1 : HLabelSet_6 ls -> HList ts -> Record_1 (zip ls ts)
    
  -- Segunda definicion de HList, donde se tienen 2 listas heterogeneas separadas para labels, y otra para los tipos  
  data Record_2 : Vect n lty -> Vect n Type -> Type where
    MkRecord2 : HLabelSet_6 ls -> HList ts -> Record_2 ls ts
  
  --mkRecord no obtiene la prueba automatica de HLabelSet_6 ls usando el getYes
  {-mkRecord1 : DecEq lty => {ls : Vect n lty} -> HList ts -> Record_1 (zip ls ts)
  mkRecord1 {ls=ls} hs = MkRecord1 prf hs
    where
        prf : HLabelSet_6 ls
        prf = getYes (isLabelSet_6 ls) -}
        
  mkRecord_1 : DecEq lty => {ls : Vect n lty} -> {prf : HLabelSet_6 ls} -> HList ts -> Record_1 (zip ls ts)
  mkRecord_1 {prf=prf} hs = MkRecord1 prf hs
  
  -- Tampoco se puede utilizar getYes en emptyRecord porque, como no se sabe lty todavia, getYes no puede realizar la
  -- computacion que genera la prueba. Hay que ver como hacerlo bien
  {-emptyRecord_1 : DecEq lty => Record_1 []
  emptyRecord_1 {lty=lty} = MkRecord1 prf {ls=[]} []
    where
      prf = getYes (isLabelSet_6 {lty=lty} []) -}
      
  mkRecord_2 : DecEq lty => {ls : Vect n lty} -> {prf : HLabelSet_6 ls} -> HList ts -> Record_2 ls ts
  mkRecord_2 {prf=prf} hs = MkRecord2 prf hs
  
  --Idem que emptyRecord_1
  {-emptyRecord_2 : DecEq lty => Record_2 [] []
  emptyRecord_2 {lty=lty} = MkRecord2 prf {ls=[]} []
    where
      prf = getYes (isLabelSet_6 {lty=lty} [])-}
        
  {-
  
  --PENDIENTE DE DEFINIR
  Access operations:
    -- Deletion
    (Record r) .-. l = Record r’
    where (ls,vs) = hUnzip r
    n       = hFind l ls -- uses HEq on labels
    ls’     = hDeleteAtHNat n ls
    vs’     = hDeleteAtHNat n vs
    r’      = hZip ls’ vs’-}
