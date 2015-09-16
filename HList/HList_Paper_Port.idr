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

  -- Nota: HLabelSet_6 puede utilizar Elem directamente
  data HLabelSet_6 : Vect n lty -> Type where
    HLabelSet6Nil : HLabelSet_6 []
    HLabelSet6Cons : Not (Elem lbl ls) -> HLabelSet_6 ls -> HLabelSet_6 (lbl :: ls)
    
  -- Funciones auxiliares
  getNotMember_6 : HLabelSet_6 (lbl :: ls) -> Not (Elem lbl ls)
  getNotMember_6 (HLabelSet6Cons notMember _) = notMember
  
  getRecLabelSet_6 : HLabelSet_6 (lbl :: ls) -> HLabelSet_6 ls
  getRecLabelSet_6 (HLabelSet6Cons _ recLabelSet) = recLabelSet

  ifNotLabelSetHereThenNeitherThere_6 : Not (HLabelSet_6 ls) -> Not (HLabelSet_6 (l :: ls))
  ifNotLabelSetHereThenNeitherThere_6 lsnotls (HLabelSet6Cons lnotm lsyesls) = lsnotls lsyesls  
  
  ifHasRepeatedThenNotLabelSet_6 : HLabelSet_6 ls -> Elem l ls -> Not (HLabelSet_6 (l :: ls))      
  ifHasRepeatedThenNotLabelSet_6 lsyesls linls (HLabelSet6Cons lninls lsyesls_2) = lninls linls
  
  -- Esta es la funcion de decision que determina si una lista de labels tiene repetidos o no    
  isLabelSet_6 : DecEq lty => (ls : Vect n lty) -> Dec (HLabelSet_6 ls)
  isLabelSet_6 [] = Yes HLabelSet6Nil
  isLabelSet_6 (l :: ls) with (isLabelSet_6 ls)
    isLabelSet_6 (l :: ls) | No lsnotls = No $ ifNotLabelSetHereThenNeitherThere_6 lsnotls
    isLabelSet_6 (l :: ls) | Yes lsyesls with (isElem l ls)
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


  -- Definicion de HLabelSet que utiliza Eq
  data HMember_8 : Eq lty => lty -> Vect n lty -> Bool -> Type where
    HMember8Nil : Eq lty => HMember_8 {lty=lty} lbl [] False
    HMember8InThere : Eq lty => HMember_8 {lty=lty} lbl1 ls b -> HMember_8 lbl1 (lbl2 :: ls) ((lbl1 == lbl2) || b)
    
  {-data HMember_8 : Eq lty => lty -> Vect n lty -> Bool -> Type where
    HMember8Nil : Eq lty => HMember_8 {lty=lty} lbl [] False
    HMember8Equal : Eq lty => HMember_8 {lty=lty} lbl1 (lbl1 :: ls) True
    HMember8NotEqual : Eq lty => HMember_8 {lty=lty} lbl1 ls b -> ((lbl1 == lbl2) = False) 
                     -> HMember_8 {lty=lty} lbl1 (lbl2 :: ls) b -}
    
  data HLabelSet_8 : Eq lty => Vect n lty -> Type where
    HLabelSet8Nil : Eq lty => HLabelSet_8 {lty=lty} []
    HLabelSet8Cons : Eq lty => HMember_8 {lty=lty} lbl ls False -> HLabelSet_8 ls -> HLabelSet_8 (lbl :: ls)

  -- NOTA: Testeando las pruebas
  --testHMember8 : HMember_8 1 [1] True
  --testHMember8 = HMember8Equal
  
  -- Error: Tira problema de unificacion de 0 con 1
  findHMember : (n : Nat) -> List (TTName, Binder TT) -> TT -> Tactic
  findHMember Z ctxt goal = Refine "HMember8Nil" `Seq` Solve
  findHMember (S n) ctxt goal = GoalType "HMember_8" (Try (Refine "HMember8Nil" `Seq` Solve) 
    (Refine "HMember8InThere" `Seq` (Solve `Seq` findHMember n ctxt goal)))
 
  fun : Eq lty => (lbl : lty) -> (ls : Vect n lty) -> (b : Bool ** HMember_8 lbl ls b)
  fun lbl1 [] = (False ** HMember8Nil)
  fun lbl1 (lbl2 :: ls) = 
    let (b ** prfRec) = fun lbl1 ls
    in (((lbl1 == lbl2) || b) ** (HMember8InThere prfRec))  
    
  -- No deberia de compilar, pero lo hace
  {-fun2 : Eq lty => (ls : Vect n lty) -> HLabelSet_8 ls 
  fun2 [] = HLabelSet8Nil
  fun2 (l :: ls) = 
      let prfRec = fun2 ls
          (False ** isMember) = fun l ls
      in HLabelSet8Cons isMember prfRec-}
      
  -- Error: Tira error de unificacion de lbl1 == lbl2 \\ b con True|False 
  {-notBothHMember : Eq lty => (ls : Vect n lty) -> (lbl : lty) -> HMember_8 lbl ls True -> HMember_8 lbl ls False -> Void  
  notBothHMember {n=S k} ls lbl (HMember8InThere subHm1) (HMember8InThere subHm2)  = ?notBothHMember_rhs 
  
  voidPrf : Eq lty => (ls : Vect n lty) -> (lbl : lty) -> HMember_8 lbl ls True -> HLabelSet_8 (lbl :: ls) -> Void
  voidPrf ls lbl isMember (HLabelSet8Cons recMember recLabelSet) = notBothHMember ls lbl isMember recMember -}
   
  testHMember8_5 : HMember_8 1 [1] True
  testHMember8_5 = getProof $ fun 1 [1]
  
  testHMember8_2 : {default tactics { search } prf : HMember_8 1 [1] True} -> HMember_8 1 [1] True
  testHMember8_2 {prf=prf} = prf
  
  {-testHMember8_3 : HMember_8 1 [1] True
  testHMember8_3 = ?testHMember_prf_1
  
  testHMember8_4 : HMember_8 1 [2] False
  testHMember8_4 = ?testHMember_prf_2-}

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
  
  testHLabelSet_8 : Eq lty => (ls : Vect n lty) -> {default tactics { search } prf : HLabelSet_8 ls} -> HLabelSet_8 ls
  testHLabelSet_8 ls {prf=prf} = prf

  -- testHLabelSet 2 y 3 ejecutan bien, pero el predicado es incorrecto
  -- testHLabelSet 1, 4, 6 y 8 no pueden generar la prueba, pero el predicado es correcto
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
       
    emptyRecord_3 : DecEq lty => Record_3 []
    emptyRecord_3 = MkRecord3 HLabelSet6Nil {ts=[]} [] 
        
    mkRecord_3 : DecEq lty => {ts : Vect n (lty, Type)} -> {prf : HLabelSet_6 (labelsOf ts)} -> HList3 ts -> Record_3 ts
    mkRecord_3 {prf=prf} hs = MkRecord3 prf hs
      
    addToRec_3 : DecEq lty => {ts : Vect n (lty, Type)} -> {t : Type} -> 
      (lbl : lty) -> (val : t)->  Record_3 ts -> {notElem : Not (Elem lbl (labelsOf ts))} -> Record_3 ((lbl,t) :: ts)
    addToRec_3 lbl val (MkRecord3 subLabelSet hs) {notElem=notElem} = MkRecord3 (HLabelSet6Cons notElem subLabelSet) (val :: hs)
    
     -- Prueba de generacion de Proof
    
    HLabelSet6OrUnit : DecEq lty => Vect n lty -> Type
    HLabelSet6OrUnit vec =
      case (isLabelSet_6 vec) of
        Yes _ => HLabelSet_6 vec
        No _ => ()
     
    mkHLabelSet6 : DecEq lty => (ls : Vect n lty) -> HLabelSet6OrUnit ls
    mkHLabelSet6 ls with (isLabelSet_6 ls)
      mkHLabelSet6 ls | Yes isLabelSet = isLabelSet
      mkHLabelSet6 ls | No _  = ()
          
    data NotElemLabel : lty -> Vect n lty -> Type where
      MkNotElemLabel : (lbl : lty) -> Not (Elem lbl ls) -> NotElemLabel lbl ls
      
    NotElemLabelOrUnit : DecEq lty => (lbl : lty) -> (ls : Vect n lty) -> Type
    NotElemLabelOrUnit lbl ls =
      case (isElem lbl ls) of
        Yes _ => ()
        No notElem => Not (Elem lbl ls)
        
    mkNotElemLabel : DecEq lty => (lbl : lty) -> (ls : Vect n lty) -> NotElemLabelOrUnit lbl ls
    mkNotElemLabel lbl ls with (isElem lbl ls)
      mkNotElemLabel lbl ls | Yes _ = ()
      mkNotElemLabel lbl ls | No notElem = notElem
        
    --Testing de pruebas automaticas    
    pruebaHLabelSet6 : HLabelSet_6 [1,2,3]
    pruebaHLabelSet6 = mkHLabelSet6 [1,2,3]
    
    pruebaNotElemLabel : Not (Elem 1 [2,3])
    pruebaNotElemLabel = mkNotElemLabel 1 [2,3]   
     
    --Tests creando records usando tales pruebas automaticas       
    pruebaRecord3_1 : Record_3 [("Edad", Nat)]
    pruebaRecord3_1 = addToRec_3 "Edad" 23 (emptyRecord_3 {lty=String}) {notElem=mkNotElemLabel "Edad" []}
    
    pruebaRecord3_2 : Record_3 [("Edad", Nat)]    
    pruebaRecord3_2 = mkRecord_3 [23] {prf=mkHLabelSet6 ["Edad"]}
    
    -- Fin Prueba de generacion de proof
    
    
    
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
           
    -- DeleteElem es el predicado equivalente a la funcion "deleteElem" del Prelude
    data DeleteElem : (xs : Vect (S n) t) -> Elem x xs -> Vect n t -> Type where
      DeleteElemHere : DeleteElem (x :: xs) Here xs
      DeleteElemThere : DeleteElem xs isThere ys -> DeleteElem (x :: xs) (There isThere) (x :: ys)
    
    data IsProjectLeft : DecEq lty => Vect k lty -> Vect n (lty, Type) -> Vect m (lty, Type) -> Type where
      IPL_EmptyLabels : DecEq lty => IsProjectLeft {lty=lty} [] ts []
      IPL_EmptyVect : DecEq lty => IsProjectLeft {lty=lty} ls [] []
      IPL_ProjLabelElem : DecEq lty => (isElem : Elem (fst t) ls) -> DeleteElem ls isElem lsNew ->
                          IsProjectLeft {lty=lty} lsNew ts res1 -> IsProjectLeft ls (t :: ts) (t :: res1)      
      IPL_ProjLabelNotElem : DecEq lty => Not (Elem (fst t) ls) -> IsProjectLeft {lty=lty} ls ts res1 -> 
                           IsProjectLeft ls (t :: ts) res1
    
    data IsProjectRight : DecEq lty => Vect k lty -> Vect n (lty, Type) -> Vect m (lty, Type) -> Type where
      IPR_EmptyLabels : DecEq lty => IsProjectRight {lty=lty} [] ts ts
      IPR_EmptyVect : DecEq lty => IsProjectRight {lty=lty} ls [] []
      IPR_ProjLabelElem : DecEq lty => (isElem : Elem (fst t) ls) -> DeleteElem ls isElem lsNew ->
                          IsProjectRight {lty=lty} lsNew ts res1 -> IsProjectRight ls (t :: ts) res1      
      IPR_ProjLabelNotElem : DecEq lty => Not (Elem (fst t) ls) -> IsProjectRight {lty=lty} ls ts res1 -> 
                           IsProjectRight ls (t :: ts) (t :: res1)
    
    -- Igual que deleteElem, pero devuelve la prueba de DeleteElem tambien
    deleteElem_2 : {x : t} -> (xs : Vect (S n) t) -> (elem : Elem x xs) -> (res : Vect n t ** DeleteElem xs elem res)
    deleteElem_2 (x :: xs) Here = (xs ** DeleteElemHere)
    deleteElem_2 {n=S n} (x :: xs) (There xinthere) = 
      let (subDel ** subPrf) = deleteElem_2 {n=n} xs xinthere
      in (x :: subDel ** DeleteElemThere subPrf)
    deleteElem_2 {n=Z} (x :: xs) (There xinthere) = absurd $ noEmptyElemImplicit xs xinthere
          
    -- hProjectByLabels que tambien devuelve una prueba de que los vectores son actualmente proyecciones izq y der
    -- Este hProjectByLabels retorna ambas listas: La de proyecciones y la resultante      
    hProjectByLabels_both : DecEq lty => {ts : Vect n (lty, Type)} -> (ls : Vect k lty) -> HList3 ts ->     
      ((q1 : Nat ** (ls1 : Vect q1 (lty, Type) ** (HList3 ls1, IsProjectLeft ls ts ls1))),
      (q2 : Nat ** (ls2 : Vect q2 (lty, Type) ** (HList3 ls2, IsProjectRight ls ts ls2))))
    hProjectByLabels_both [] {n=n} {ts=ts} hs = 
                       ((0 ** ([] ** ([], IPL_EmptyLabels))),
                       (n ** (ts ** (hs, IPR_EmptyLabels))))
    hProjectByLabels_both _ [] =
                       ((0 ** ([] ** ([], IPL_EmptyVect))),
                       (0 ** ([] ** ([], IPR_EmptyVect))))
    hProjectByLabels_both {lty=lty} {k=S k2} ls ((::) {lbl=l2} {t=t} {ts=ts2} val hs) = 
      case (isElem l2 ls) of
        Yes l2inls =>
          let 
              (lsNew ** isDelElem) = deleteElem_2 ls l2inls
              ((n3 ** (subInLs ** (subInHs, subPrjLeft))), (n4 ** (subOutLs ** (subOutHs, subPrjRight)))) = 
                         hProjectByLabels_both {lty=lty} {ts=ts2} lsNew hs
              rPrjRight = IPR_ProjLabelElem {t=(l2,t)} {ts=ts2} {res1=subOutLs}  l2inls isDelElem subPrjRight  
              rPrjLeft = IPL_ProjLabelElem {t=(l2,t)} {ts=ts2} {res1=subInLs}  l2inls isDelElem subPrjLeft
              rRight = (n4 ** (subOutLs ** (subOutHs, rPrjRight)))
              rLeft =  (S n3 ** ((l2,t) :: subInLs ** ((::) {lbl=l2} val subInHs, rPrjLeft)))       
          in (rLeft, rRight)
        No l2ninls => 
          let ((n3 ** (subInLs ** (subInHs, subPrjLeft))), (n4 ** (subOutLs ** (subOutHs, subPrjRight))))  = 
              hProjectByLabels_both {lty=lty} {ts=ts2} ls hs
              
              rPrjLeft = IPL_ProjLabelNotElem {t=(l2,t)} {ts=ts2} {res1=subInLs} l2ninls subPrjLeft
              rLeft = (n3 ** (subInLs ** (subInHs, rPrjLeft)))
              rPrjRight = IPR_ProjLabelNotElem {t=(l2,t)} {ts=ts2} {res1=subOutLs} l2ninls subPrjRight
              rRight = (S n4 ** ((l2,t) :: subOutLs ** ((::) {lbl=l2} val subOutHs, rPrjRight)))
          in (rLeft, rRight)
  
    
    -- Dada una prueba que un elemento no pertenece a un Cons de una lista, divide tal prueba en sus dos componentes
    notElemLemma1 : Not (Elem x (y :: xs)) -> (Not (Elem x xs), Not (x = y))
    notElemLemma1 notElemCons = (notElem_prf, notEq_prf)
      where
        notElem_prf isElem = notElemCons $ There isElem
        notEq_prf isEq = notElemCons $ rewrite isEq in Here
    
    -- Dada una prueba que un elemento no pertenece a una lista, y no es igual a otro, se obtiene la prueba de que no pertenece al Cons
    -- Es isomorfo al lemma anterior
    notElemLemma2 : Not (Elem x xs) -> Not (x = y) -> Not (Elem x (y :: xs))
    notElemLemma2 notElem notEq Here = notEq Refl
    notElemLemma2 notElem notEq (There isElem) = notElem isElem 
    
    hProjectByLabelsRightIsLabelSet_Lemma1 : DecEq lty => {ls : Vect n1 lty} -> {ts1 : Vect n2 (lty,Type)} -> {ts2 : Vect n3 (lty,Type)} ->
      IsProjectRight ls ts1 ts2 -> Not (Elem lbl (map fst ts1)) -> Not (Elem lbl (map fst ts2))
    hProjectByLabelsRightIsLabelSet_Lemma1 IPR_EmptyLabels notElem = notElem
    hProjectByLabelsRightIsLabelSet_Lemma1 IPR_EmptyVect notElem = notElem
    hProjectByLabelsRightIsLabelSet_Lemma1 (IPR_ProjLabelElem isElem delLs subPrjRight) notElem = 
      let
        (notElemSub, notEq) = notElemLemma1 notElem
        isNotElemRec = hProjectByLabelsRightIsLabelSet_Lemma1 subPrjRight notElemSub
      in isNotElemRec
    hProjectByLabelsRightIsLabelSet_Lemma1 (IPR_ProjLabelNotElem subNotElem subPrjRight) notElem = 
      let
        (notElemSub, notEq) = notElemLemma1 notElem
        isNotElemRec = hProjectByLabelsRightIsLabelSet_Lemma1 subPrjRight notElemSub
      in notElemLemma2 isNotElemRec notEq
      
    hProjectByLabelsLeftIsLabelSet_Lemma1 : DecEq lty => {ls : Vect n1 lty} -> {ts1 : Vect n2 (lty,Type)} -> {ts2 : Vect n3 (lty,Type)} ->
      IsProjectLeft ls ts1 ts2 -> Not (Elem lbl (map fst ts1)) -> Not (Elem lbl (map fst ts2))
    hProjectByLabelsLeftIsLabelSet_Lemma1 IPL_EmptyLabels notElem = noEmptyElem
    hProjectByLabelsLeftIsLabelSet_Lemma1 IPL_EmptyVect notElem = notElem
    hProjectByLabelsLeftIsLabelSet_Lemma1 (IPL_ProjLabelElem isElem delElem subPrjLeft) notElem = 
      let
        (notElemSub, notEq) = notElemLemma1 notElem
        isNotElemRec = hProjectByLabelsLeftIsLabelSet_Lemma1 subPrjLeft notElemSub
      in notElemLemma2 isNotElemRec notEq  
    hProjectByLabelsLeftIsLabelSet_Lemma1 (IPL_ProjLabelNotElem subNotElem subPrjLeft) notElem =
      let
        (notElemSub, notEq) = notElemLemma1 notElem
        isNotElemRec = hProjectByLabelsLeftIsLabelSet_Lemma1 subPrjLeft notElemSub
      in isNotElemRec
    
    hProjectByLabelsLeftIsLabelSet_Lemma2 : DecEq lty => {ls : Vect n1 lty} -> {ts1 : Vect n2 (lty,Type)} -> {ts2 : Vect n3 (lty,Type)} 
    -> IsProjectLeft ls ts1 ts2 -> HLabelSet_6 (map fst ts1) -> HLabelSet_6 (map fst ts2)
    hProjectByLabelsLeftIsLabelSet_Lemma2 IPL_EmptyLabels isLabelSet = HLabelSet6Nil
    hProjectByLabelsLeftIsLabelSet_Lemma2 IPL_EmptyVect isLabelSet = isLabelSet
    hProjectByLabelsLeftIsLabelSet_Lemma2 (IPL_ProjLabelElem isElem delLs subPrjLeft) (HLabelSet6Cons notMember subLabelSet) = 
      let isLabelSetRec = hProjectByLabelsLeftIsLabelSet_Lemma2 subPrjLeft subLabelSet
          notElemPrf = hProjectByLabelsLeftIsLabelSet_Lemma1 subPrjLeft notMember
      in HLabelSet6Cons notElemPrf isLabelSetRec
    hProjectByLabelsLeftIsLabelSet_Lemma2 (IPL_ProjLabelNotElem notElem subPrjLeft) (HLabelSet6Cons notMember subLabelSet) = 
      let isLabelSetRec = hProjectByLabelsLeftIsLabelSet_Lemma2 subPrjLeft subLabelSet
      in isLabelSetRec
    
    hProjectByLabelsRightIsLabelSet_Lemma2 : DecEq lty => {ls : Vect n1 lty} -> {ts1 : Vect n2 (lty,Type)} -> {ts2 : Vect n3 (lty,Type)} 
    -> IsProjectRight ls ts1 ts2 -> HLabelSet_6 (map fst ts1) -> HLabelSet_6 (map fst ts2)
    hProjectByLabelsRightIsLabelSet_Lemma2 IPR_EmptyLabels isLabelSet = isLabelSet         
    hProjectByLabelsRightIsLabelSet_Lemma2 IPR_EmptyVect isLabelSet = isLabelSet         
    hProjectByLabelsRightIsLabelSet_Lemma2 (IPR_ProjLabelElem isElem delLs subPrjRight) (HLabelSet6Cons notMember subLabelSet) =
      let isLabelSetRec = hProjectByLabelsRightIsLabelSet_Lemma2 subPrjRight subLabelSet
      in isLabelSetRec 
    hProjectByLabelsRightIsLabelSet_Lemma2 (IPR_ProjLabelNotElem notElem subPrjRight) (HLabelSet6Cons notMember subLabelSet) = 
      let isLabelSetRec = hProjectByLabelsRightIsLabelSet_Lemma2 subPrjRight subLabelSet
          notElemPrf = hProjectByLabelsRightIsLabelSet_Lemma1 subPrjRight notMember 
      in HLabelSet6Cons notElemPrf isLabelSetRec
          
    
    -- *-* Definicion de "hProjectByLabels" de hackage *-*
    hProjectByLabels : DecEq lty => {ts1 : Vect n (lty, Type)} -> (ls : Vect k lty) -> Record_3 ts1 ->     
      (q1 : Nat ** (ts2 : Vect q1 (lty, Type) ** (Record_3 ts2, IsProjectLeft ls ts1 ts2)))
    hProjectByLabels ls (MkRecord3 isLabelSet hs) =
      let (qRes ** (lsRes ** (hsRes, prjLeftRes))) = fst $ hProjectByLabels_both ls hs
          isLabelSetRes = hProjectByLabelsLeftIsLabelSet_Lemma2 prjLeftRes isLabelSet
      in (qRes ** (lsRes ** (MkRecord3 isLabelSetRes hsRes, prjLeftRes)))         
          
    -- Predicado que indica que un campo fue eliminado de la lista de un record      
    data DeleteFromRecPred : DecEq lty => lty -> Vect n (lty, Type) -> Vect m (lty, Type) -> Type where
      DFR_EmptyRecord : DecEq lty => {lbl : lty} -> DeleteFromRecPred lbl [] []
      DFR_IsElem : DecEq lty => {lbl : lty} -> DeleteFromRecPred lbl ((lbl,ty) :: ts) ts
      DFR_IsNotElem : DecEq lty => {lbl : lty} -> DeleteFromRecPred lbl ts1 ts2 -> DeleteFromRecPred lbl (tup :: ts1) (tup :: ts2)
          
    -- Transformo una prueba de que se proyecto una lista con un solo elemento a una prueba de que se elimino tal elemento
    fromIsProjectRightToDeleteFromRec : DecEq lty => {ts1 : Vect n (lty, Type)} -> {ts2 : Vect m (lty, Type)} ->
                                      {lbl : lty} -> IsProjectRight [lbl] ts1 ts2 -> DeleteFromRecPred lbl ts1 ts2
    fromIsProjectRightToDeleteFromRec IPR_EmptyVect = DFR_EmptyRecord
    fromIsProjectRightToDeleteFromRec {lbl=lbl} (IPR_ProjLabelElem {t=(lbl,ty)} Here DeleteElemHere IPR_EmptyLabels) = DFR_IsElem
    fromIsProjectRightToDeleteFromRec {lbl=lbl} (IPR_ProjLabelElem {t=(lbl,ty)} Here DeleteElemHere IPR_EmptyVect) = DFR_IsElem
    fromIsProjectRightToDeleteFromRec {lbl=lbl} (IPR_ProjLabelElem {t=(lbl,ty)} Here DeleteElemHere (IPR_ProjLabelNotElem f x)) impossible
    fromIsProjectRightToDeleteFromRec (IPR_ProjLabelNotElem notElem subPrjRight) = 
      let subDelFromRec = fromIsProjectRightToDeleteFromRec subPrjRight
      in DFR_IsNotElem subDelFromRec
    
    
    -- *-* Definicion de "hDeleteAtLabel" de hackage *-*
    hDeleteAtLabel : DecEq lty => {ts1 : Vect n1 (lty, Type)} -> (lbl : lty) -> Record_3 ts1 ->
      (n2 : Nat ** (ts2 : Vect n2 (lty, Type) ** (Record_3 ts2, DeleteFromRecPred lbl ts1 ts2)))
    hDeleteAtLabel lbl (MkRecord3 isLabelSet hs) =
      let 
        (_, (n2 ** (ts2 ** (hs2, prjRightRes)))) = hProjectByLabels_both [lbl] hs
        isLabelSet2 = hProjectByLabelsRightIsLabelSet_Lemma2 prjRightRes isLabelSet
      in (n2 ** (ts2 ** (MkRecord3 isLabelSet2 hs2, fromIsProjectRightToDeleteFromRec prjRightRes)))
