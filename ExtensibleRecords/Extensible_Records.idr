{-
  Definición de Records Extensibles.
  
  Se toma inspiración en HList de Haskell
  Paper: http://okmij.org/ftp/Haskell/HList-ext.pdf
  Hackage: https://hackage.haskell.org/package/HList
-}
module Extensible_Records

import Data.Vect
import Data.Fin

%default total

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

-- PRedicado de que un vector no tiene repetidos
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
   
-- ** HList **
data HList3 : Vect n (lty, Type) -> Type where
  Nil : HList3 []
  (::) : {lbl : lty} -> (val : t) -> HList3 ts -> HList3 ((lbl,t):: ts)
 
-- Obtiene los labels de una lista de tal HList
labelsOf : Vect n (lty, Type) -> Vect n lty
labelsOf = map fst

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


