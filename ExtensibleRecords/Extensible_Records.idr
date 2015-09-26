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

-- Predicado que indica que un vector es un conjunto, i.e no tiene elementos repetidos
data IsSet : Vect n t -> Type where
  IsSetNil : IsSet []
  IsSetCons : Not (Elem x xs) -> IsSet xs -> IsSet (x :: xs)
    
-- Dada una prueba que un vector no tiene repetidos, retorna la prueba que su primer elemento no pertenece al resto.    
ifSetThenNotElemFirst : IsSet (x :: xs) -> Not (Elem x xs)
ifSetThenNotElemFirst (IsSetCons notXIsInXs  _) = notXIsInXs
  
-- Dada una prueba que un cons de un vector es un set, retorna la prueba de que el tail es un set.
ifSetThenRestIsSet : IsSet (x :: xs) -> IsSet xs
ifSetThenRestIsSet (IsSetCons _ xsIsSet) = xsIsSet

-- Dada una prueba de que un vector no es un set, retorna una prueba que cualquier cons de tal vector no es un set
ifNotSetHereThenNeitherThere : Not (IsSet xs) -> Not (IsSet (x :: xs))
ifNotSetHereThenNeitherThere notXsIsSet (IsSetCons xIsInXs xsIsSet) = notXsIsSet xsIsSet  
  
-- Dada una prueba de que un valor pertenece a un vector, entonces este elemento agregado al vector no es un set.  
ifIsElemThenConsIsNotSet : Elem x xs -> Not (IsSet (x :: xs))      
ifIsElemThenConsIsNotSet xIsInXs (IsSetCons notXIsInXs xsIsSet) = notXIsInXs xIsInXs
  
-- Funcion de decision que indica si un vector es un set o no
isSet : DecEq t => (xs : Vect n t) -> Dec (IsSet xs)
isSet [] = Yes IsSetNil
isSet (x :: xs) with (isSet xs)
  isSet (x :: xs) | No notXsIsSet = No $ ifNotSetHereThenNeitherThere notXsIsSet
  isSet (x :: xs) | Yes xsIsSet with (isElem x xs)
    isSet (x :: xs) | Yes xsIsSet | No notXInXs = Yes $ IsSetCons notXInXs xsIsSet
    isSet (x :: xs) | Yes xsIsSet | Yes xInXs = No $ ifIsElemThenConsIsNotSet xInXs
   
-- ** Listas heterogeneas con labels **

data HList : Vect n (lty, Type) -> Type where
  Nil : HList []
  (::) : {lbl : lty} -> (val : t) -> HList ts -> HList ((lbl,t):: ts)
 
-- Obtiene los labels de una lista de tal HList
labelsOf : Vect n (lty, Type) -> Vect n lty
labelsOf = map fst

-- *** Records extensibles ***

data Record : Vect n (lty, Type) -> Type where
  MkRecord : IsSet (labelsOf ts) -> HList ts -> Record ts
       
-- Transforma un record en una lista heterogenea
recToHList : Record ts -> HList ts
recToHList (MkRecord _ hs) = hs

-- Dado un record retorna la prueba de que sus labels son un set
recLblIsSet : Record ts -> IsSet (labelsOf ts)
recLblIsSet (MkRecord lsIsSet _ ) = lsIsSet       
       
-- Record vacio       
emptyRecord : DecEq lty => Record []
emptyRecord = MkRecord IsSetNil {ts=[]} [] 
        
-- Dado una lista heterogenea y una prueba de que sus labels son un set, crea un record        
hListToRec : DecEq lty => {ts : Vect n (lty, Type)} -> {prf : IsSet (labelsOf ts)} -> HList ts -> Record ts
hListToRec {prf=prf} hs = MkRecord prf hs

--TODO: Agregar un hListToRec con el RecOrUnit
      
consRec : DecEq lty => {ts : Vect n (lty, Type)} -> {t : Type} -> 
  (lbl : lty) -> (val : t)->  Record ts -> {notElem : Not (Elem lbl (labelsOf ts))} -> Record ((lbl,t) :: ts)
consRec lbl val (MkRecord subLabelSet hs) {notElem=notElem} = MkRecord (IsSetCons notElem subLabelSet) (val :: hs)
    
--TODO: Agregar un consRec con el RecOrUnit    
    
-- * Prueba de generacion de Proof *
--TODO: Modificar con lo nuevo visto

HLabelSet6OrUnit : DecEq lty => Vect n lty -> Type
HLabelSet6OrUnit vec =
  case (isSet vec) of
    Yes _ => IsSet vec
    No _ => ()
     
mkHLabelSet6 : DecEq lty => (ls : Vect n lty) -> HLabelSet6OrUnit ls
mkHLabelSet6 ls with (isSet ls)
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
pruebaHLabelSet6 : IsSet [1,2,3]
pruebaHLabelSet6 = mkHLabelSet6 [1,2,3]
    
pruebaNotElemLabel : Not (Elem 1 [2,3])
pruebaNotElemLabel = mkNotElemLabel 1 [2,3]   
     
--Tests creando records usando tales pruebas automaticas       
pruebaRecord3_1 : Record [("Edad", Nat)]
pruebaRecord3_1 = consRec "Edad" 23 (emptyRecord {lty=String}) {notElem=mkNotElemLabel "Edad" []}
    
pruebaRecord3_2 : Record [("Edad", Nat)]    
pruebaRecord3_2 = hListToRec [23] {prf=mkHLabelSet6 ["Edad"]}
    
-- * Fin Prueba de generacion de proof *
    
    
    
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

-- Predicado que la proyeccion izquierda de un hProjectByLabels es efectivamente tal proyeccion    
data IsProjectLeft : DecEq lty => Vect k lty -> Vect n (lty, Type) -> Vect m (lty, Type) -> Type where
  IPL_EmptyLabels : DecEq lty => IsProjectLeft {lty=lty} [] ts []
  IPL_EmptyVect : DecEq lty => IsProjectLeft {lty=lty} ls [] []
  IPL_ProjLabelElem : DecEq lty => (isElem : Elem (fst t) ls) -> DeleteElem ls isElem lsNew ->
                      IsProjectLeft {lty=lty} lsNew ts res1 -> IsProjectLeft ls (t :: ts) (t :: res1)      
  IPL_ProjLabelNotElem : DecEq lty => Not (Elem (fst t) ls) -> IsProjectLeft {lty=lty} ls ts res1 -> 
                       IsProjectLeft ls (t :: ts) res1

    
-- Predicado que la proyeccion derecha de un hProjectByLabels es efectivamente tal proyeccion    
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
          
-- hProjectByLabels que tambien devuelve una prueba de que los vectores son actualmente proyecciones izq y der para un HList
-- Este hProjectByLabels retorna ambas listas: La de proyecciones y la resultante      
hProjectByLabelsHList : DecEq lty => {ts : Vect n (lty, Type)} -> (ls : Vect k lty) -> HList ts ->     
  ((q1 : Nat ** (ls1 : Vect q1 (lty, Type) ** (HList ls1, IsProjectLeft ls ts ls1))),
  (q2 : Nat ** (ls2 : Vect q2 (lty, Type) ** (HList ls2, IsProjectRight ls ts ls2))))
hProjectByLabelsHList [] {n=n} {ts=ts} hs = 
                   ((0 ** ([] ** ([], IPL_EmptyLabels))),
                   (n ** (ts ** (hs, IPR_EmptyLabels))))
hProjectByLabelsHList _ [] =
                   ((0 ** ([] ** ([], IPL_EmptyVect))),
                   (0 ** ([] ** ([], IPR_EmptyVect))))
hProjectByLabelsHList {lty=lty} {k=S k2} ls ((::) {lbl=l2} {t=t} {ts=ts2} val hs) = 
  case (isElem l2 ls) of
    Yes l2inls =>
      let 
          (lsNew ** isDelElem) = deleteElem_2 ls l2inls
          ((n3 ** (subInLs ** (subInHs, subPrjLeft))), (n4 ** (subOutLs ** (subOutHs, subPrjRight)))) = 
                     hProjectByLabelsHList {lty=lty} {ts=ts2} lsNew hs
          rPrjRight = IPR_ProjLabelElem {t=(l2,t)} {ts=ts2} {res1=subOutLs}  l2inls isDelElem subPrjRight  
          rPrjLeft = IPL_ProjLabelElem {t=(l2,t)} {ts=ts2} {res1=subInLs}  l2inls isDelElem subPrjLeft
          rRight = (n4 ** (subOutLs ** (subOutHs, rPrjRight)))
          rLeft =  (S n3 ** ((l2,t) :: subInLs ** ((::) {lbl=l2} val subInHs, rPrjLeft)))       
      in (rLeft, rRight)
    No l2ninls => 
      let ((n3 ** (subInLs ** (subInHs, subPrjLeft))), (n4 ** (subOutLs ** (subOutHs, subPrjRight))))  = 
          hProjectByLabelsHList {lty=lty} {ts=ts2} ls hs
              
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
    
-- Prueba de que una proyeccion por la derecha, si un label no pertenece al vector inicial, entonces tampoco pertenece al resultante    
hProjectByLabelsRightIsSet_Lemma1 : DecEq lty => {ls : Vect n1 lty} -> {ts1 : Vect n2 (lty,Type)} -> {ts2 : Vect n3 (lty,Type)} ->
  IsProjectRight ls ts1 ts2 -> Not (Elem lbl (map fst ts1)) -> Not (Elem lbl (map fst ts2))
hProjectByLabelsRightIsSet_Lemma1 IPR_EmptyLabels notElem = notElem
hProjectByLabelsRightIsSet_Lemma1 IPR_EmptyVect notElem = notElem
hProjectByLabelsRightIsSet_Lemma1 (IPR_ProjLabelElem isElem delLs subPrjRight) notElem = 
  let
    (notElemSub, notEq) = notElemLemma1 notElem
    isNotElemRec = hProjectByLabelsRightIsSet_Lemma1 subPrjRight notElemSub
  in isNotElemRec
hProjectByLabelsRightIsSet_Lemma1 (IPR_ProjLabelNotElem subNotElem subPrjRight) notElem = 
  let
    (notElemSub, notEq) = notElemLemma1 notElem
    isNotElemRec = hProjectByLabelsRightIsSet_Lemma1 subPrjRight notElemSub
  in notElemLemma2 isNotElemRec notEq

-- Dada una proyeccion por la izquierda, si un label no pertenece al vector inicial, tampoco pertenece al resultante      
hProjectByLabelsLeftIsSet_Lemma1 : DecEq lty => {ls : Vect n1 lty} -> {ts1 : Vect n2 (lty,Type)} -> {ts2 : Vect n3 (lty,Type)} ->
  IsProjectLeft ls ts1 ts2 -> Not (Elem lbl (map fst ts1)) -> Not (Elem lbl (map fst ts2))
hProjectByLabelsLeftIsSet_Lemma1 IPL_EmptyLabels notElem = noEmptyElem
hProjectByLabelsLeftIsSet_Lemma1 IPL_EmptyVect notElem = notElem
hProjectByLabelsLeftIsSet_Lemma1 (IPL_ProjLabelElem isElem delElem subPrjLeft) notElem = 
  let
    (notElemSub, notEq) = notElemLemma1 notElem
    isNotElemRec = hProjectByLabelsLeftIsSet_Lemma1 subPrjLeft notElemSub
  in notElemLemma2 isNotElemRec notEq  
hProjectByLabelsLeftIsSet_Lemma1 (IPL_ProjLabelNotElem subNotElem subPrjLeft) notElem =
  let
    (notElemSub, notEq) = notElemLemma1 notElem
    isNotElemRec = hProjectByLabelsLeftIsSet_Lemma1 subPrjLeft notElemSub
  in isNotElemRec

-- Dada una proyeccion por la derecha, si el vector inicial es un set, el entonces resultante tambien lo es
hProjectByLabelsRightIsSet_Lemma2 : DecEq lty => {ls : Vect n1 lty} -> {ts1 : Vect n2 (lty,Type)} -> {ts2 : Vect n3 (lty,Type)} 
  -> IsProjectRight ls ts1 ts2 -> IsSet (map fst ts1) -> IsSet (map fst ts2)
hProjectByLabelsRightIsSet_Lemma2 IPR_EmptyLabels isLabelSet = isLabelSet         
hProjectByLabelsRightIsSet_Lemma2 IPR_EmptyVect isLabelSet = isLabelSet         
hProjectByLabelsRightIsSet_Lemma2 (IPR_ProjLabelElem isElem delLs subPrjRight) (IsSetCons notMember subLabelSet) =
  let isLabelSetRec = hProjectByLabelsRightIsSet_Lemma2 subPrjRight subLabelSet
  in isLabelSetRec 
hProjectByLabelsRightIsSet_Lemma2 (IPR_ProjLabelNotElem notElem subPrjRight) (IsSetCons notMember subLabelSet) = 
  let isLabelSetRec = hProjectByLabelsRightIsSet_Lemma2 subPrjRight subLabelSet
      notElemPrf = hProjectByLabelsRightIsSet_Lemma1 subPrjRight notMember 
  in IsSetCons notElemPrf isLabelSetRec

-- Dada una proyeccion por la izquierda, si el vector inicial es un set, entonces el resultante tambien lo es    
hProjectByLabelsLeftIsSet_Lemma2 : DecEq lty => {ls : Vect n1 lty} -> {ts1 : Vect n2 (lty,Type)} -> {ts2 : Vect n3 (lty,Type)} 
  -> IsProjectLeft ls ts1 ts2 -> IsSet (map fst ts1) -> IsSet (map fst ts2)
hProjectByLabelsLeftIsSet_Lemma2 IPL_EmptyLabels isLabelSet = IsSetNil
hProjectByLabelsLeftIsSet_Lemma2 IPL_EmptyVect isLabelSet = isLabelSet
hProjectByLabelsLeftIsSet_Lemma2 (IPL_ProjLabelElem isElem delLs subPrjLeft) (IsSetCons notMember subLabelSet) = 
  let isLabelSetRec = hProjectByLabelsLeftIsSet_Lemma2 subPrjLeft subLabelSet
      notElemPrf = hProjectByLabelsLeftIsSet_Lemma1 subPrjLeft notMember
  in IsSetCons notElemPrf isLabelSetRec
hProjectByLabelsLeftIsSet_Lemma2 (IPL_ProjLabelNotElem notElem subPrjLeft) (IsSetCons notMember subLabelSet) = 
  let isLabelSetRec = hProjectByLabelsLeftIsSet_Lemma2 subPrjLeft subLabelSet
  in isLabelSetRec 
    
-- *-* Definicion de "hProjectByLabels" de hackage *-*
hProjectByLabels : DecEq lty => {ts1 : Vect n (lty, Type)} -> (ls : Vect k lty) -> Record ts1 ->     
  (q1 : Nat ** (ts2 : Vect q1 (lty, Type) ** (Record ts2, IsProjectLeft ls ts1 ts2)))
hProjectByLabels ls rec =
  let 
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
    (qRes ** (lsRes ** (hsRes, prjLeftRes))) = fst $ hProjectByLabelsHList ls hs
    isLabelSetRes = hProjectByLabelsLeftIsSet_Lemma2 prjLeftRes isLabelSet
  in (qRes ** (lsRes ** (hListToRec {prf=isLabelSetRes} hsRes, prjLeftRes))) 
  
  
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
hDeleteAtLabel : DecEq lty => {ts1 : Vect n1 (lty, Type)} -> (lbl : lty) -> Record ts1 ->
  (n2 : Nat ** (ts2 : Vect n2 (lty, Type) ** (Record ts2, DeleteFromRecPred lbl ts1 ts2)))
hDeleteAtLabel lbl rec =
  let 
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
    (_, (n2 ** (ts2 ** (hs2, prjRightRes)))) = hProjectByLabelsHList [lbl] hs
    isLabelSet2 = hProjectByLabelsRightIsSet_Lemma2 prjRightRes isLabelSet
  in (n2 ** (ts2 ** (hListToRec {prf=isLabelSet2} hs2, fromIsProjectRightToDeleteFromRec prjRightRes)))
