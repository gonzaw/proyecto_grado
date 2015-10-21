{-

  Definición de Records Extensibles.
  
  Se toma inspiración en HList de Haskell
  Paper: http://okmij.org/ftp/Haskell/HList-ext.pdf
  Hackage: https://hackage.haskell.org/package/HList
  
-}

module Extensible_Records

import Data.List

%default total

-- Nada puede pertenecer a una lista vacia
noEmptyElem : Elem x [] -> Void
noEmptyElem Here impossible

-- Predicado que indica que una lista es un conjunto, i.e no tiene elementos repetidos
data IsSet : List t -> Type where
  IsSetNil : IsSet []
  IsSetCons : Not (Elem x xs) -> IsSet xs -> IsSet (x :: xs)
    
-- Dada una prueba que una lista no tiene repetidos, retorna la prueba que su primer elemento no pertenece al resto.    
ifSetThenNotElemFirst : IsSet (x :: xs) -> Not (Elem x xs)
ifSetThenNotElemFirst (IsSetCons notXIsInXs  _) = notXIsInXs
  
-- Dada una prueba que un cons de una lista es un set, retorna la prueba de que el tail es un set.
ifSetThenRestIsSet : IsSet (x :: xs) -> IsSet xs
ifSetThenRestIsSet (IsSetCons _ xsIsSet) = xsIsSet

-- Dada una prueba de que una lista no es un set, retorna una prueba que cualquier cons de tal lista no es un set
ifNotSetHereThenNeitherThere : Not (IsSet xs) -> Not (IsSet (x :: xs))
ifNotSetHereThenNeitherThere notXsIsSet (IsSetCons xIsInXs xsIsSet) = notXsIsSet xsIsSet  
  
-- Dada una prueba de que un valor pertenece a una lista, entonces este elemento agregado a la lista no es un set.  
ifIsElemThenConsIsNotSet : Elem x xs -> Not (IsSet (x :: xs))      
ifIsElemThenConsIsNotSet xIsInXs (IsSetCons notXIsInXs xsIsSet) = notXIsInXs xIsInXs
  
-- Funcion de decision que indica si una lista es un set o no
isSet : DecEq t => (xs : List t) -> Dec (IsSet xs)
isSet [] = Yes IsSetNil
isSet (x :: xs) with (isSet xs)
  isSet (x :: xs) | No notXsIsSet = No $ ifNotSetHereThenNeitherThere notXsIsSet
  isSet (x :: xs) | Yes xsIsSet with (isElem x xs)
    isSet (x :: xs) | Yes xsIsSet | No notXInXs = Yes $ IsSetCons notXInXs xsIsSet
    isSet (x :: xs) | Yes xsIsSet | Yes xInXs = No $ ifIsElemThenConsIsNotSet xInXs
   
   
-- ** Listas heterogeneas con labels **

-- Vector de listas y tipos
LabelList : Type -> Type
LabelList lty = List (lty, Type)

data HList : LabelList lty -> Type where
  Nil : HList []
  (::) : {lbl : lty} -> (val : t) -> HList ts -> HList ((lbl,t) :: ts)
 
 
-- Obtiene los labels de una lista de tal HList
labelsOf : LabelList lty -> List lty
labelsOf = map fst

-- Alternativa de IsSet, para listas de labels+tipos
IsLabelSet : LabelList lty -> Type
IsLabelSet ts = IsSet (labelsOf ts)  

-- Alternativa de "isSet", para listas de labels+tipos
isLabelSet : DecEq lty => (ts : LabelList lty) -> Dec (IsLabelSet ts)
isLabelSet ts = isSet (labelsOf ts)

-- Predicado que indica que un label pertenece a un vector de labels+tipos
ElemLabel : lty -> LabelList lty -> Type
ElemLabel lbl ts = Elem lbl (labelsOf ts)

-- Nota: Utilizar "Dec (ElemLabel lbl ts)" no typechequea por algún motivo
isElemLabel : DecEq lty => (lbl : lty) -> (ts : LabelList lty) -> Dec (Elem lbl (labelsOf ts))
isElemLabel lbl ts = isElem lbl (labelsOf ts)

-- *** Records extensibles ***

data Record : LabelList lty -> Type where
  MkRecord : IsLabelSet ts -> HList ts -> Record ts
       
-- Transforma un record en una lista heterogenea
-- Es "unlabeled" en HList de Haskell
recToHList : Record ts -> HList ts
recToHList (MkRecord _ hs) = hs

-- Dado un record retorna la prueba de que sus labels son un set
recLblIsSet : Record ts -> IsLabelSet ts
recLblIsSet (MkRecord lsIsSet _ ) = lsIsSet       
       
-- Record vacio       
emptyRec : Record []
emptyRec = MkRecord IsSetNil {ts=[]} [] 
        
-- Dado una lista heterogenea y una prueba de que sus labels son un set, crea un record        
-- Es "hListRecord" en HList de Haskell
hListToRec : DecEq lty => {ts : LabelList lty} -> {prf : IsLabelSet ts} -> HList ts -> Record ts
hListToRec {prf=prf} hs = MkRecord prf hs

-- Dado un record, un label y un valor, extiende el record con ese valor.   
-- Es "HExtend" en HList de Haskell   
consRec : DecEq lty => {ts : LabelList lty} -> {t : Type} -> 
  (lbl : lty) -> (val : t)->  Record ts -> {notElem : Not (ElemLabel lbl ts)} -> Record ((lbl,t) :: ts)
consRec lbl val (MkRecord subLabelSet hs) {notElem=notElem} = MkRecord (IsSetCons notElem subLabelSet) (val :: hs)

-- Tipo que representa un Record o () (i.e una falla)    
RecordOrUnit : DecEq lty => (ts : LabelList lty) -> Type
RecordOrUnit ts with (isLabelSet ts)
  RecordOrUnit ts | Yes _ = Record ts
  RecordOrUnit ts | No _ = ()
 
-- Dada una prueba de que labels no son un conjunto, retorna ()
mkRecordOrUnitFromUnit : DecEq lty => (ts : LabelList lty) -> Not (IsLabelSet ts) -> RecordOrUnit ts
mkRecordOrUnitFromUnit ts notTsIsSet with (isLabelSet ts)
  mkRecordOrUnitFromUnit ts notTsIsSet | Yes tsIsSet = absurd $ notTsIsSet tsIsSet 
  mkRecordOrUnitFromUnit ts notTsIsSet | No _ = ()

-- Dada una prueba de que labels son un conjunto, y un record, retorna ese record  
mkRecordOrUnitFromRecord : DecEq lty => (ts : LabelList lty) -> Record ts -> IsLabelSet ts -> RecordOrUnit ts
mkRecordOrUnitFromRecord ts rec tsIsSet with (isLabelSet ts)
  mkRecordOrUnitFromRecord ts rec tsIsSet | Yes _ = rec
  mkRecordOrUnitFromRecord ts rec tsIsSet | No notTsIsSet = absurd $ notTsIsSet tsIsSet
 
-- "consRec" donde la prueba de labels no repetidos es calculada automaticamente  
consRecAuto : DecEq lty => {ts : LabelList lty} -> {t : Type} -> (lbl : lty) -> (val : t) -> Record ts -> 
  RecordOrUnit ((lbl,t) :: ts)
consRecAuto {ts=ts} {t=t} lbl val (MkRecord subLabelSet hs) with (isElemLabel lbl ts)
  consRecAuto {ts=ts} {t=t} lbl val (MkRecord subLabelSet hs) | Yes lblIsInTs = 
    let notIsSet = ifIsElemThenConsIsNotSet lblIsInTs
    in mkRecordOrUnitFromUnit ((lbl,t) :: ts) notIsSet
  consRecAuto {ts=ts} {t=t} lbl val (MkRecord subLabelSet hs) | No notLblIsInTs =
    let isSet = IsSetCons notLblIsInTs subLabelSet
    in mkRecordOrUnitFromRecord ((lbl,t) :: ts) (MkRecord isSet (val :: hs)) isSet
  
-- "hListToRecAuto" donde la prueba de labels no repetidos es calculada automaticamente
hListToRecAuto : DecEq lty => (ts : LabelList lty) -> HList ts -> RecordOrUnit ts
hListToRecAuto ts hs with (isLabelSet ts)
  hListToRecAuto ts hs | No notTsIsSet = ()
  hListToRecAuto ts hs | Yes tsIsSet = MkRecord tsIsSet hs

        
-- *** hProjectByLabels ***                     
                                    
-- DeleteElem es el predicado que indica que una lista es el resultado de eliminar un elemento de otra lista
data DeleteElem : (xs : List t) -> Elem x xs -> List t -> Type where
  DeleteElemHere : DeleteElem (x :: xs) Here xs
  DeleteElemThere : DeleteElem xs isThere ys -> DeleteElem (x :: xs) (There isThere) (x :: ys)

-- Predicado que la proyeccion izquierda de un hProjectByLabels es efectivamente tal proyeccion    
data IsProjectLeft : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type where
  IPL_EmptyLabels : DecEq lty => IsProjectLeft {lty=lty} [] ts []
  IPL_EmptyVect : DecEq lty => IsProjectLeft {lty=lty} ls [] []
  IPL_ProjLabelElem : DecEq lty => (isElem : Elem (fst t) ls) -> DeleteElem ls isElem lsNew ->
                      IsProjectLeft {lty=lty} lsNew ts res1 -> IsProjectLeft ls (t :: ts) (t :: res1)      
  IPL_ProjLabelNotElem : DecEq lty => Not (Elem (fst t) ls) -> IsProjectLeft {lty=lty} ls ts res1 -> 
                       IsProjectLeft ls (t :: ts) res1

-- Predicado que la proyeccion derecha de un hProjectByLabels es efectivamente tal proyeccion    
data IsProjectRight : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type where
  IPR_EmptyLabels : DecEq lty => IsProjectRight {lty=lty} [] ts ts
  IPR_EmptyVect : DecEq lty => IsProjectRight {lty=lty} ls [] []
  IPR_ProjLabelElem : DecEq lty => (isElem : Elem (fst t) ls) -> DeleteElem ls isElem lsNew ->
                      IsProjectRight {lty=lty} lsNew ts res1 -> IsProjectRight ls (t :: ts) res1      
  IPR_ProjLabelNotElem : DecEq lty => Not (Elem (fst t) ls) -> IsProjectRight {lty=lty} ls ts res1 -> 
                       IsProjectRight ls (t :: ts) (t :: res1)
  
-- Funcion que dada una prueba que un elemento pertenece a una lista, retorna la lista sin el elemento y una prueba de que 
-- fue eliminado
deleteElem : {x : t} -> (xs : List t) -> (elem : Elem x xs) -> (res : List t ** DeleteElem xs elem res)
deleteElem (x :: xs) Here = (xs ** DeleteElemHere)
deleteElem (x :: xs) (There xinthere) =
  let (subDel ** subPrf) = deleteElem xs xinthere
  in (x :: subDel ** DeleteElemThere subPrf)
          
-- hProjectByLabels que tambien devuelve una prueba de que los vectores son actualmente proyecciones izq y der para un HList
-- Este hProjectByLabels retorna ambas listas: La de proyecciones y la resultante      
hProjectByLabelsHList : DecEq lty => {ts : LabelList lty} -> (ls : List lty) -> HList ts ->     
  ((ls1 : LabelList lty ** (HList ls1, IsProjectLeft ls ts ls1)),
  (ls2 : LabelList lty ** (HList ls2, IsProjectRight ls ts ls2)))
hProjectByLabelsHList [] {ts=ts} hs = 
                   (([] ** ([], IPL_EmptyLabels)),
                   (ts ** (hs, IPR_EmptyLabels)))
hProjectByLabelsHList _ [] =
                   (([] ** ([], IPL_EmptyVect)),
                   ([] ** ([], IPR_EmptyVect)))
hProjectByLabelsHList {lty=lty} ls ((::) {lbl=l2} {t=t} {ts=ts2} val hs) =
  case (isElem l2 ls) of
    Yes l2inls =>
      let
        (lsNew ** isDelElem) = deleteElem ls l2inls
        ((subInLs ** (subInHs, subPrjLeft)), (subOutLs ** (subOutHs, subPrjRight))) =
          hProjectByLabelsHList {lty=lty} {ts=ts2} lsNew hs
        rPrjRight = IPR_ProjLabelElem {t=(l2,t)} {ts=ts2} {res1=subOutLs} l2inls isDelElem subPrjRight
        rPrjLeft = IPL_ProjLabelElem {t=(l2,t)} {ts=ts2} {res1=subInLs} l2inls isDelElem subPrjLeft
        rRight = (subOutLs ** (subOutHs, rPrjRight))
        rLeft = ((l2,t) :: subInLs ** ((::) {lbl=l2} val subInHs, rPrjLeft))
       in
         (rLeft, rRight)
    No l2ninls =>
      let
        ((subInLs ** (subInHs, subPrjLeft)), (subOutLs ** (subOutHs, subPrjRight))) =
          hProjectByLabelsHList {lty=lty} {ts=ts2} ls hs
        rPrjLeft = IPL_ProjLabelNotElem {t=(l2,t)} {ts=ts2} {res1=subInLs} l2ninls subPrjLeft
        rPrjRight = IPR_ProjLabelNotElem {t=(l2,t)} {ts=ts2} {res1=subOutLs} l2ninls subPrjRight
        rLeft = (subInLs ** (subInHs, rPrjLeft))
        rRight = ((l2,t) :: subOutLs ** ((::) {lbl=l2} val subOutHs, rPrjRight))
      in
        (rLeft, rRight)
    
-- Dada una prueba que un elemento no pertenece a un Cons de una lista, divide tal prueba en sus dos componentes
notElem_Lemma1 : Not (Elem x (y :: xs)) -> (Not (Elem x xs), Not (x = y))
notElem_Lemma1 notElemCons = (notElem_prf, notEq_prf)
  where
    notElem_prf isElem = notElemCons $ There isElem
    notEq_prf isEq = notElemCons $ rewrite isEq in Here
    
-- Dada una prueba que un elemento no pertenece a una lista, y no es igual a otro, se obtiene la prueba de que no pertenece al Cons
-- Es isomorfo al lemma anterior
notElem_Lemma2 : Not (Elem x xs) -> Not (x = y) -> Not (Elem x (y :: xs))
notElem_Lemma2 notElem notEq Here = notEq Refl
notElem_Lemma2 notElem notEq (There isElem) = notElem isElem 
    
-- Prueba de que una proyeccion por la derecha, si un label no pertenece a la lista inicial, entonces tampoco pertenece al resultante    
hProjectByLabelsRightIsSet_Lemma1 : DecEq lty => {ls : List lty} -> {ts1 : LabelList lty} -> {ts2 : LabelList lty} ->
  IsProjectRight ls ts1 ts2 -> Not (ElemLabel lbl ts1) -> Not (ElemLabel lbl ts2)
hProjectByLabelsRightIsSet_Lemma1 IPR_EmptyLabels notElem = notElem
hProjectByLabelsRightIsSet_Lemma1 IPR_EmptyVect notElem = notElem
hProjectByLabelsRightIsSet_Lemma1 (IPR_ProjLabelElem isElem delLs subPrjRight) notElem = 
  let
    (notElemSub, notEq) = notElem_Lemma1 notElem
    isNotElemRec = hProjectByLabelsRightIsSet_Lemma1 subPrjRight notElemSub
  in isNotElemRec
hProjectByLabelsRightIsSet_Lemma1 (IPR_ProjLabelNotElem subNotElem subPrjRight) notElem = 
  let
    (notElemSub, notEq) = notElem_Lemma1 notElem
    isNotElemRec = hProjectByLabelsRightIsSet_Lemma1 subPrjRight notElemSub
  in notElem_Lemma2 isNotElemRec notEq

-- Dada una proyeccion por la izquierda, si un label no pertenece a la lista inicial, tampoco pertenece al resultante      
hProjectByLabelsLeftIsSet_Lemma1 : DecEq lty => {ls : List lty} -> {ts1 : LabelList lty} -> {ts2 : LabelList lty} ->
  IsProjectLeft ls ts1 ts2 -> Not (ElemLabel lbl ts1) -> Not (ElemLabel lbl ts2)
hProjectByLabelsLeftIsSet_Lemma1 IPL_EmptyLabels notElem = noEmptyElem
hProjectByLabelsLeftIsSet_Lemma1 IPL_EmptyVect notElem = notElem
hProjectByLabelsLeftIsSet_Lemma1 (IPL_ProjLabelElem isElem delElem subPrjLeft) notElem = 
  let
    (notElemSub, notEq) = notElem_Lemma1 notElem
    isNotElemRec = hProjectByLabelsLeftIsSet_Lemma1 subPrjLeft notElemSub
  in notElem_Lemma2 isNotElemRec notEq  
hProjectByLabelsLeftIsSet_Lemma1 (IPL_ProjLabelNotElem subNotElem subPrjLeft) notElem =
  let
    (notElemSub, notEq) = notElem_Lemma1 notElem
    isNotElemRec = hProjectByLabelsLeftIsSet_Lemma1 subPrjLeft notElemSub
  in isNotElemRec

-- Dada una proyeccion por la derecha, si la lista inicial es un set, entonces la resultante tambien lo es
hProjectByLabelsRightIsSet_Lemma2 : DecEq lty => {ls : List lty} -> {ts1 : LabelList lty} -> {ts2 : LabelList lty} 
  -> IsProjectRight ls ts1 ts2 -> IsLabelSet ts1 -> IsLabelSet ts2
hProjectByLabelsRightIsSet_Lemma2 IPR_EmptyLabels isLabelSet = isLabelSet         
hProjectByLabelsRightIsSet_Lemma2 IPR_EmptyVect isLabelSet = isLabelSet         
hProjectByLabelsRightIsSet_Lemma2 (IPR_ProjLabelElem isElem delLs subPrjRight) (IsSetCons notMember subLabelSet) =
  let isLabelSetRec = hProjectByLabelsRightIsSet_Lemma2 subPrjRight subLabelSet
  in isLabelSetRec 
hProjectByLabelsRightIsSet_Lemma2 (IPR_ProjLabelNotElem notElem subPrjRight) (IsSetCons notMember subLabelSet) = 
  let isLabelSetRec = hProjectByLabelsRightIsSet_Lemma2 subPrjRight subLabelSet
      notElemPrf = hProjectByLabelsRightIsSet_Lemma1 subPrjRight notMember 
  in IsSetCons notElemPrf isLabelSetRec

-- Dada una proyeccion por la izquierda, si la lista inicial es un set, entonces la resultante tambien lo es    
hProjectByLabelsLeftIsSet_Lemma2 : DecEq lty => {ls : List lty} -> {ts1 : LabelList lty} -> {ts2 : LabelList lty} 
  -> IsProjectLeft ls ts1 ts2 -> IsLabelSet ts1 -> IsLabelSet ts2
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
hProjectByLabels : DecEq lty => {ts1 : LabelList lty} -> (ls : List lty) -> Record ts1 ->     
  (ts2 : LabelList lty ** (Record ts2, IsProjectLeft ls ts1 ts2))
hProjectByLabels ls rec =
  let 
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
    (lsRes ** (hsRes, prjLeftRes)) = fst $ hProjectByLabelsHList ls hs
    isLabelSetRes = hProjectByLabelsLeftIsSet_Lemma2 prjLeftRes isLabelSet
  in (lsRes ** (hListToRec {prf=isLabelSetRes} hsRes, prjLeftRes)) 
  
  
-- *** hDeleteByLabel *** 
  
-- Predicado que indica que un campo fue eliminado de la lista de un record      
data DeleteLabelAtPred : DecEq lty => lty -> LabelList lty -> LabelList lty -> Type where
  EmptyRecord : DecEq lty => {lbl : lty} -> DeleteLabelAtPred lbl [] []
  IsElem : DecEq lty => {lbl : lty} -> DeleteLabelAtPred lbl ((lbl,ty) :: ts) ts
  IsNotElem : DecEq lty => {lbl : lty} -> DeleteLabelAtPred lbl ts1 ts2 -> DeleteLabelAtPred lbl (tup :: ts1) (tup :: ts2)
          
-- Transformo una prueba de que se proyecto una lista con un solo elemento a una prueba de que se elimino tal elemento
fromIsProjectRightToDeleteFromRec : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} ->
                                  {lbl : lty} -> IsProjectRight [lbl] ts1 ts2 -> DeleteLabelAtPred lbl ts1 ts2
fromIsProjectRightToDeleteFromRec IPR_EmptyVect = EmptyRecord
fromIsProjectRightToDeleteFromRec {lbl=lbl} (IPR_ProjLabelElem {t=(lbl,ty)} Here delElem IPR_EmptyLabels) = IsElem
fromIsProjectRightToDeleteFromRec (IPR_ProjLabelElem (There isElem) delElem IPR_EmptyLabels) = absurd $ noEmptyElem isElem
fromIsProjectRightToDeleteFromRec {lbl=lbl} (IPR_ProjLabelElem {t=(lbl,ty)} Here delElem IPR_EmptyVect) = IsElem
fromIsProjectRightToDeleteFromRec (IPR_ProjLabelElem (There isElem) delElem IPR_EmptyVect) = absurd $ noEmptyElem isElem
fromIsProjectRightToDeleteFromRec (IPR_ProjLabelElem isElem delElem (IPR_ProjLabelElem subElem subDel subPrjRight)) impossible
fromIsProjectRightToDeleteFromRec (IPR_ProjLabelElem isElem delElem (IPR_ProjLabelNotElem subNotElem subPrjRight)) impossible
fromIsProjectRightToDeleteFromRec (IPR_ProjLabelNotElem notElem subPrjRight) = 
  let subDelFromRec = fromIsProjectRightToDeleteFromRec subPrjRight
  in IsNotElem subDelFromRec
    
-- *-* Definicion de "hDeleteAtLabel" de hackage *-*
hDeleteAtLabel : DecEq lty => {ts1 : LabelList lty} -> (lbl : lty) -> Record ts1 ->
  (ts2 : LabelList lty ** (Record ts2, DeleteLabelAtPred lbl ts1 ts2))
hDeleteAtLabel lbl rec =
  let 
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
    (_, (ts2 ** (hs2, prjRightRes))) = hProjectByLabelsHList [lbl] hs
    isLabelSet2 = hProjectByLabelsRightIsSet_Lemma2 prjRightRes isLabelSet
  in (ts2 ** (hListToRec {prf=isLabelSet2} hs2, fromIsProjectRightToDeleteFromRec prjRightRes))


-- *** hAppend ***

-- hAppend para HList
(++) : HList ts1 -> HList ts2 -> HList (ts1 ++ ts2)
(++) [] hs2 = hs2
(++) (h1 :: hs1) hs2 = h1 :: (hs1 ++ hs2)

-- *-* Definicion de "hAppend" de hackage *-*
hAppend : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} -> Record ts1 -> Record ts2 ->
  IsLabelSet (ts1 ++ ts2) -> Record (ts1 ++ ts2)
hAppend rec1 rec2 isLabelSet =
  let
    hs1 = recToHList rec1
    hs2 = recToHList rec2
  in hListToRec {prf=isLabelSet} (hs1 ++ hs2)
    
-- "hAppendAuto" donde la prueba de labels no repetidos es calculada automaticamente
hAppendAuto : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} -> Record ts1 -> Record ts2 -> RecordOrUnit (ts1 ++ ts2)
hAppendAuto {ts1=ts1} {ts2=ts2} rec1 rec2 with (isLabelSet (ts1 ++ ts2))
  hAppendAuto {ts1=ts1} {ts2=ts2} rec1 rec2 | No notIsSet = ()
  hAppendAuto {ts1=ts1} {ts2=ts2} rec1 rec2 | Yes isSet = hAppend rec1 rec2 isSet


-- *** hDeleteLabels ***

-- Predicado que indica que una lista de labels fue eliminada de un record
DeleteLabelsPred : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type
DeleteLabelsPred = IsProjectRight

-- *-* Definicion de "hDeleteLabels" de hackage *-*
hDeleteLabels : DecEq lty => {ts1 : LabelList lty} -> (ls : List lty) -> Record ts1 ->
  (ts2 : LabelList lty ** (Record ts2, DeleteLabelsPred ls ts1 ts2))
hDeleteLabels ls rec =
  let
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
    (_, (ts2 ** (hs2, prjRightRes))) = hProjectByLabelsHList ls hs
    isLabelSet2 = hProjectByLabelsRightIsSet_Lemma2 prjRightRes isLabelSet
  in
    (ts2 ** (hListToRec {prf=isLabelSet2} hs2, prjRightRes))


-- *** hLeftUnion ***

-- Predicado que indica que la union de dos LabelList que son un set es equivalente a la tercera
data IsSetUnion : DecEq lty => LabelList lty -> LabelList lty -> LabelList lty -> Type where
  LeftIsEmpty : DecEq lty => IsLabelSet ts2 -> IsSetUnion {lty=lty} [] ts2 ts2
  IsInRight : DecEq lty => ElemLabel (fst t) ts2 -> Not (ElemLabel (fst t) ts1) ->  IsSetUnion ts1 ts2 tsRes -> 
    IsSetUnion {lty=lty} (t :: ts1) ts2 tsRes
  IsNotInRight : DecEq lty => Not (ElemLabel (fst t) ts2) -> Not (ElemLabel (fst t) ts1) -> IsSetUnion ts1 ts2 tsRes -> 
    IsSetUnion {lty=lty} (t :: ts1) ts2 (t :: tsRes)

-- Lemmas necesarios
ifAppendEmptyIsLabelSetLemma : IsLabelSet ts -> IsLabelSet (ts ++ [])
ifAppendEmptyIsLabelSetLemma {ts=ts} isLblSet = rewrite (appendNilRightNeutral ts) in isLblSet

ifDeleteLabelsThenAppendIsSetLemma_1 : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} -> {t : (lty, Type)} ->
  IsLabelSet (ts1 ++ ts2) -> Not (ElemLabel (fst t) ts1) -> IsLabelSet (ts1 ++ (t :: ts2))
ifDeleteLabelsThenAppendIsSetLemma_1 lblSetAppend notElem = ?ifDeleteLabelsThenAppendIsSetLemma_1_rhs

-- Lemma que indica que si se eliminan del 2ndo record los labels del 1ero, entonces agregar la resta al 1ero es un labelset
ifDeleteLabelsThenAppendIsSetLemma : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} -> {tsDel : LabelList lty} ->
  IsLabelSet ts1 -> IsLabelSet ts2 -> DeleteLabelsPred (labelsOf ts1) ts2 tsDel -> IsLabelSet (ts1 ++ tsDel)
ifDeleteLabelsThenAppendIsSetLemma {ts1=[]} isLblSet1 isLblSet2 IPR_EmptyLabels = isLblSet2
ifDeleteLabelsThenAppendIsSetLemma isLblSet1 isLblSet2 IPR_EmptyVect = ifAppendEmptyIsLabelSetLemma isLblSet1
ifDeleteLabelsThenAppendIsSetLemma {ts1=ts1} {ts2=(t :: tsSub)} isLblSet1 isLblSet2 (IPR_ProjLabelElem isElem delElem subPrjRight) = ?ifDeleteLabelsThenAppendIsSetLemma_rhs_2
ifDeleteLabelsThenAppendIsSetLemma {ts1=ts1} {ts2=(t :: tsSub)} isLblSet1 isLblSet2 (IPR_ProjLabelNotElem {res1=subTsDel} notElem subPrjRight) = 
  let
    subLabelSet = ifDeleteLabelsThenAppendIsSetLemma {ts1=ts1} {ts2=tsSub} {tsDel=subTsDel} isLblSet1 (ifSetThenRestIsSet isLblSet2) subPrjRight
  in ifDeleteLabelsThenAppendIsSetLemma_1 {ts1=ts1} {ts2=subTsDel} {t=t} subLabelSet notElem
    
-- Lemma que indica que una lista es la union de si misma (por la izquierda)
leftListIsSetUnion : DecEq lty => {ts : LabelList lty} -> IsLabelSet ts -> IsSetUnion ts [] ts
leftListIsSetUnion {ts=[]} IsSetNil = LeftIsEmpty IsSetNil
leftListIsSetUnion {ts=(t :: ts)} (IsSetCons notElem subLblSet) = 
  let subSetUnion = leftListIsSetUnion {ts=ts} subLblSet
  in IsNotInRight noEmptyElem notElem subSetUnion

-- Lemma que indica que si se eliminan del 2ndo record los labels del 1ero, entonces agregar la resta al 1ero equivale a la union de
-- ambos
ifDeleteLabelsThenItIsSetUnion : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} -> {tsDel : LabelList lty} ->
  IsLabelSet ts1 -> IsLabelSet ts2 -> DeleteLabelsPred (labelsOf ts1) ts2 tsDel -> IsSetUnion ts1 ts2 (ts1 ++ tsDel)
ifDeleteLabelsThenItIsSetUnion {ts1=[]} isLblSet1 isLblSet2 IPR_EmptyLabels = LeftIsEmpty isLblSet2
ifDeleteLabelsThenItIsSetUnion {ts1=ts1} isLblSet1 isLblSet2 IPR_EmptyVect = 
  rewrite (appendNilRightNeutral ts1) in leftListIsSetUnion isLblSet1
ifDeleteLabelsThenItIsSetUnion {ts2=(t::ts2)} isLblSet1 isLblSet2 (IPR_ProjLabelElem isElem delElem subPrjRight) = ?ifDeleteLabelsThenItIsSetUnion_rhs_2
ifDeleteLabelsThenItIsSetUnion {ts2=(t::ts2)} isLblSet1 isLblSet2 (IPR_ProjLabelNotElem notElem subPrjRight) = ?ifDeleteLabelsThenItIsSetUnion_rhs_3

-- *-* Definicion de "hLeftUnion" de hackage *-*
hLeftUnion : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} -> Record ts1 -> Record ts2 -> 
   (tsRes : LabelList lty ** (Record tsRes, IsSetUnion ts1 ts2 tsRes))
hLeftUnion {ts1=ts1} {ts2=ts2} rec1 rec2 = 
  let
    isLblSet1 = recLblIsSet rec1
    isLblSet2 = recLblIsSet rec2
    (tsDel ** (recDel, prfDel)) = hDeleteLabels (labelsOf ts1) rec2
    recRes = hAppend rec1 recDel (ifDeleteLabelsThenAppendIsSetLemma {ts1=ts1} {ts2=ts2} {tsDel=tsDel} isLblSet1 isLblSet2 prfDel)
   in
    (ts1 ++ tsDel ** (recRes, ifDeleteLabelsThenItIsSetUnion {ts1=ts1} {ts2=ts2} {tsDel=tsDel} isLblSet1 isLblSet2 prfDel))
    
  
