{-

  Definición de Records Extensibles.
  
  Se toma inspiración en HList de Haskell
  Paper: http://okmij.org/ftp/Haskell/HList-ext.pdf
  Hackage: https://hackage.haskell.org/package/HList
  
-}

module Extensible_Records

import Data.List

%default total

consNotEqNil : {xs : List t} -> Not (x :: xs = [])
consNotEqNil Refl impossible

-- Nada puede pertenecer a una lista vacia
noEmptyElem : Not (Elem x [])
noEmptyElem Here impossible

-- Si un elemento no pertenece a una lista, no pertenece al tail de esa lista tampoco
notElemInCons : Not (Elem x (y :: ys)) -> Not (Elem x ys)
notElemInCons notElemCons elemTail = notElemCons $ There elemTail

-- Si un elemento no pertenece a una lista, no es igual al primer elemento de esta
ifNotElemThenNotEqual : Not (Elem x (y :: ys)) -> Not (x = y)
ifNotElemThenNotEqual notElemCons equal = notElemCons $ rewrite equal in Here

-- Sym para Not
symNot : Not (x = y) -> Not (y = x)
symNot notEqual Refl = notEqual Refl

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


-- *** PENDIENTE ***

--XOrUnit : Dec p -> (p -> Type) -> Type
--XOrUnit d maker 

-- *** FinPendiente

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
hProjectByLabelsRightIsSet_Lemma1 : DecEq lty => {ls : List lty} -> {ts1, ts2 : LabelList lty} ->
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
hProjectByLabelsLeftIsSet_Lemma1 : DecEq lty => {ls : List lty} -> {ts1, ts2 : LabelList lty} ->
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
hProjectByLabelsRightIsSet_Lemma2 : DecEq lty => {ls : List lty} -> {ts1, ts2 : LabelList lty} -> 
  IsProjectRight ls ts1 ts2 -> IsLabelSet ts1 -> IsLabelSet ts2
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
hProjectByLabelsLeftIsSet_Lemma2 : DecEq lty => {ls : List lty} -> {ts1, ts2 : LabelList lty} -> 
  IsProjectLeft ls ts1 ts2 -> IsLabelSet ts1 -> IsLabelSet ts2
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
  
-- Predicado que indica que un campo fue eliminado de la lista de un record. Si el elemento no existe en la lista la retorna igual      
data DeleteLabelAtPred : DecEq lty => lty -> LabelList lty -> LabelList lty -> Type where
  EmptyRecord : DecEq lty => {lbl : lty} -> DeleteLabelAtPred lbl [] []
  IsElem : DecEq lty => {lbl : lty} -> DeleteLabelAtPred lbl ((lbl,ty) :: ts) ts
  IsNotElem : DecEq lty => {lbl : lty} -> Not (lbl = fst tup) -> DeleteLabelAtPred lbl ts1 ts2 -> DeleteLabelAtPred lbl (tup :: ts1) (tup :: ts2)
                              
-- Transformo una prueba de que se proyecto una lista con un solo elemento a una prueba de que se elimino tal elemento
fromIsProjectRightToDeleteLabelAtPred : DecEq lty => {ts1, ts2 : LabelList lty} -> {lbl : lty} -> IsProjectRight [lbl] ts1 ts2 -> 
  DeleteLabelAtPred lbl ts1 ts2
fromIsProjectRightToDeleteLabelAtPred IPR_EmptyVect = EmptyRecord
fromIsProjectRightToDeleteLabelAtPred {lbl=lbl} (IPR_ProjLabelElem {t=(lbl,ty)} Here delElem IPR_EmptyLabels) = IsElem
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelElem (There isElem) delElem IPR_EmptyLabels) = absurd $ noEmptyElem isElem
fromIsProjectRightToDeleteLabelAtPred {lbl=lbl} (IPR_ProjLabelElem {t=(lbl,ty)} Here delElem IPR_EmptyVect) = IsElem
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelElem (There isElem) delElem IPR_EmptyVect) = absurd $ noEmptyElem isElem
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelElem isElem delElem (IPR_ProjLabelElem subElem subDel subPrjRight)) impossible
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelElem isElem delElem (IPR_ProjLabelNotElem subNotElem subPrjRight)) impossible
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelNotElem notElem subPrjRight) = 
  let subDelFromRec = fromIsProjectRightToDeleteLabelAtPred subPrjRight
      notEqual = ifNotElemThenNotEqual notElem
  in IsNotElem (symNot notEqual) subDelFromRec
    
-- *-* Definicion de "hDeleteAtLabel" de hackage *-*
hDeleteAtLabel : DecEq lty => {ts1 : LabelList lty} -> (lbl : lty) -> Record ts1 ->
  (ts2 : LabelList lty ** (Record ts2, DeleteLabelAtPred lbl ts1 ts2))
hDeleteAtLabel lbl rec =
  let 
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
    (_, (ts2 ** (hs2, prjRightRes))) = hProjectByLabelsHList [lbl] hs
    isLabelSet2 = hProjectByLabelsRightIsSet_Lemma2 prjRightRes isLabelSet
  in (ts2 ** (hListToRec {prf=isLabelSet2} hs2, fromIsProjectRightToDeleteLabelAtPred prjRightRes))


-- *** hAppend ***

-- hAppend para HList
(++) : HList ts1 -> HList ts2 -> HList (ts1 ++ ts2)
(++) [] hs2 = hs2
(++) (h1 :: hs1) hs2 = h1 :: (hs1 ++ hs2)

ifIsElemThenIsInAppendLeft : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
    ElemLabel l ts1 -> ElemLabel l (ts1 ++ ts2)
ifIsElemThenIsInAppendLeft {ts1=((l,ty) :: ts1)} Here = Here
ifIsElemThenIsInAppendLeft {ts1=((l,ty) :: ts1)} {ts2=ts2} (There isThere) = 
  let subPrf = ifIsElemThenIsInAppendLeft {ts2=ts2} isThere
  in (There subPrf)

ifIsElemThenIsInAppendRight : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  ElemLabel l ts2 -> ElemLabel l (ts1 ++ ts2)
ifIsElemThenIsInAppendRight {ts1=[]} isElem = isElem
ifIsElemThenIsInAppendRight {ts1=((l1,ty1) :: ts1)} {ts2=[]} isElem = absurd $ noEmptyElem isElem
ifIsElemThenIsInAppendRight {l=l} {ts1=((l1,ty1) :: ts1)} {ts2=((l2,ty2) :: ts2)} isElem = 
  let subPrf = ifIsElemThenIsInAppendRight {ts1=ts1} {ts2=((l2,ty2)::ts2)} {l=l} isElem
  in There subPrf

-- Si un elemento pertenece a una de las dos listas, pertenece al append
ifIsInOneThenIsInAppend : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  Either (ElemLabel l ts1) (ElemLabel l ts2) -> ElemLabel l (ts1 ++ ts2)
ifIsInOneThenIsInAppend (Left isElem) = ifIsElemThenIsInAppendLeft isElem    
ifIsInOneThenIsInAppend {ts1=ts1} {ts2=ts2} {l=l} (Right isElem) = ifIsElemThenIsInAppendRight isElem     

-- Si el elemento pertenece a un append, pertenece a alguna de ambas listas
ifIsInAppendThenIsInOne : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  ElemLabel l (ts1 ++ ts2) -> Either (ElemLabel l ts1) (ElemLabel l ts2)
ifIsInAppendThenIsInOne {ts1=[]} isElem = (Right isElem)
ifIsInAppendThenIsInOne {ts1=((l1,ty1) :: ts1)} Here = (Left Here)
ifIsInAppendThenIsInOne {l=l} {ts1=((l1,ty) :: ts1)} (There isThere) =
  case (ifIsInAppendThenIsInOne isThere) of
    Left isElem => Left $ There isElem
    Right isElem => Right isElem
    
-- Si un elemento no pertenece a un append, entonces no pertenece a ninguno
ifNotInAppendThenNotInNeither : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  Not (ElemLabel l (ts1 ++ ts2)) -> (Not (ElemLabel l ts1), Not (ElemLabel l ts2))
ifNotInAppendThenNotInNeither {ts1=[]} {ts2=ts2} {l=l} notInAppend = (notInTs1, notInTs2)
   where
    notInTs1 : Not (ElemLabel l [])
    notInTs1 inTs1 = noEmptyElem inTs1
    
    notInTs2 : Not (ElemLabel l ts2)
    notInTs2 inTs2 = notInAppend inTs2
ifNotInAppendThenNotInNeither {ts1=((l2,ty)::ts1)} {ts2=ts2} {l=l} notInAppend = (notInTs1, notInTs2)
  where    
    notInTs1 : Not (ElemLabel l ((l2,ty)::ts1))
    notInTs1 Here impossible
    notInTs1 (There isThere) = 
      let isInAppend = ifIsInOneThenIsInAppend {ts1=ts1} {ts2=ts2} (Left isThere)
      in notInAppend (There isInAppend)
    
    notInTs2 : Not (ElemLabel l ts2)
    notInTs2 inTs2 =
      let isInAppend = ifIsInOneThenIsInAppend {ts1=ts1} {ts2=ts2} (Right inTs2)
      in notInAppend (There isInAppend)

-- Si un label no esta en ningun lado, no esta en el append
ifNotInEitherThenNotInAppend : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  Not (ElemLabel l ts1) -> Not (ElemLabel l ts2) -> Not (ElemLabel l (ts1 ++ ts2))
ifNotInEitherThenNotInAppend {ts1=[]} notInTs1 notInTs2 inAppend = notInTs2 inAppend
ifNotInEitherThenNotInAppend {ts1=((l1,ty1) :: ts1)} notInTs1 notInTs2 Here = notInTs1 Here
ifNotInEitherThenNotInAppend {ts1=((l1,ty1) :: ts1)} notInTs1 notInTs2 (There inThere) = 
  let notInAppend = ifNotInEitherThenNotInAppend (notElemInCons notInTs1) notInTs2
  in notInAppend inThere

-- Si dos labellist concatenados son un set, cada uno es un set
ifAppendIsSetThenEachIsToo : DecEq lty => {ts1, ts2 : LabelList lty} -> IsLabelSet (ts1 ++ ts2) -> (IsLabelSet ts1, IsLabelSet ts2)
ifAppendIsSetThenEachIsToo {ts1=[]} isSet = (IsSetNil, isSet)
ifAppendIsSetThenEachIsToo {ts1=((l,ty)::ts1)} (IsSetCons notInAppend isSetAppend) =
  let 
    subPrf = ifAppendIsSetThenEachIsToo isSetAppend
    notInTs1 = fst $ ifNotInAppendThenNotInNeither notInAppend
  in (IsSetCons notInTs1 (fst $ subPrf), snd subPrf)

-- *-* Definicion de "hAppend" de hackage *-*
hAppend : DecEq lty => {ts1, ts2 : LabelList lty} -> Record ts1 -> Record ts2 -> IsLabelSet (ts1 ++ ts2) -> Record (ts1 ++ ts2)
hAppend rec1 rec2 isLabelSet =
  let
    hs1 = recToHList rec1
    hs2 = recToHList rec2
  in hListToRec {prf=isLabelSet} (hs1 ++ hs2)
    
-- "hAppendAuto" donde la prueba de labels no repetidos es calculada automaticamente
hAppendAuto : DecEq lty => {ts1, ts2 : LabelList lty} -> Record ts1 -> Record ts2 -> RecordOrUnit (ts1 ++ ts2)
hAppendAuto {ts1=ts1} {ts2=ts2} rec1 rec2 with (isLabelSet (ts1 ++ ts2))
  hAppendAuto {ts1=ts1} {ts2=ts2} rec1 rec2 | No notIsSet = ()
  hAppendAuto {ts1=ts1} {ts2=ts2} rec1 rec2 | Yes isSet = hAppend rec1 rec2 isSet


-- *** hDeleteLabels ***

-- Predicado que indica que una lista de labels fue eliminada de un record
data DeleteLabelsPred : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type where
  EmptyLabelList : DecEq lty => DeleteLabelsPred {lty=lty} [] ts ts
  DeleteFirstOfLabelList : DecEq lty => DeleteLabelAtPred l tsAux tsRes -> DeleteLabelsPred ls ts tsAux ->
    DeleteLabelsPred {lty=lty} (l :: ls) ts tsRes
    
-- Lemmas necesarios
fromIsProjectRightToDeleteLabelsPred_Lemma1 : DecEq lty => (ls : List lty) -> DeleteLabelsPred ls [] []      
fromIsProjectRightToDeleteLabelsPred_Lemma1 [] = EmptyLabelList
fromIsProjectRightToDeleteLabelsPred_Lemma1 (l :: ls) = 
  let subPrf = fromIsProjectRightToDeleteLabelsPred_Lemma1 ls
  in DeleteFirstOfLabelList EmptyRecord subPrf
  
fromIsProjectRightToDeleteLabelsPred_Lemma2 : DecEq lty => {ts1, ts2 : LabelList lty} -> DeleteLabelsPred [] ts1 ts2 -> ts1 = ts2   
fromIsProjectRightToDeleteLabelsPred_Lemma2 EmptyLabelList = Refl

fromIsProjectRightToDeleteLabelsPred_Lemma3 : DecEq lty => {l : lty} -> {t : (lty, Type)} -> Not (fst t = l) ->
  DeleteLabelAtPred l ts1 ts2 -> DeleteLabelAtPred l (t :: ts1) (t :: ts2)
fromIsProjectRightToDeleteLabelsPred_Lemma3 notEqual EmptyRecord = IsNotElem (symNot notEqual) EmptyRecord 
fromIsProjectRightToDeleteLabelsPred_Lemma3 notEqual IsElem = IsNotElem (symNot notEqual) IsElem
fromIsProjectRightToDeleteLabelsPred_Lemma3 notEqual (IsNotElem subNotEqual subDelAtLabelPred) = 
  let subDelPred = fromIsProjectRightToDeleteLabelsPred_Lemma3 (symNot subNotEqual) subDelAtLabelPred
  in IsNotElem (symNot notEqual) subDelPred

fromIsProjectRightToDeleteLabelsPred_Lemma4 : DecEq lty => {ts1, ts2 : LabelList lty} -> {t : (lty,Type)} ->
  {ls : List lty} -> Not (Elem (fst t) ls) -> DeleteLabelsPred ls ts1 ts2 -> DeleteLabelsPred ls (t :: ts1) (t :: ts2)
fromIsProjectRightToDeleteLabelsPred_Lemma4 notElem EmptyLabelList = EmptyLabelList
fromIsProjectRightToDeleteLabelsPred_Lemma4 {t=t} notElem (DeleteFirstOfLabelList delAtLabelPred delLabelsPred) =
  let notElemTail = notElemInCons notElem
      subDelPred = fromIsProjectRightToDeleteLabelsPred_Lemma4 {t=t} notElemTail delLabelsPred
      notEqElem = ifNotElemThenNotEqual notElem
      consDelAtLabelPred = fromIsProjectRightToDeleteLabelsPred_Lemma3 {t=t} notEqElem delAtLabelPred
  in DeleteFirstOfLabelList consDelAtLabelPred subDelPred

{-fromIsProjectRightToDeleteLabelsPred_Lemma5 : DecEq lty => {ts1, ts2 : LabelList lty} -> {t : (lty,Type)} -> {ls : List lty} ->
  Not (Elem (fst t) ls) -> DeleteLabelsPred ls ts1 ts2 -> DeleteLabelsPred (fst t :: ls) (t :: ts1) ts2
fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(lbl,lty)} notElem {ts2=ts2} delLabelsPred = 
  let subDelPrf = fromIsProjectRightToDeleteLabelsPred_Lemma4 {t=(lbl,lty)} notElem delLabelsPred
  in DeleteFirstOfLabelList {tsAux=((lbl,lty) :: ts2)} IsElem subDelPrf-}

fromIsProjectRightToDeleteLabelsPred_Lemma5_1 : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> {l1, l2 : lty} -> {ty : Type} ->
  DeleteLabelAtPred l2 ts3 ts2 -> DeleteLabelsPred xs ts1 ts3 -> DeleteLabelsPred (l1 :: xs) ((l1, ty) :: ts1) ts3 ->
  DeleteLabelsPred (l1 :: l2 :: xs) ((l1, ty) :: ts1) ts2
{-fromIsProjectRightToDeleteLabelsPred_Lemma5_1 {xs=xs} {l1=l1} {l2=l2} {ty=ty} {ts2=ts2} delAtPred delPred (DeleteFirstOfLabelList {tsAux=ts4} subDelAtPred subDelPred) with (isElem l1 (l2 :: xs)) 
  fromIsProjectRightToDeleteLabelsPred_Lemma5_1 {l1=l1} {l2=l1} {ty=ty} {ts2=ts2} delAtPred delPred (DeleteFirstOfLabelList {tsAux=ts4} subDelAtPred subDelPred) | Yes Here =
    let 
      subPrf = DeleteFirstOfLabelList delAtPred delPred
    --Como se sigue de aqui?
      tsAux = ?wat_1
    in DeleteFirstOfLabelList {tsAux=(l1, ty) :: ts2} IsElem (DeleteFirstOfLabelList {tsAux=tsAux} ?lemma5_1_rhs_1 ?lemma_5_1_rhs_2)
  fromIsProjectRightToDeleteLabelsPred_Lemma5_1 {l1=l1} {l2=l2} {ty=ty} {ts2=ts2} delAtPred delPred (DeleteFirstOfLabelList {tsAux=ts4} subDelAtPred subDelPred) | Yes (There isThere) =
    let 
      subPrf = DeleteFirstOfLabelList delAtPred delPred
    --Como se sigue de aqui?
      tsAux = ?wat_2
    in DeleteFirstOfLabelList {tsAux=(l1, ty) :: ts2} IsElem (DeleteFirstOfLabelList {tsAux=tsAux} ?lemma5_2_rhs_1 ?lemma_5_2_rhs_2)
  fromIsProjectRightToDeleteLabelsPred_Lemma5_1 {l1=l1} {l2=l2} {ty=ty} {ts2=ts2} delAtPred delPred (DeleteFirstOfLabelList {tsAux=ts4} subDelAtPred subDelPred) | No notElem =
    let 
      subPrf = DeleteFirstOfLabelList delAtPred delPred
      subLemma = fromIsProjectRightToDeleteLabelsPred_Lemma4 {t=(l1,ty)} notElem subPrf
    in DeleteFirstOfLabelList {tsAux=(l1, ty) :: ts2} IsElem subLemma-}
 
  

fromIsProjectRightToDeleteLabelsPred_Lemma5 : DecEq lty => {ts1, ts2 : LabelList lty} -> {t : (lty,Type)} -> {ls : List lty} ->
  DeleteLabelsPred ls ts1 ts2 -> DeleteLabelsPred (fst t :: ls) (t :: ts1) ts2
fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(lbl,lty)} {ts2=ts2} {ls=ls} delLabelsPred with (isElem lbl ls)
  fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(lbl,lty)} {ts2=ts2} delLabelsPred | No notElem =  
    let subDelPrf = fromIsProjectRightToDeleteLabelsPred_Lemma4 {t=(lbl,lty)} notElem delLabelsPred
    in DeleteFirstOfLabelList {tsAux=((lbl,lty) :: ts2)} IsElem subDelPrf
  fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(lbl,ty)} {ts2=ts2} EmptyLabelList | Yes Here impossible
  fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(lbl,ty)} {ts2=ts2} (DeleteFirstOfLabelList {tsAux=ts3} subDelAt subDelLbls) | Yes Here = 
    let subPrf = fromIsProjectRightToDeleteLabelsPred_Lemma5 subDelLbls
    in DeleteFirstOfLabelList {tsAux=ts3} subDelAt subPrf
  fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(lbl,ty)} {ts2=ts2} EmptyLabelList | Yes (There x) impossible
  fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(l1,ty1)} {ts2=ts2} (DeleteFirstOfLabelList {tsAux=ts3} {l=l2} subDelAt subDelLbls) | Yes (There inThere) =     
    let 
      subPrf = fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(l1,ty1)} subDelLbls
    in fromIsProjectRightToDeleteLabelsPred_Lemma5_1 subDelAt subDelLbls subPrf
  
fromIsProjectRightToDeleteLabelsPred_Lemma6 : DecEq lty => {ts1, ts2 : LabelList lty} -> {ls1, ls2 : List lty} ->
  {t : (lty, Type)} -> (isElem : Elem (fst t) ls1) -> DeleteElem ls1 isElem ls2 -> DeleteLabelsPred ls2 ts1 ts2 ->
  DeleteLabelsPred ls1 (t :: ts1) ts2
fromIsProjectRightToDeleteLabelsPred_Lemma6 {t=(l,ty)} {ts1=ts1} Here DeleteElemHere EmptyLabelList =
    DeleteFirstOfLabelList {tsAux=((l,ty) :: ts1)} IsElem EmptyLabelList
fromIsProjectRightToDeleteLabelsPred_Lemma6 {t=(l,ty)} Here DeleteElemHere (DeleteFirstOfLabelList {tsAux=ts3} subDelAtLabelPred subDelLabelsPred) =
  fromIsProjectRightToDeleteLabelsPred_Lemma5 {t=(l,ty)} (DeleteFirstOfLabelList subDelAtLabelPred subDelLabelsPred)
fromIsProjectRightToDeleteLabelsPred_Lemma6 (There isThere) (DeleteElemThere subDelElem) (DeleteFirstOfLabelList {tsAux=ts3} subDelAtLabelPred subDelLabelsPred) = 
  let subPrf = fromIsProjectRightToDeleteLabelsPred_Lemma6 isThere subDelElem subDelLabelsPred
  in DeleteFirstOfLabelList {tsAux=ts3} subDelAtLabelPred subPrf

fromIsProjectRightToDeleteLabelsPred_Lemma7 : DecEq lty => {ts1, ts2 : LabelList lty} -> {ls1, ls2 : List lty} -> {l : lty} ->
  {t : (lty, Type)} -> (isElem : Elem (fst t) ls1) -> DeleteElem ls1 isElem ls2 -> DeleteLabelsPred (l :: ls2) ts1 ts2 ->
  DeleteLabelsPred (l :: ls1) (t :: ts1) ts2
fromIsProjectRightToDeleteLabelsPred_Lemma7 isElem delElem (DeleteFirstOfLabelList {tsAux=ts3} subDelAtLabelPred subDelLabelsPred) = 
  DeleteFirstOfLabelList {tsAux=ts3} subDelAtLabelPred (fromIsProjectRightToDeleteLabelsPred_Lemma6 isElem delElem subDelLabelsPred)
  
fromIsProjectRightToDeleteLabelsPred : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} ->
                                  {ls : List lty} -> IsProjectRight ls ts1 ts2 -> DeleteLabelsPred ls ts1 ts2                                 
fromIsProjectRightToDeleteLabelsPred IPR_EmptyLabels = EmptyLabelList
fromIsProjectRightToDeleteLabelsPred {ls=ls} IPR_EmptyVect = fromIsProjectRightToDeleteLabelsPred_Lemma1 ls
fromIsProjectRightToDeleteLabelsPred {ls=[]} (IPR_ProjLabelElem isElem delElem subPrjRight) = absurd $ noEmptyElem isElem
fromIsProjectRightToDeleteLabelsPred (IPR_ProjLabelElem {t=t} Here DeleteElemHere subPrjRight) = 
  let subDelLabelPred = fromIsProjectRightToDeleteLabelsPred subPrjRight
  in fromIsProjectRightToDeleteLabelsPred_Lemma5 subDelLabelPred {t=t}
fromIsProjectRightToDeleteLabelsPred {ls=(l::ls)} (IPR_ProjLabelElem (There isInThere) (DeleteElemThere delInThere) subPrjRight) = 
  let subDelLabelPred = fromIsProjectRightToDeleteLabelsPred subPrjRight
  in fromIsProjectRightToDeleteLabelsPred_Lemma7 isInThere delInThere subDelLabelPred
fromIsProjectRightToDeleteLabelsPred {ls=[]} (IPR_ProjLabelNotElem notElem subPrjRight) = 
  let subDelLabelPred = fromIsProjectRightToDeleteLabelsPred subPrjRight
      tsAreEqual = fromIsProjectRightToDeleteLabelsPred_Lemma2 subDelLabelPred
  in rewrite tsAreEqual in EmptyLabelList
fromIsProjectRightToDeleteLabelsPred {ls=(l::ls)} (IPR_ProjLabelNotElem notElem subPrjRight) = 
  let subDelLabelPred = fromIsProjectRightToDeleteLabelsPred subPrjRight
  in fromIsProjectRightToDeleteLabelsPred_Lemma4 notElem subDelLabelPred


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
    (ts2 ** (hListToRec {prf=isLabelSet2} hs2, fromIsProjectRightToDeleteLabelsPred prjRightRes))

-- Viejo

{-DeleteLabelsPred : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type
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
-}

-- *** hLeftUnion ***

-- Predicado que indica que la union por la izquierda de dos LabelList que son un set es equivalente a la tercera
{-data IsLeftUnion : DecEq lty => LabelList lty -> LabelList lty -> LabelList lty -> Type where
  RightIsEmpty : DecEq lty => IsLabelSet ts1 -> IsLeftUnion {lty=lty} ts1 [] ts1
  IsInLeft : DecEq lty => ElemLabel l ts1 -> Not (ElemLabel l ts2) -> IsLeftUnion ts1 ts2 tsRes ->
    IsLeftUnion {lty=lty} ts1 ((l,ty) :: ts2) tsRes
  IsNotInLeft : DecEq lty => Not (ElemLabel l ts1) -> Not (ElemLabel l ts2) -> IsLeftUnion ts1 ts2 tsRes ->
    IsLeftUnion {lty=lty} ts1 ((l,ty) :: ts2) (tsRes ++ [(l,ty)])-}
    
data IsLeftUnion : DecEq lty => LabelList lty -> LabelList lty -> LabelList lty -> Type where
  IsLeftUnionAppend : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> IsLabelSet ts1 -> IsLabelSet ts2 -> 
  DeleteLabelsPred (labelsOf ts1) ts2 ts3 -> IsLeftUnion ts1 ts2 (ts1 ++ ts3)

-- Lemas necesarios
ifDeleteLabelsThenAppendIsSetLemma_1_1 : DecEq lty => {ts1, ts2 : LabelList lty} -> {t : (lty,Type)} ->
  IsLabelSet (ts1 ++ (t :: ts2)) -> IsLabelSet (ts1 ++ ts2)
ifDeleteLabelsThenAppendIsSetLemma_1_1 {ts1=[]} (IsSetCons notElem isSet) = isSet
ifDeleteLabelsThenAppendIsSetLemma_1_1 {ts1=((l,ty) :: ts1)} (IsSetCons notElem isSet) = 
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_1_1 isSet
      (notInTs1, notInTs2Cons) = ifNotInAppendThenNotInNeither notElem
      notInTs2 = notElemInCons notInTs2Cons
      notInAppend = ifNotInEitherThenNotInAppend notInTs1 notInTs2
  in IsSetCons notInAppend subPrf

ifDeleteLabelsThenAppendIsSetLemma_1_2_1 : DecEq lty => {l1, l2 : lty} -> {ts1, ts2 : LabelList lty} -> 
  Not (ElemLabel l1 (ts1 ++ ((l2, ty2) :: ts2))) -> Not (ElemLabel l2 ts1) -> Not (Elem l2 (l1 :: labelsOf (ts1)))
ifDeleteLabelsThenAppendIsSetLemma_1_2_1 {ts1=ts1} {ts2=ts2} {l1=l1} {l2=l1} {ty2=ty2} notElemCons notL2InTs1 Here =
  let inCons = ifIsInOneThenIsInAppend {l=l1} {ts1=ts1} {ts2=(l1,ty2)::ts2} (Right Here)
  in notElemCons inCons
ifDeleteLabelsThenAppendIsSetLemma_1_2_1 notElemCons notL2InTs1 (There isThere) = notL2InTs1 isThere

ifDeleteLabelsThenAppendIsSetLemma_1_2 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} -> {ty : Type} ->
  IsLabelSet (ts1 ++ ((l,ty) :: ts2)) -> (Not (ElemLabel l ts1), Not (ElemLabel l ts2))  
ifDeleteLabelsThenAppendIsSetLemma_1_2 {ts1=[]} {l=l} {ty=ty} {ts2=ts2} (IsSetCons notElem subIsSet) = (noEmptyElem, notElem)
ifDeleteLabelsThenAppendIsSetLemma_1_2 {ts1=(l1,ty1) :: ts1} {l=l2} {ty=ty2} {ts2=ts2} (IsSetCons notElem subIsSet) = 
  let (notInTs1, notInTs2) = ifDeleteLabelsThenAppendIsSetLemma_1_2 subIsSet
  in (ifDeleteLabelsThenAppendIsSetLemma_1_2_1 notElem notInTs1, notInTs2)

ifDeleteLabelsThenAppendIsSetLemma_1_3 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} ->
  DeleteLabelAtPred l1 ts1 ts2 -> Not (ElemLabel l2 ts1) -> Not (ElemLabel l2 ts2)
ifDeleteLabelsThenAppendIsSetLemma_1_3 EmptyRecord notInTs1 inTs2 = notInTs1 inTs2
ifDeleteLabelsThenAppendIsSetLemma_1_3 IsElem notInTs1 inTs2 = notInTs1 $ There inTs2
ifDeleteLabelsThenAppendIsSetLemma_1_3 (IsNotElem notEqual subDelAt) notInTs1 Here = notInTs1 Here
ifDeleteLabelsThenAppendIsSetLemma_1_3 {l1=l1} {l2=l2} {ts1=((l3,ty3) :: ts1)} {ts2=((l3,ty3) :: ts2)} (IsNotElem notEqual subDelAt) notInTs1 (There inTs2) =
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_1_3 {l1=l1} {ts1=ts1} {ts2=ts2} subDelAt (notElemInCons notInTs1)
  in subPrf inTs2

ifDeleteLabelsThenAppendIsSetLemma_1_4_1 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} -> {ty2 : Type} ->
  Not (l1 = l2) -> Not (ElemLabel l1 (ts1 ++ ts2)) -> Not (ElemLabel l1 (ts1 ++ ((l2,ty2) :: ts2)))
ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {ts1=[]} notEqual notInAppend Here = notEqual Refl
ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {ts1=[]} notEqual notInAppend (There isThere) = notInAppend isThere
ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {l1=l1} {l2=l2} {ts1=(l1,ty3)::ts1} notEqual notInAppend Here = notInAppend Here
ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {l1=l1} {l2=l2} {ts1=(l3,ty3)::ts1} {ts2=ts2} {ty2=ty2} notEqual notInAppend (There isThere) = 
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {l1=l1} {l2=l2} {ts1=ts1} {ts2=ts2} {ty2=ty2} notEqual (notElemInCons notInAppend)
  in subPrf isThere

ifDeleteLabelsThenAppendIsSetLemma_1_4 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} -> {ty : Type} ->
  IsLabelSet (ts1 ++ ts2) -> Not (ElemLabel l ts1) -> Not (ElemLabel l ts2) -> IsLabelSet (ts1 ++ ((l,ty) :: ts2))
ifDeleteLabelsThenAppendIsSetLemma_1_4 {ts1=[]} isSet notInTs1 notInTs2 = IsSetCons notInTs2 isSet
ifDeleteLabelsThenAppendIsSetLemma_1_4 {l=l2} {ty=ty2} {ts1=(l1,ty1) :: ts1} {ts2=ts2} (IsSetCons notElem isSet) notInTs1 notInTs2 = 
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_1_4 {l=l2} {ty=ty2} isSet (notElemInCons notInTs1) notInTs2
      notEqual = symNot $ ifNotElemThenNotEqual notInTs1
      notElemCons = ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {l2=l2} {ty2=ty2} {l1=l1} {ts1=ts1} {ts2=ts2} notEqual notElem
  in IsSetCons notElemCons subPrf

ifDeleteLabelsThenAppendIsSetLemma_1 : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> {l : lty} -> DeleteLabelAtPred l ts2 ts3 ->
  IsLabelSet (ts1 ++ ts2) -> IsLabelSet (ts1 ++ ts3)
ifDeleteLabelsThenAppendIsSetLemma_1 EmptyRecord isSet = isSet
ifDeleteLabelsThenAppendIsSetLemma_1 {ts1=[]} IsElem (IsSetCons notElem isSet) = isSet
ifDeleteLabelsThenAppendIsSetLemma_1 {l=l} {ts1=((l1,ty1) :: ts1)} {ts3=ts3} IsElem (IsSetCons notElem isSet) =
  let (notInTs1, notInTs3Cons) = ifNotInAppendThenNotInNeither notElem
      notInTs3 = notElemInCons notInTs3Cons
      notInAppend = ifNotInEitherThenNotInAppend notInTs1 notInTs3
  in IsSetCons notInAppend (ifDeleteLabelsThenAppendIsSetLemma_1_1 {ts1=ts1} {ts2=ts3} isSet)
ifDeleteLabelsThenAppendIsSetLemma_1 {ts1=ts1} {ts2=((l2,ty2) :: ts2)} {ts3=((l2,ty2) :: ts3)} (IsNotElem notElem delAt) isSet = 
  let isSetAppend = ifDeleteLabelsThenAppendIsSetLemma_1_1 isSet
      subPrf = ifDeleteLabelsThenAppendIsSetLemma_1 {ts1=ts1} {ts2=ts2} {ts3=ts3} delAt isSetAppend
      (notInTs1, notInTs2) = ifDeleteLabelsThenAppendIsSetLemma_1_2 isSet {l=l2} {ty=ty2} {ts1=ts1} {ts2=ts2}
      notInTs3 = ifDeleteLabelsThenAppendIsSetLemma_1_3 delAt notInTs2
  in ifDeleteLabelsThenAppendIsSetLemma_1_4 subPrf notInTs1 notInTs3

ifDeleteLabelsThenAppendIsSetLemma_2 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  IsLabelSet ts1 -> DeleteLabelAtPred l ts1 ts2 -> Not (ElemLabel l ts2)
ifDeleteLabelsThenAppendIsSetLemma_2 isSet1 EmptyRecord elemLabel = noEmptyElem elemLabel
ifDeleteLabelsThenAppendIsSetLemma_2 (IsSetCons notElem isSet) IsElem elemLabel = notElem elemLabel
ifDeleteLabelsThenAppendIsSetLemma_2 (IsSetCons notElem isSet) (IsNotElem notEqual subDelAt) Here = notEqual Refl
ifDeleteLabelsThenAppendIsSetLemma_2 {l=l} (IsSetCons notElem isSet) (IsNotElem notEqual subDelAt) (There isThere) = 
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_2 {l=l} isSet subDelAt 
  in subPrf isThere

-- Lemma que indica que si se eliminan del 2ndo record los labels del 1ero, entonces agregar la resta al 1ero es un labelset
ifDeleteLabelsThenAppendIsSetLemma : DecEq lty => {ts1, ts2, tsDel : LabelList lty} -> IsLabelSet ts1 -> IsLabelSet ts2 -> 
  DeleteLabelsPred (labelsOf ts1) ts2 tsDel -> IsLabelSet (ts1 ++ tsDel)
ifDeleteLabelsThenAppendIsSetLemma {ts1=[]} isSet1 isSet2 EmptyLabelList = isSet2
ifDeleteLabelsThenAppendIsSetLemma {ts1=((l1,ty1) :: ts1)} {tsDel=tsDel} (IsSetCons notElem subIsSet1) isSet2 (DeleteFirstOfLabelList {tsAux=ts3} subDelAt subDel) =
  let
    subPrf = ifDeleteLabelsThenAppendIsSetLemma {ts1=ts1} subIsSet1 isSet2 subDel
    resIsSet = ifDeleteLabelsThenAppendIsSetLemma_1 {ts1=ts1} {ts2=ts3} {ts3=tsDel} subDelAt subPrf
    isSet3 = snd $ ifAppendIsSetThenEachIsToo subPrf
    isNotInTsDel = ifDeleteLabelsThenAppendIsSetLemma_2 isSet3 subDelAt
    isNotInAppend = ifNotInEitherThenNotInAppend notElem isNotInTsDel
  in IsSetCons isNotInAppend resIsSet
  
{-ifDeleteLabelsThenItIsLeftUnion_Lemma_1 : DecEq lty => {ts : LabelList lty} -> IsLabelSet ts -> IsLeftUnion [] ts ts 
ifDeleteLabelsThenItIsLeftUnion_Lemma_1 {ts=[]} isSet = RightIsEmpty IsSetNil
ifDeleteLabelsThenItIsLeftUnion_Lemma_1 {ts=(l,ty)::ts} (IsSetCons notLInTs isSet) = 
  let subPrf = ifDeleteLabelsThenItIsLeftUnion_Lemma_1 isSet
  in ?wadawdawdawd
  --in IsNotInLeft noEmptyElem notLInTs subPrf
-}

{-ifDeleteLabelsThenItIsSetUnion_Lemma_2_1_1 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} -> DeleteLabelAtPred l2 ts1 ts2 ->
  ElemLabel l1 ts2 -> Not (l1 = l2) -> ElemLabel l1 ts1
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1_1 EmptyRecord inTs2 l1NotEqL2 = inTs2
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1_1 IsElem inTs2 l1NotEqL2 = There inTs2
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1_1 (IsNotElem {tup=(l3,ty3)} l2NotEqL3 delAt) Here l1NotEqL2 = Here
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1_1 (IsNotElem {tup=(l3,ty3)} l2NotEqL3 delAt) (There inTs2) l1NotEqL2 = 
  let subPrf = ifDeleteLabelsThenItIsSetUnion_Lemma_2_1_1 delAt inTs2 l1NotEqL2
  in (There subPrf)

ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> {l : lty} -> DeleteLabelsPred (labelsOf ts1) ts2 ts3 -> Not (ElemLabel l ts1) -> ElemLabel l ts3 -> ElemLabel l ts2
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 {ts1=[]} EmptyLabelList notInTs1 inTs3 = inTs3
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 {l=l1} {ts1=(l2,ty2)::ts1} (DeleteFirstOfLabelList delAt delLabels) notInConsTs1 inTs3 =
  let notInTs1 = notElemInCons notInConsTs1
      l1NotEqL2 = ifNotElemThenNotEqual notInConsTs1
      inTsAux = ifDeleteLabelsThenItIsSetUnion_Lemma_2_1_1 delAt inTs3 l1NotEqL2
      subPrf = ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 delLabels notInTs1 inTsAux
  in subPrf -}

{-ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> DeleteLabelsPred (labelsOf ts1) [] ts2 ->
  DeleteLabelAtPred l ts2 ts3 -> ts3 = []
ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 {ts1=[]} EmptyLabelList EmptyRecord = Refl
ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 {ts1=[]} EmptyLabelList IsElem impossible
ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 {ts1=[]} EmptyLabelList (IsNotElem _ _) impossible
ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 {ts1=(l1,ty1)::ts1} {ts2=[]} (DeleteFirstOfLabelList _ _) EmptyRecord = Refl 
ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 {ts1=(l1,ty1)::ts1} {ts2=[]} (DeleteFirstOfLabelList _ _) IsElem impossible
ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 {ts1=(l1,ty1)::ts1} {ts2=[]} (DeleteFirstOfLabelList _ _) (IsNotElem _ _) impossible
ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 {ts1=(l1,ty1)::ts1} {ts2=(l2,ty2)::ts2} (DeleteFirstOfLabelList subDelAt delLabels) delAt = 
  let subPrf = ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 delLabels subDelAt
  in absurd $ consNotEqNil subPrf

ifDeleteLabelsThenItIsLeftUnion_Lemma_2_2 : DecEq lty => {ts1, ts2 : LabelList lty} -> ts2 = [] -> ts1 ++ [] = ts1 -> ts1 ++ ts2 = ts1
ifDeleteLabelsThenItIsLeftUnion_Lemma_2_2 {ts2=[]} Refl prf = prf

ifDeleteLabelsThenItIsLeftUnion_Lemma_2 : DecEq lty => {ts1, ts2, tsDel, tsAux : LabelList lty} -> {l1 : lty} -> Not (ElemLabel l1 ts1) ->
  IsLabelSet ts1 -> IsLabelSet ts2 -> DeleteLabelAtPred l1 tsAux tsDel -> DeleteLabelsPred (labelsOf ts1) ts2 tsAux ->
  IsLeftUnion ts1 ts2 (ts1 ++ tsAux) -> ElemLabel l1 tsAux -> IsLeftUnion ((l1, ty1) :: ts1) ts2 ((l1,ty1) :: (ts1 ++ tsDel))
ifDeleteLabelsThenItIsLeftUnion_Lemma_2 {ts1=ts1} {ts2=[]} notL1InTs1 isSet1 IsSetNil delAt delLabels isUnion l1InTsAux = 
  let tsDelIsNil = ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 delLabels delAt
      ts1AppendIsNil = appendNilRightNeutral ts1
      ts1AppendTsDelNeutral = ifDeleteLabelsThenItIsLeftUnion_Lemma_2_2 tsDelIsNil ts1AppendIsNil
  in rewrite ts1AppendTsDelNeutral in (RightIsEmpty (IsSetCons notL1InTs1 isSet1))
ifDeleteLabelsThenItIsLeftUnion_Lemma_2 {ts2=(l2,ty2)::ts2} notL1InTs1 isSet1 (IsSetCons notL2InTs2 isSet2) delAt delLabels isUnion l1InTsAux = 
  --IsInLeft ?Lemma_2_inTs1 ?Lemma_2_notInTs2 ?Lemma_2_isUnion
  ?ifDeleteLabelsThenItIsLeftUnion_Lemma_2_rhs
-}
{-ifDeleteLabelsThenItIsSetUnion_Lemma_3_1_1 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} -> DeleteLabelAtPred l2 ts1 ts2 ->
  Not (ElemLabel l1 ts2) -> Not (l1 = l2) -> Not (ElemLabel l1 ts1)
ifDeleteLabelsThenItIsSetUnion_Lemma_3_1_1 EmptyRecord notInTs2 l1NotEqL2 inTs1 = noEmptyElem inTs1
ifDeleteLabelsThenItIsSetUnion_Lemma_3_1_1 IsElem notInTs2 l1NotEqL2 Here = l1NotEqL2 Refl
ifDeleteLabelsThenItIsSetUnion_Lemma_3_1_1 IsElem notInTs2 l1NotEqL2 (There inTs2) = notInTs2 inTs2
ifDeleteLabelsThenItIsSetUnion_Lemma_3_1_1 (IsNotElem {tup=(l3,ty3)} l2NotEqL3 delAt) notInConsTs2 l1NotEqL2 Here = 
  let l1NotEqL3 = ifNotElemThenNotEqual notInConsTs2
  in l1NotEqL3 Refl
ifDeleteLabelsThenItIsSetUnion_Lemma_3_1_1 (IsNotElem {tup=(l3,ty3)} l2NotEqL3 delAt) notInConsTs2 l1NotEqL2 (There inTs1) = 
  let notInTs2 = notElemInCons notInConsTs2
      notInTs1 = ifDeleteLabelsThenItIsSetUnion_Lemma_3_1_1 delAt notInTs2 l1NotEqL2
  in notInTs1 inTs1

ifDeleteLabelsThenItIsSetUnion_Lemma_3_1 : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> {l : lty} -> DeleteLabelsPred (labelsOf ts1) ts2 ts3 -> Not (ElemLabel l ts1) -> Not (ElemLabel l ts3) -> Not (ElemLabel l ts2)
ifDeleteLabelsThenItIsSetUnion_Lemma_3_1 {ts1=[]} EmptyLabelList notInTs1 notInTs3 inTs2 = notInTs3 inTs2
ifDeleteLabelsThenItIsSetUnion_Lemma_3_1 {l=l1} {ts1=(l2,ty2)::ts1} (DeleteFirstOfLabelList delAt delLabels) notInConsTs1 notInTs3 inTs2 = 
  let notInTs1 = notElemInCons notInConsTs1
      l1NotEqL2 = ifNotElemThenNotEqual notInConsTs1
      notInTsAux = ifDeleteLabelsThenItIsSetUnion_Lemma_3_1_1 delAt notInTs3 l1NotEqL2
      subPrf = ifDeleteLabelsThenItIsSetUnion_Lemma_3_1 delLabels notInTs1 notInTsAux
  in subPrf inTs2 -}

{-ifDeleteLabelsThenItIsLeftUnion_Lemma_3 : DecEq lty => {ts1, ts2, tsDel, tsAux : LabelList lty} -> {l1 : lty} -> Not (ElemLabel l1 ts1) ->
  IsLabelSet ts1 -> IsLabelSet ts2 -> DeleteLabelAtPred l1 tsAux tsDel -> DeleteLabelsPred (labelsOf ts1) ts2 tsAux ->
  IsLeftUnion ts1 ts2 (ts1 ++ tsAux) -> Not (ElemLabel l1 tsAux) -> IsLeftUnion ((l1, ty1) :: ts1) ts2 ((l1,ty1) :: (ts1 ++ tsDel))
ifDeleteLabelsThenItIsLeftUnion_Lemma_3 {ts1=ts1} {ts2=[]} notL1InTs1 isSet1 IsSetNil delAt delLabels isUnion notL1InTsAux = 
  let tsDelIsNil = ifDeleteLabelsThenItIsLeftUnion_Lemma_2_1 delLabels delAt
      ts1AppendIsNil = appendNilRightNeutral ts1
      ts1AppendTsDelNeutral = ifDeleteLabelsThenItIsLeftUnion_Lemma_2_2 tsDelIsNil ts1AppendIsNil
  in rewrite ts1AppendTsDelNeutral in (RightIsEmpty (IsSetCons notL1InTs1 isSet1))
ifDeleteLabelsThenItIsLeftUnion_Lemma_3 {ts2=(l2,ty2)::ts2} notL1InTs1 isSet1 (IsSetCons notL2InTs2 isSet2) delAt delLabels isUnion notL1InTsAux = 
  --IsNotInLeft ?Lemma_3_notInTs1 ?Lemma_3_notInTs2 ?Lemma_3_isUnion
  ?ifDeleteLabelsThenItIsLeftUnion_Lemma_3_rhs
-}
-- Lemma que indica que si se eliminan del 2ndo record los labels del 1ero, entonces agregar la resta al 1ero equivale a la union de
-- ambos por la izquierda
{-ifDeleteLabelsThenItIsLeftUnion : DecEq lty => {ts1, ts2, tsDel : LabelList lty} -> IsLabelSet ts1 -> IsLabelSet ts2 -> 
  DeleteLabelsPred (labelsOf ts1) ts2 tsDel -> IsLeftUnion ts1 ts2 (ts1 ++ tsDel)
ifDeleteLabelsThenItIsLeftUnion {ts1=[]} isSet1 isSet2 EmptyLabelList = ifDeleteLabelsThenItIsLeftUnion_Lemma_1 isSet2
ifDeleteLabelsThenItIsLeftUnion {ts1=(l1,ty1)::ts1} {ts2=ts2} (IsSetCons notL1InTs1 isSet1) isSet2 (DeleteFirstOfLabelList {tsAux=tsAux} delAt delLabels) with (isElemLabel l1 tsAux)
  ifDeleteLabelsThenItIsLeftUnion {ts1=(l1,ty1)::ts1} {ts2=ts2} (IsSetCons notL1InTs1 isSet1) isSet2 (DeleteFirstOfLabelList {tsAux=tsAux} delAt delLabels) | Yes l1InTsAux =
    let subPrf = ifDeleteLabelsThenItIsLeftUnion {ts1=ts1} {ts2=ts2} {tsDel=tsAux} isSet1 isSet2 delLabels
    in ifDeleteLabelsThenItIsLeftUnion_Lemma_2 notL1InTs1 isSet1 isSet2 delAt delLabels subPrf l1InTsAux
  ifDeleteLabelsThenItIsLeftUnion {ts1=(l1,ty1)::ts1} {ts2=ts2} (IsSetCons notL1InTs1 isSet1) isSet2 (DeleteFirstOfLabelList {tsAux=tsAux} delAt delLabels) | No notL1InTsAux = 
    let subPrf = ifDeleteLabelsThenItIsLeftUnion {ts1=ts1} {ts2=ts2} {tsDel=tsAux} isSet1 isSet2 delLabels
    in ifDeleteLabelsThenItIsLeftUnion_Lemma_3 notL1InTs1 isSet1 isSet2 delAt delLabels subPrf notL1InTsAux-}
  
 
-- *-* Definicion de "hLeftUnion" de hackage *-*
hLeftUnion : DecEq lty => {ts1, ts2 : LabelList lty} -> Record ts1 -> Record ts2 -> 
   (tsRes : LabelList lty ** (Record tsRes, IsLeftUnion ts1 ts2 tsRes))
hLeftUnion {ts1=ts1} {ts2=ts2} rec1 rec2 = 
  let
    isSet1 = recLblIsSet rec1
    isSet2 = recLblIsSet rec2
    (tsDel ** (recDel, prfDel)) = hDeleteLabels (labelsOf ts1) rec2
    recRes = hAppend rec1 recDel (ifDeleteLabelsThenAppendIsSetLemma {ts1=ts1} {ts2=ts2} {tsDel=tsDel} isSet1 isSet2 prfDel)
   in
    (ts1 ++ tsDel ** (recRes, IsLeftUnionAppend isSet1 isSet2 prfDel))
--    (ts1 ++ tsDel ** (recRes, ifDeleteLabelsThenItIsLeftUnion {ts1=ts1} {ts2=ts2} {tsDel=tsDel} isLblSet1 isLblSet2 prfDel))
      

-- *** VIejo ***  
{-
ifDeleteLabelsThenItIsSetUnion_Lemma_1_1_1 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} -> DeleteLabelAtPred l2 ts1 ts2 ->
  ElemLabel l1 ts2 -> Not (l1 = l2) -> ElemLabel l1 ts1
ifDeleteLabelsThenItIsSetUnion_Lemma_1_1_1 EmptyRecord inTs2 l1NotEqL2 = inTs2
ifDeleteLabelsThenItIsSetUnion_Lemma_1_1_1 IsElem inTs2 l1NotEqL2 = There inTs2
ifDeleteLabelsThenItIsSetUnion_Lemma_1_1_1 (IsNotElem {tup=(l3,ty3)} l2NotEqL3 delAt) Here l1NotEqL2 = Here
ifDeleteLabelsThenItIsSetUnion_Lemma_1_1_1 (IsNotElem {tup=(l3,ty3)} l2NotEqL3 delAt) (There inTs2) l1NotEqL2 = 
  let subPrf = ifDeleteLabelsThenItIsSetUnion_Lemma_1_1_1 delAt inTs2 l1NotEqL2
  in (There subPrf)

ifDeleteLabelsThenItIsSetUnion_Lemma_1_1 : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> {l : lty} -> DeleteLabelsPred (labelsOf ts1) ts2 ts3 -> Not (ElemLabel l ts1) -> ElemLabel l ts3 -> ElemLabel l ts2
ifDeleteLabelsThenItIsSetUnion_Lemma_1_1 {ts1=[]} EmptyLabelList notInTs1 inTs3 = inTs3
ifDeleteLabelsThenItIsSetUnion_Lemma_1_1 {l=l1} {ts1=(l2,ty2)::ts1} (DeleteFirstOfLabelList delAt delLabels) notInConsTs1 inTs3 =
  let notInTs1 = notElemInCons notInConsTs1
      l1NotEqL2 = ifNotElemThenNotEqual notInConsTs1
      inTsAux = ifDeleteLabelsThenItIsSetUnion_Lemma_1_1_1 delAt inTs3 l1NotEqL2
      subPrf = ifDeleteLabelsThenItIsSetUnion_Lemma_1_1 delLabels notInTs1 inTsAux
  in subPrf
  
ifDeleteLabelsThenItIsSetUnion_Lemma_1_2 : DecEq lty => {ts1, ts2, ts3, tsDel : LabelList lty} -> {l : lty} -> {ty : Type} ->
  DeleteLabelAtPred l ts3 tsDel -> IsSetUnion ts1 ts2 (ts1 ++ ts3) -> Not (ElemLabel l ts1) -> ElemLabel l ts3 -> 
  IsSetUnion ts1 ts2 ((l, ty) :: (ts1 ++ tsDel))
ifDeleteLabelsThenItIsSetUnion_Lemma_1_2 EmptyRecord isUnion isNotInTs1 isInTs3 = ?wat1
ifDeleteLabelsThenItIsSetUnion_Lemma_1_2 IsElem isUnion isNotInTs1 isInTs3 = ?wat2
ifDeleteLabelsThenItIsSetUnion_Lemma_1_2 {l=l1} (IsNotElem {tup=(l2,ty2)} l1NotEqL2 delAt) isUnion isNotInTs1 isInTs3 = ?wat3

ifDeleteLabelsThenItIsSetUnion_Lemma_1 : DecEq lty => {ts1, ts2, tsDel, tsAux : LabelList lty} -> {l : lty} -> {ty : Type} -> 
  Not (ElemLabel l ts1) -> IsLabelSet ts1 -> IsLabelSet ts2 -> DeleteLabelAtPred l tsAux tsDel -> 
  DeleteLabelsPred (labelsOf ts1) ts2 tsAux -> IsSetUnion ts1 ts2 (ts1 ++ tsAux) -> ElemLabel l tsAux -> 
  IsSetUnion ((l, ty) :: ts1) ts2 ((l, ty) :: (ts1 ++ tsDel))
ifDeleteLabelsThenItIsSetUnion_Lemma_1 {ty=ty} notInTs1 isSet1 isSet2 delAt delLabels isUnion inTsAux =
  let inTs2 = ifDeleteLabelsThenItIsSetUnion_Lemma_1_1 delLabels notInTs1 inTsAux
      isAppendUnion = ifDeleteLabelsThenItIsSetUnion_Lemma_1_2 {ty=ty} delAt isUnion notInTs1 inTsAux
  --in IsInRight inTs2 notInTs1 isAppendUnion
  in ?ifDeleteLabelsThenItIsSetUnion_Lemma_DAWDAWDW

ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} -> DeleteLabelAtPred l ts1 ts2 -> Not (ElemLabel l ts1) -> ts1 = ts2
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 EmptyRecord notInTs1 = Refl
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 IsElem notInTs1 = absurd $ notInTs1 Here
ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 {l=l1} (IsNotElem {tup=(l2,ty2)} l1NotEqL2 delAt) notInConsTs1 = 
  let notInTs1 = notElemInCons notInConsTs1
      ts1EqTs2 = ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 delAt notInTs1
  in cong ts1EqTs2

ifDeleteLabelsThenItIsSetUnion_Lemma_2_2_1 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} -> DeleteLabelAtPred l2 ts1 ts2 ->
  Not (ElemLabel l1 ts2) -> Not (l1 = l2) -> Not (ElemLabel l1 ts1)
ifDeleteLabelsThenItIsSetUnion_Lemma_2_2_1 EmptyRecord notInTs2 l1NotEqL2 inTs1 = noEmptyElem inTs1
ifDeleteLabelsThenItIsSetUnion_Lemma_2_2_1 IsElem notInTs2 l1NotEqL2 Here = l1NotEqL2 Refl
ifDeleteLabelsThenItIsSetUnion_Lemma_2_2_1 IsElem notInTs2 l1NotEqL2 (There inTs2) = notInTs2 inTs2
ifDeleteLabelsThenItIsSetUnion_Lemma_2_2_1 (IsNotElem {tup=(l3,ty3)} l2NotEqL3 delAt) notInConsTs2 l1NotEqL2 Here = 
  let l1NotEqL3 = ifNotElemThenNotEqual notInConsTs2
  in l1NotEqL3 Refl
ifDeleteLabelsThenItIsSetUnion_Lemma_2_2_1 (IsNotElem {tup=(l3,ty3)} l2NotEqL3 delAt) notInConsTs2 l1NotEqL2 (There inTs1) = 
  let notInTs2 = notElemInCons notInConsTs2
      notInTs1 = ifDeleteLabelsThenItIsSetUnion_Lemma_2_2_1 delAt notInTs2 l1NotEqL2
  in notInTs1 inTs1

ifDeleteLabelsThenItIsSetUnion_Lemma_2_2 : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> {l : lty} -> DeleteLabelsPred (labelsOf ts1) ts2 ts3 -> Not (ElemLabel l ts1) -> Not (ElemLabel l ts3) -> Not (ElemLabel l ts2)
ifDeleteLabelsThenItIsSetUnion_Lemma_2_2 {ts1=[]} EmptyLabelList notInTs1 notInTs3 inTs2 = notInTs3 inTs2
ifDeleteLabelsThenItIsSetUnion_Lemma_2_2 {l=l1} {ts1=(l2,ty2)::ts1} (DeleteFirstOfLabelList delAt delLabels) notInConsTs1 notInTs3 inTs2 = 
  let notInTs1 = notElemInCons notInConsTs1
      l1NotEqL2 = ifNotElemThenNotEqual notInConsTs1
      notInTsAux = ifDeleteLabelsThenItIsSetUnion_Lemma_2_2_1 delAt notInTs3 l1NotEqL2
      subPrf = ifDeleteLabelsThenItIsSetUnion_Lemma_2_2 delLabels notInTs1 notInTsAux
  in subPrf inTs2

ifDeleteLabelsThenItIsSetUnion_Lemma_2 : DecEq lty => {ts1, ts2, tsDel, tsAux : LabelList lty} -> {l1 : lty} -> Not (ElemLabel l1 ts1) ->
  IsLabelSet ts1 -> IsLabelSet ts2 -> DeleteLabelAtPred l1 tsAux tsDel -> DeleteLabelsPred (labelsOf ts1) ts2 tsAux -> 
  IsSetUnion ts1 ts2 (ts1 ++ tsAux) -> Not (ElemLabel l1 tsAux) -> IsSetUnion ((l1, ty1) :: ts1) ts2 ((l1, ty1) :: ts1 ++ tsDel)
ifDeleteLabelsThenItIsSetUnion_Lemma_2 {ts1=ts1} {ts2=ts2} {tsDel=tsDel} {tsAux=tsAux} {l1=l1} notInTs1 isSet1 isSet2 delAt delLabels isUnion notInTsAux = 
  let notInTs2 = ifDeleteLabelsThenItIsSetUnion_Lemma_2_2 delLabels notInTs1 notInTsAux
      tsAreEquals = ifDeleteLabelsThenItIsSetUnion_Lemma_2_1 delAt notInTsAux
  in rewrite (sym tsAreEquals) in IsNotInRight notInTs2 notInTs1 isUnion
  
-- Lemma que indica que si se eliminan del 2ndo record los labels del 1ero, entonces agregar la resta al 1ero equivale a la union de
-- ambos
ifDeleteLabelsThenItIsSetUnion : DecEq lty => {ts1, ts2, tsDel : LabelList lty} -> IsLabelSet ts1 -> IsLabelSet ts2 -> 
  DeleteLabelsPred (labelsOf ts1) ts2 tsDel -> IsSetUnion ts1 ts2 (ts1 ++ tsDel)
ifDeleteLabelsThenItIsSetUnion {ts1=[]} isSet1 isSet2 EmptyLabelList = LeftIsEmpty isSet2
ifDeleteLabelsThenItIsSetUnion {ts1=((l1,ty1) :: ts1)} {ts2=ts2} {tsDel=tsDel} (IsSetCons notElem isSet1) isSet2 (DeleteFirstOfLabelList {tsAux=tsAux} delAt delLabels) with (isElemLabel l1 tsAux)  
  ifDeleteLabelsThenItIsSetUnion {ts1=((l1,ty1) :: ts1)} {ts2=ts2} {tsDel=tsDel} (IsSetCons notElem isSet1) isSet2 (DeleteFirstOfLabelList {tsAux=tsAux} delAt delLabels) | Yes l1InTsAux =
    let subPrf = ifDeleteLabelsThenItIsSetUnion {ts1=ts1} {ts2=ts2} {tsDel=tsAux} isSet1 isSet2 delLabels
    in ifDeleteLabelsThenItIsSetUnion_Lemma_1 notElem isSet1 isSet2 delAt delLabels subPrf l1InTsAux
  ifDeleteLabelsThenItIsSetUnion {ts1=((l1,ty1) :: ts1)} {ts2=ts2} {tsDel=tsDel} (IsSetCons notElem isSet1) isSet2 (DeleteFirstOfLabelList {tsAux=tsAux} delAt delLabels) | No notL1InTsAux = 
    let subPrf = ifDeleteLabelsThenItIsSetUnion {ts1=ts1} {ts2=ts2} {tsDel=tsAux} isSet1 isSet2 delLabels
    in ifDeleteLabelsThenItIsSetUnion_Lemma_2 notElem isSet1 isSet2 delAt delLabels subPrf notL1InTsAux
-}
