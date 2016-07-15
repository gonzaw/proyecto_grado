{-

  Definición de Records Extensibles en Idris.
  
  Se toma inspiración de HList de Haskell
  Paper: http://okmij.org/ftp/Haskell/HList-ext.pdf
  Hackage: https://hackage.haskell.org/package/HList
  
-}

module Extensible_Records

import Data.List

-- Todas las funciones deben ser totales
%default total

-- Se exportan todas las definiciones y funciones
%access export

-- *** Propiedades de igualdad ***

-- Propiedad simétrica de la igualdad para el Not
symNot : Not (x = y) -> Not (y = x)
symNot notEqual Refl = notEqual Refl

-- *** Propiedades de List ***

-- Una lista vacía no puede ser igual a una lista con un elemento
consNotEqNil : {xs : List t} -> Not (x :: xs = [])
consNotEqNil Refl impossible

-- Nada puede pertenecer a una lista vacía
noEmptyElem : Not (Elem x [])
noEmptyElem Here impossible

-- *** Propiedades de Elem (de List) ***

-- Si un elemento no pertenece a una lista, no pertenece al tail de esa lista tampoco
notElemInCons : Not (Elem x (y :: ys)) -> Not (Elem x ys)
notElemInCons notElemCons elemTail = notElemCons $ There elemTail

-- Si un elemento no pertenece a una lista, no es igual al primer elemento de ésta
ifNotElemThenNotEqual : Not (Elem x (y :: ys)) -> Not (x = y)
ifNotElemThenNotEqual notElemCons equal = notElemCons $ rewrite equal in Here


-- *** IsSet - Predicado de conjunto ***
-- Predicado que indica que una lista es un conjunto, i.e no tiene elementos repetidos
data IsSet : List t -> Type where
  IsSetNil : IsSet []
  IsSetCons : Not (Elem x xs) -> IsSet xs -> IsSet (x :: xs)
    
-- Dada una prueba que una lista no tiene repetidos, retorna la prueba de que su primer elemento no pertenece al resto    
ifSetThenNotElemFirst : IsSet (x :: xs) -> Not (Elem x xs)
ifSetThenNotElemFirst (IsSetCons notXIsInXs  _) = notXIsInXs
  
-- Dada una prueba que un cons de una lista es un conjunto, retorna la prueba de que el tail es un conjunto
ifSetThenRestIsSet : IsSet (x :: xs) -> IsSet xs
ifSetThenRestIsSet (IsSetCons _ xsIsSet) = xsIsSet

-- Dada una prueba de que una lista no es un conjunto, retorna una prueba que cualquier cons de tal lista no es un conjunto
ifNotSetHereThenNeitherThere : Not (IsSet xs) -> Not (IsSet (x :: xs))
ifNotSetHereThenNeitherThere notXsIsSet (IsSetCons xIsInXs xsIsSet) = notXsIsSet xsIsSet  
  
-- Dada una prueba de que un valor pertenece a una lista, entonces este elemento agregado a la lista no es un conjunto
ifIsElemThenConsIsNotSet : Elem x xs -> Not (IsSet (x :: xs))      
ifIsElemThenConsIsNotSet xIsInXs (IsSetCons notXIsInXs xsIsSet) = notXIsInXs xIsInXs
  
-- Función de decisión que indica si una lista es un conjunto o no
isSet : DecEq t => (xs : List t) -> Dec (IsSet xs)
isSet [] = Yes IsSetNil
isSet (x :: xs) with (isSet xs)
  isSet (x :: xs) | No notXsIsSet = No $ ifNotSetHereThenNeitherThere notXsIsSet
  isSet (x :: xs) | Yes xsIsSet with (isElem x xs)
    isSet (x :: xs) | Yes xsIsSet | No notXInXs = Yes $ IsSetCons notXInXs xsIsSet
    isSet (x :: xs) | Yes xsIsSet | Yes xInXs = No $ ifIsElemThenConsIsNotSet xInXs
   
   
-- ** Listas heterogéneas con labels **

-- Vector de labels y tipos
LabelList : Type -> Type
LabelList lty = List (lty, Type)

-- Lista heterogénea
data HList : LabelList lty -> Type where
  Nil : HList []
  (::) : {l : lty} -> (val : t) -> HList ts -> HList ((l,t) :: ts)
 
-- Obtiene los labels de una LabelList
labelsOf : LabelList lty -> List lty
labelsOf = map fst

-- Alternativa de IsSet, para listas de labels+tipos
IsLabelSet : LabelList lty -> Type
IsLabelSet ts = IsSet (labelsOf ts)  

-- Alternativa de isSet, para listas de labels+tipos
isLabelSet : DecEq lty => (ts : LabelList lty) -> Dec (IsLabelSet ts)
isLabelSet ts = isSet (labelsOf ts)

-- Predicado que indica que un label pertenece a un vector de labels+tipos
ElemLabel : lty -> LabelList lty -> Type
ElemLabel l ts = Elem l (labelsOf ts)

-- Nota: Utilizar "Dec (ElemLabel l ts)" no typechequea por algún motivo
isElemLabel : DecEq lty => (l : lty) -> (ts : LabelList lty) -> Dec (Elem l (labelsOf ts))
isElemLabel l ts = isElem l (labelsOf ts)

-- *** Records extensibles ***

-- Record que contiene una lista heterogénea, y una prueba de que sus labels no son repetidos
data Record : LabelList lty -> Type where
  MkRecord : IsLabelSet ts -> HList ts -> Record ts
       
-- Transforma un record en una lista heterogenea ("unlabeled" en HList de Haskell)
recToHList : Record ts -> HList ts
recToHList (MkRecord _ hs) = hs

-- Dado un record retorna la prueba de que sus labels son un conjunto
recLblIsSet : Record ts -> IsLabelSet ts
recLblIsSet (MkRecord lsIsSet _ ) = lsIsSet       
       
-- Record vacio       
emptyRec : Record []
emptyRec = MkRecord IsSetNil {ts=[]} [] 
        
-- Dado una lista heterogénea y una prueba de que sus labels son un conjunto, crea un record ("hListRecord" en HList de Haskell)
hListToRec : DecEq lty => {ts : LabelList lty} -> {prf : IsLabelSet ts} -> HList ts -> Record ts
hListToRec {prf} hs = MkRecord prf hs

-- Dado un record, un label y un valor, extiende el record con ese valor ("hExtend" en HList de Haskell)
consRec : DecEq lty => {ts : LabelList lty} -> {t : Type} -> 
  (l : lty) -> (val : t)->  Record ts -> {notElem : Not (ElemLabel l ts)} -> Record ((l,t) :: ts)
consRec l val (MkRecord subLabelSet hs) {notElem} = MkRecord (IsSetCons notElem subLabelSet) (val :: hs)


-- Tipo que representa un tipo o top ("()") segun si se cumple una condicion o no
-- Es utilizado para forzar la unificación de ese tipo si la condición se cumple, o unificar contra top y crear un error de compilación
-- en caso de que no se cumpla la condición
TypeOrUnit : Dec p -> Type -> Type
TypeOrUnit (Yes prf) res = res
TypeOrUnit (No _) _ = ()

-- Dada una condición construye un tipo, o si falla la condición retorna top ("()")
mkTypeOrUnit : (d : Dec p) -> (cnst : p -> res) -> TypeOrUnit d res
mkTypeOrUnit (Yes prf) cnst = cnst prf
mkTypeOrUnit (No _) _ = ()

-- Tipo que representa un Record o top ("()") (i.e una falla)
RecordOrUnit : DecEq lty => LabelList lty -> Type
RecordOrUnit ts = TypeOrUnit (isLabelSet ts) (Record ts)
   
-- "consRec" donde la prueba de labels no repetidos es calculada automáticamente      
consRecAuto : DecEq lty => {ts : LabelList lty} -> {t : Type} -> (l : lty) -> (val : t) -> Record ts -> RecordOrUnit ((l,t) :: ts)
consRecAuto {ts} {t} l val (MkRecord tsIsLabelSet hs) = mkTypeOrUnit (isLabelSet ((l, t) :: ts)) (\isLabelSet => MkRecord isLabelSet (val :: hs))
    
-- "hListToRecAuto" donde la prueba de labels no repetidos es calculada automáticamente
hListToRecAuto : DecEq lty => (ts : LabelList lty) -> HList ts -> RecordOrUnit ts
hListToRecAuto ts hs = mkTypeOrUnit (isLabelSet ts) (\tsIsSet => MkRecord tsIsSet hs) 
        
        
-- *** hProjectByLabels ***                     
                                    
-- Predicado que indica que una lista es el resultado de eliminar un elemento de otra lista
data DeleteElemPred : (xs : List t) -> Elem x xs -> List t -> Type where
  DeleteElemPredHere : DeleteElemPred (x :: xs) Here xs
  DeleteElemPredThere : {isThere : Elem y xs} -> DeleteElemPred xs isThere ys -> DeleteElemPred (x :: xs) (There isThere) (x :: ys)

isDeleteElemPred_Lemma_1 : DecEq t => {xs, res : List t} -> Not (xs = res) -> Not (DeleteElemPred (x :: xs) Here res)
isDeleteElemPred_Lemma_1 notEq DeleteElemPredHere = notEq Refl

isDeleteElemPred_Lemma_2 : DecEq t => {xs : List t} -> {isThere : Elem y xs} -> Not (DeleteElemPred (x :: xs) (There isThere) [])
isDeleteElemPred_Lemma_2 (DeleteElemPredThere _) impossible

isDeleteElemPred_Lemma_3 : DecEq t => {xs1, xs2 : List t} -> {isThere : Elem y xs1} -> Not (x1 = x2) ->
  Not (DeleteElemPred (x1 :: xs1) (There isThere) (x2 :: xs2))
isDeleteElemPred_Lemma_3 notEq (DeleteElemPredThere _) = notEq Refl

isDeleteElemPred_Lemma_4 : DecEq t => {xs, ys : List t} -> {isThere : Elem y xs} -> Not (DeleteElemPred xs isThere ys) ->
  Not (DeleteElemPred (x :: xs) (There isThere) (x :: ys))
isDeleteElemPred_Lemma_4 notSubDel (DeleteElemPredThere subDel) = notSubDel subDel

-- Función de decisión de DeleteElemPred
isDeleteElemPred : DecEq t => (xs : List t) -> (isElem : Elem x xs) -> (res : List t) -> Dec (DeleteElemPred xs isElem res)
isDeleteElemPred [] isElem res = absurd $ noEmptyElem isElem
isDeleteElemPred (x :: xs) Here res with (decEq xs res)
  isDeleteElemPred (x :: xs) Here xs | Yes Refl = Yes DeleteElemPredHere
  isDeleteElemPred (x :: xs) Here res | No notXsEqRes = No (isDeleteElemPred_Lemma_1 notXsEqRes)
isDeleteElemPred (x1 :: xs) (There {x=x2} isThere) [] = No (isDeleteElemPred_Lemma_2 {isThere=isThere} {x=x1} {xs=xs} {y=x2})
isDeleteElemPred (x1 :: xs) (There {x=x2} isThere) (y::ys) with (decEq x1 y)
  isDeleteElemPred (x1 :: xs) (There {x=x2} isThere) (x1::ys) | Yes Refl with (isDeleteElemPred xs isThere ys)
    isDeleteElemPred (x1 :: xs) (There {x=x2} isThere) (x1::ys) | Yes Refl | Yes subDel = Yes (DeleteElemPredThere subDel)
    isDeleteElemPred (x1 :: xs) (There {x=x2} isThere) (x1::ys) | Yes Refl | No notSubDel = No (isDeleteElemPred_Lemma_4 notSubDel)
  isDeleteElemPred (x1 :: xs) (There {x=x2} isThere) (y::ys) | No notX1EqY = No (isDeleteElemPred_Lemma_3 notX1EqY)
  
-- Función que computa una lista eliminando un elemento de ella
deleteElem : (xs : List t) -> Elem x xs -> List t
deleteElem (x :: xs) Here = xs
deleteElem (x :: xs) (There inThere) =
  let rest = deleteElem xs inThere
  in x :: rest  
  
-- Dado "DeleteElemPred" se puede computar "deleteElem"
fromDeleteElemPredToComp : {xs1, xs2 : List t} -> {isElem : Elem x xs1} -> DeleteElemPred xs1 isElem xs2 -> xs2 = deleteElem xs1 isElem
fromDeleteElemPredToComp DeleteElemPredHere = Refl
fromDeleteElemPredToComp (DeleteElemPredThere isDelElem) = 
  let subPrf = fromDeleteElemPredToComp isDelElem
  in rewrite subPrf in Refl

-- Dada la computación de "deleteElem" de puede crear una prueba de "DeleteElemPred"
fromCompToDeleteElemPred : (xs : List t) -> (isElem : Elem x xs) -> DeleteElemPred xs isElem (deleteElem xs isElem)
fromCompToDeleteElemPred (x :: xs) Here = DeleteElemPredHere
fromCompToDeleteElemPred (x :: xs) (There inThere) =
  let subPrf = fromCompToDeleteElemPred xs inThere
  in DeleteElemPredThere subPrf
      
-- Predicado que indica que la proyección izquierda de un hProjectByLabels es efectivamente tal proyección    
data IsProjectLeft : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type where
  IPL_EmptyLabels : DecEq lty => IsProjectLeft {lty} [] ts []
  IPL_EmptyVect : DecEq lty => IsProjectLeft {lty} ls [] []
  IPL_ProjLabelElem : DecEq lty => (isElem : Elem l ls) -> DeleteElemPred ls isElem lsNew ->
                      IsProjectLeft {lty} lsNew ts res1 -> IsProjectLeft ls ((l,ty) :: ts) ((l,ty) :: res1)      
  IPL_ProjLabelNotElem : DecEq lty => Not (Elem l ls) -> IsProjectLeft {lty} ls ts res1 -> 
                       IsProjectLeft ls ((l,ty) :: ts) res1

-- Predicado que indica que la proyección derecha de un hProjectByLabels es efectivamente tal proyección    
data IsProjectRight : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type where
  IPR_EmptyLabels : DecEq lty => IsProjectRight {lty} [] ts ts
  IPR_EmptyVect : DecEq lty => IsProjectRight {lty} ls [] []
  IPR_ProjLabelElem : DecEq lty => (isElem : Elem l ls) -> DeleteElemPred ls isElem lsNew ->
                      IsProjectRight {lty} lsNew ts res1 -> IsProjectRight ls ((l,ty) :: ts) res1      
  IPR_ProjLabelNotElem : DecEq lty => Not (Elem l ls) -> IsProjectRight {lty} ls ts res1 -> 
                       IsProjectRight ls ((l,ty) :: ts) ((l,ty) :: res1)
  
-- Función que dada una prueba de que un elemento pertenece a una lista, retorna la lista sin el elemento y una prueba de que 
-- éste fue eliminado
deleteElemPred : {x : t} -> (xs : List t) -> (elem : Elem x xs) -> (res : List t ** DeleteElemPred xs elem res)
deleteElemPred (x :: xs) Here = (xs ** DeleteElemPredHere)
deleteElemPred (x :: xs) (There xInThere) =
  let (subDel ** subPrf) = deleteElemPred xs xInThere
  in (x :: subDel ** DeleteElemPredThere subPrf)
          
-- hProjectByLabels que también devuelve una prueba de que los vectores son actualmente proyecciones izquierda y derecha para un HList
-- Este hProjectByLabels retorna ambas listas: La de proyecciones y la resultante      
hProjectByLabelsHList : DecEq lty => {ts : LabelList lty} -> (ls : List lty) -> HList ts ->     
  ((ls1 : LabelList lty ** (HList ls1, IsProjectLeft ls ts ls1)),
  (ls2 : LabelList lty ** (HList ls2, IsProjectRight ls ts ls2)))
hProjectByLabelsHList [] {ts} hs = 
                   (([] ** ([], IPL_EmptyLabels)),
                   (ts ** (hs, IPR_EmptyLabels)))
hProjectByLabelsHList _ [] =
                   (([] ** ([], IPL_EmptyVect)),
                   ([] ** ([], IPR_EmptyVect)))
hProjectByLabelsHList {lty} ls ((::) {l=l2} {t} {ts=ts2} val hs) =
  case (isElem l2 ls) of
    Yes l2InLs =>
      let
        (lsNew ** isDelElem) = deleteElemPred ls l2InLs
        ((subInLs ** (subInHs, subPrjLeft)), (subOutLs ** (subOutHs, subPrjRight))) =
          hProjectByLabelsHList {lty=lty} {ts=ts2} lsNew hs
        rPrjRight = IPR_ProjLabelElem {l=l2} {ty=t} {ts=ts2} {res1=subOutLs} l2InLs isDelElem subPrjRight
        rPrjLeft = IPL_ProjLabelElem {l=l2} {ty=t} {ts=ts2} {res1=subInLs} l2InLs isDelElem subPrjLeft
        rRight = (subOutLs ** (subOutHs, rPrjRight))
        rLeft = ((l2,t) :: subInLs ** ((::) {l=l2} val subInHs, rPrjLeft))
       in
         (rLeft, rRight)
    No notL2InLs =>
      let
        ((subInLs ** (subInHs, subPrjLeft)), (subOutLs ** (subOutHs, subPrjRight))) =
          hProjectByLabelsHList {lty=lty} {ts=ts2} ls hs
        rPrjLeft = IPL_ProjLabelNotElem {l=l2} {ty=t} {ts=ts2} {res1=subInLs} notL2InLs subPrjLeft
        rPrjRight = IPR_ProjLabelNotElem {l=l2} {ty=t} {ts=ts2} {res1=subOutLs} notL2InLs subPrjRight
        rLeft = (subInLs ** (subInHs, rPrjLeft))
        rRight = ((l2,t) :: subOutLs ** ((::) {l=l2} val subOutHs, rPrjRight))
      in
        (rLeft, rRight)
    
-- Dada una prueba de que un elemento no pertenece a un cons de una lista, divide tal prueba en sus dos componentes
notElem_Lemma1 : Not (Elem x (y :: xs)) -> (Not (Elem x xs), Not (x = y))
notElem_Lemma1 notElemCons = (notElem_prf, notEq_prf)
  where
    notElem_prf isElem = notElemCons $ There isElem
    notEq_prf isEq = notElemCons $ rewrite isEq in Here
    
-- Dada una prueba de que un elemento no pertenece a una lista, y no es igual a otro, se obtiene la prueba de que éste no pertenece al cons
-- Es isomorfo al lemma anterior
notElem_Lemma2 : Not (Elem x xs) -> Not (x = y) -> Not (Elem x (y :: xs))
notElem_Lemma2 notElem notEq Here = notEq Refl
notElem_Lemma2 notElem notEq (There isElem) = notElem isElem 
    
-- Prueba de que dada una proyección por la derecha, si un label no pertenece a la lista inicial, entonces éste tampoco pertenece al
-- resultante    
hProjectByLabelsRightIsSet_Lemma1 : DecEq lty => {ls : List lty} -> {ts1, ts2 : LabelList lty} ->
  IsProjectRight ls ts1 ts2 -> Not (ElemLabel l ts1) -> Not (ElemLabel l ts2)
hProjectByLabelsRightIsSet_Lemma1 IPR_EmptyLabels notElem = notElem
hProjectByLabelsRightIsSet_Lemma1 IPR_EmptyVect notElem = notElem
hProjectByLabelsRightIsSet_Lemma1 (IPR_ProjLabelElem isElem delLs subPrjRight) notElem = 
  let
    (notElemSub, notEq) = notElem_Lemma1 notElem
    notIsElemRec = hProjectByLabelsRightIsSet_Lemma1 subPrjRight notElemSub
  in notIsElemRec
hProjectByLabelsRightIsSet_Lemma1 (IPR_ProjLabelNotElem subNotElem subPrjRight) notElem = 
  let
    (notElemSub, notEq) = notElem_Lemma1 notElem
    notIsElemRec = hProjectByLabelsRightIsSet_Lemma1 subPrjRight notElemSub
  in notElem_Lemma2 notIsElemRec notEq

-- Dada una proyección por la izquierda, si un label no pertenece a la lista inicial, tampoco pertenece al resultante      
hProjectByLabelsLeftIsSet_Lemma1 : DecEq lty => {ls : List lty} -> {ts1, ts2 : LabelList lty} ->
  IsProjectLeft ls ts1 ts2 -> Not (ElemLabel l ts1) -> Not (ElemLabel l ts2)
hProjectByLabelsLeftIsSet_Lemma1 IPL_EmptyLabels notElem = noEmptyElem
hProjectByLabelsLeftIsSet_Lemma1 IPL_EmptyVect notElem = notElem
hProjectByLabelsLeftIsSet_Lemma1 (IPL_ProjLabelElem isElem delElem subPrjLeft) notElem = 
  let
    (notElemSub, notEq) = notElem_Lemma1 notElem
    notIsElemRec = hProjectByLabelsLeftIsSet_Lemma1 subPrjLeft notElemSub
  in notElem_Lemma2 notIsElemRec notEq  
hProjectByLabelsLeftIsSet_Lemma1 (IPL_ProjLabelNotElem subNotElem subPrjLeft) notElem =
  let
    (notElemSub, notEq) = notElem_Lemma1 notElem
    notIsElemRec = hProjectByLabelsLeftIsSet_Lemma1 subPrjLeft notElemSub
  in notIsElemRec

-- Dada una proyección por la derecha, si la lista inicial es un conjunto, entonces la resultante tambien lo es
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

-- Dada una proyección por la izquierda, si la lista inicial es un conjunto, entonces la resultante tambien lo es    
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
-- Se necesita que la lista de labels no tenga repetidos
hProjectByLabelsWithPred : DecEq lty => {ts1 : LabelList lty} -> (ls : List lty) -> Record ts1 -> IsSet ls ->    
  (ts2 : LabelList lty ** (Record ts2, IsProjectLeft ls ts1 ts2))
hProjectByLabelsWithPred ls rec lsIsSet =
  let 
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
    (lsRes ** (hsRes, prjLeftRes)) = fst $ hProjectByLabelsHList ls hs
    isLabelSetRes = hProjectByLabelsLeftIsSet_Lemma2 prjLeftRes isLabelSet
  in (lsRes ** (hListToRec {prf=isLabelSetRes} hsRes, prjLeftRes)) 
  
-- Definición de hProjectByLabels que obtiene la prueba de "IsSet ls" de forma automática
hProjectByLabelsWithPredAuto : DecEq lty => {ts1 : LabelList lty} -> (ls : List lty) -> Record ts1 ->  
   TypeOrUnit (isSet ls) ((ts2 : LabelList lty ** (Record ts2, IsProjectLeft ls ts1 ts2)))
hProjectByLabelsWithPredAuto ls rec = mkTypeOrUnit (isSet ls) (\isSet => hProjectByLabelsWithPred ls rec isSet)
   
-- *-* hProjectByLabels con tipo computado *-*

-- Función que computa la proyeccion por izquierda de una LabelList dada una lista de labels
projectLeft : DecEq lty => List lty -> LabelList lty -> LabelList lty
projectLeft [] ts = []
projectLeft ls [] = []
projectLeft ls ((l,ty) :: ts) with (isElem l ls)
  projectLeft ls ((l,ty) :: ts) | Yes lIsInLs = 
    let delLFromLs = deleteElem ls lIsInLs
        rest = projectLeft delLFromLs ts
    in (l,ty) :: rest
  projectLeft ls ((l,ty) :: ts) | No _ = projectLeft ls ts

fromIsProjectLeftToComp_Lemma_1 : DecEq lty => {ls : List lty} -> [] = projectLeft ls []
fromIsProjectLeftToComp_Lemma_1 {ls=[]} = Refl
fromIsProjectLeftToComp_Lemma_1 {ls=(l::ls)} = Refl

fromIsProjectLeftToComp_Lemma_2 : DecEq lty => {ls : List lty} -> {ts : LabelList lty} -> Not (Elem l ls) -> 
  projectLeft ls ts = projectLeft ls ((l, ty) :: ts)
fromIsProjectLeftToComp_Lemma_2 {l} {ls=[]} {ts} lInLs = Refl
fromIsProjectLeftToComp_Lemma_2 {l=l1} {ls=(l2 :: ls)} {ts} notLInLs with (isElem l1 (l2 :: ls))
  fromIsProjectLeftToComp_Lemma_2 {l=l1} {ls=(l2 :: ls)} {ts} notLInLs | Yes lInLs = absurd $ notLInLs lInLs
  fromIsProjectLeftToComp_Lemma_2 {l=l1} {ls=(l2 :: ls)} {ts} notLInLs | No _  = Refl

fromIsProjectLeftToComp_Lemma_3_1 : DecEq lty => {ls : List lty} -> {elm1, elm2 : Elem l ls} -> IsSet ls -> 
  deleteElem ls elm1 = deleteElem ls elm2
fromIsProjectLeftToComp_Lemma_3_1 {ls=[]} {elm1} {elm2} _ = absurd $ noEmptyElem elm1
fromIsProjectLeftToComp_Lemma_3_1 {ls=(l :: ls)} {elm1=Here} {elm2=Here} (IsSetCons notLInLs lsIsSet) = Refl
fromIsProjectLeftToComp_Lemma_3_1 {ls=(l :: ls)} {elm1=(There elm1)} {elm2=Here} (IsSetCons notLInLs lsIsSet) = absurd $ notLInLs elm1
fromIsProjectLeftToComp_Lemma_3_1 {ls=(l :: ls)} {elm1=Here} {elm2=(There elm2)} (IsSetCons notLInLs lsIsSet) = absurd $ notLInLs elm2
fromIsProjectLeftToComp_Lemma_3_1 {ls=(l :: ls)} {elm1=(There elm1)} {elm2=(There elm2)} (IsSetCons notLInLs lsIsSet) = 
  let subPrf = fromIsProjectLeftToComp_Lemma_3_1 {elm1=elm1} {elm2=elm2} lsIsSet
  in cong subPrf

fromIsProjectLeftToComp_Lemma_3 : DecEq lty => {ls : List lty} -> {ts : LabelList lty} -> (lInLs : Elem l ls) -> IsSet ls ->
  projectLeft ls ((l, ty) :: ts) = (l, ty) :: (projectLeft (deleteElem ls lInLs) ts)
fromIsProjectLeftToComp_Lemma_3 {ls=[]} {ts} lInLs _ = absurd $ noEmptyElem lInLs
fromIsProjectLeftToComp_Lemma_3 {l=l1} {ls=(l2 :: ls)} {ts} lInLs lsIsSet with (isElem l1 (l2::ls))
  fromIsProjectLeftToComp_Lemma_3 {l=l1} {ls=(l2 :: ls)} {ts} lInLs lsIsSet | Yes lInLsAux =
    let delElemEq = fromIsProjectLeftToComp_Lemma_3_1 {ls=(l2 :: ls)} {elm1=lInLs} {elm2=lInLsAux} lsIsSet
    in rewrite delElemEq in Refl
  fromIsProjectLeftToComp_Lemma_3 {l=l1} {ls=(l2 :: ls)} {ts} lInLs lsIsSet | No notLInLs = absurd $ notLInLs lInLs

fromIsProjectLeftToComp_Lemma_4_1 : {elm : Elem l ls1} -> DeleteElemPred ls1 elm ls2 -> Not (Elem x ls1) -> Not (Elem x ls2)
fromIsProjectLeftToComp_Lemma_4_1 DeleteElemPredHere notXInLs1 xInLs2 = notElemInCons notXInLs1 xInLs2
fromIsProjectLeftToComp_Lemma_4_1 (DeleteElemPredThere delElemPred) notX1InLs1Cons Here = 
  let notX1EqX2 = ifNotElemThenNotEqual notX1InLs1Cons
  in notX1EqX2 Refl
fromIsProjectLeftToComp_Lemma_4_1 {x=x1} {ls1=(x2 :: ls1)} {ls2=(x2 :: ls2)} (DeleteElemPredThere delElemPred) notX1InLs1Cons (There x1InLs2) =
  let notX1InLs1 = notElemInCons notX1InLs1Cons
      notX1EqX2 = ifNotElemThenNotEqual notX1InLs1Cons
      subPrf = fromIsProjectLeftToComp_Lemma_4_1 delElemPred notX1InLs1
  in subPrf x1InLs2

fromIsProjectLeftToComp_Lemma_4 : {elm : Elem l ls1} -> DeleteElemPred ls1 elm ls2 -> IsSet ls1 -> IsSet ls2
fromIsProjectLeftToComp_Lemma_4 DeleteElemPredHere (IsSetCons _ isSet) = isSet
fromIsProjectLeftToComp_Lemma_4 (DeleteElemPredThere delElemPred) (IsSetCons notElem isSet) = 
  let subPrf = fromIsProjectLeftToComp_Lemma_4 delElemPred isSet
      notInLs2 = fromIsProjectLeftToComp_Lemma_4_1 delElemPred notElem
  in IsSetCons notInLs2 subPrf

-- Dada una prueba de "IsProjectLeft" se puede computar "projectLeft"
fromIsProjectLeftToComp : DecEq lty => {ls : List lty} -> {ts1, ts2 : LabelList lty} -> IsProjectLeft ls ts1 ts2 -> IsSet ls -> ts2 = projectLeft ls ts1
fromIsProjectLeftToComp IPL_EmptyLabels _ = Refl
fromIsProjectLeftToComp {ls} {ts1=[]} {ts2=[]} IPL_EmptyVect _ = fromIsProjectLeftToComp_Lemma_1 {ls=ls}
fromIsProjectLeftToComp {ls} {ts1=(l1,ty1) :: ts1} (IPL_ProjLabelElem l1InLs isDelElem isProjLeft) lsIsSet =
  let lsNewIsSet = fromIsProjectLeftToComp_Lemma_4 isDelElem lsIsSet
      subPrf = fromIsProjectLeftToComp isProjLeft lsNewIsSet
      delElemEq = fromDeleteElemPredToComp isDelElem
      resEq = fromIsProjectLeftToComp_Lemma_3 {ls=ls} {ts=ts1} {l=l1} {ty=ty1} l1InLs lsIsSet
  in rewrite subPrf in (rewrite delElemEq in sym resEq)
fromIsProjectLeftToComp {ls} {ts1=(l1,ty1) :: ts1} (IPL_ProjLabelNotElem notIsElem isProjLeft) lsIsSet =
  let subPrf = fromIsProjectLeftToComp isProjLeft lsIsSet
      resEq = fromIsProjectLeftToComp_Lemma_2 notIsElem {ls=ls} {ts=ts1} {l=l1} {ty=ty1}
  in rewrite subPrf in (rewrite resEq in Refl)
  
-- Dada la computación de "projectLeft" se puede crear una prueba de "IsProjectLeft"
fromCompToIsProjectLeft : DecEq lty => (ls : List lty) -> (ts : LabelList lty) -> IsProjectLeft ls ts (projectLeft ls ts) 
fromCompToIsProjectLeft [] ts = IPL_EmptyLabels
fromCompToIsProjectLeft (l1 :: ls) [] = IPL_EmptyVect
fromCompToIsProjectLeft (l1 :: ls) ((l2,ty) :: ts) with (isElem l2 (l1::ls))
  fromCompToIsProjectLeft (l1 :: ls) ((l2,ty) :: ts) | Yes l2InLs = 
    let delElemPred = fromCompToDeleteElemPred (l1 :: ls) l2InLs        
        subPrf = fromCompToIsProjectLeft (deleteElem (l1 :: ls) l2InLs) ts
    in IPL_ProjLabelElem l2InLs delElemPred subPrf
  fromCompToIsProjectLeft (l1 :: ls) ((l2,ty) :: ts) | No notL2InLs = 
    let subPrf = fromCompToIsProjectLeft (l1 :: ls) ts
    in IPL_ProjLabelNotElem notL2InLs subPrf
    
-- hProjectByLabels que retorna la computación de la proyección en el tipo
hProjectByLabels : DecEq lty => {ts : LabelList lty} -> (ls : List lty) -> Record ts -> IsSet ls -> Record (projectLeft ls ts)
hProjectByLabels {ts} ls rec lsIsSet =
  let 
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
    (lsRes ** (hsRes, prjLeftRes)) = fst $ hProjectByLabelsHList ls hs
    isLabelSetRes = hProjectByLabelsLeftIsSet_Lemma2 prjLeftRes isLabelSet
    resIsProjComp = fromIsProjectLeftToComp prjLeftRes lsIsSet
    recRes = hListToRec {prf=isLabelSetRes} hsRes
  in rewrite (sym resIsProjComp) in recRes
  
-- hProjectByLabels_comp que obtiene la prueba de "IsSet ls" de forma automática
hProjectByLabelsAuto : DecEq lty => {ts : LabelList lty} -> (ls : List lty) -> Record ts -> TypeOrUnit (isSet ls) (Record (projectLeft ls ts))
hProjectByLabelsAuto {ts} ls rec = mkTypeOrUnit (isSet ls) (\lsIsSet => hProjectByLabels {ts=ts} ls rec lsIsSet)
  
-- *** hDeleteByLabel *** 
  
-- Predicado que indica que un campo fue eliminado de la lista de un record. Si el elemento no existe en la lista la retorna igual      
data DeleteLabelAtPred : DecEq lty => lty -> LabelList lty -> LabelList lty -> Type where
  EmptyRecord : DecEq lty => {l : lty} -> DeleteLabelAtPred l [] []
  IsElem : DecEq lty => {l : lty} -> DeleteLabelAtPred l ((l,ty) :: ts) ts
  IsNotElem : DecEq lty => {l1 : lty} -> Not (l1 = l2) -> DeleteLabelAtPred l1 ts1 ts2 -> 
    DeleteLabelAtPred l1 ((l2,ty) :: ts1) ((l2,ty) :: ts2)
  
deleteLabelAt : DecEq lty => lty -> LabelList lty -> LabelList lty
deleteLabelAt l [] = []
deleteLabelAt l1 ((l2,ty) :: ts) with (decEq l1 l2)
  deleteLabelAt l1 ((l2,ty) :: ts) | Yes l1EqL2 = ts
  deleteLabelAt l1 ((l2,ty) :: ts) | No notL1EqL2 = (l2,ty) :: deleteLabelAt l1 ts

fromDeleteLabelAtFuncToPred : DecEq lty => {l : lty} -> {ts : LabelList lty} -> DeleteLabelAtPred l ts (deleteLabelAt l ts)  
fromDeleteLabelAtFuncToPred {l} {ts=[]} = EmptyRecord
fromDeleteLabelAtFuncToPred {l=l1} {ts=((l2,ty) :: ts)} with (decEq l1 l2)
  fromDeleteLabelAtFuncToPred {l=l1} {ts=((l2,ty) :: ts)} | Yes l1EqL2 = rewrite l1EqL2 in IsElem
  fromDeleteLabelAtFuncToPred {l=l1} {ts=((l2,ty) :: ts)} | No notL1EqL2 = 
    let subDelPred = fromDeleteLabelAtFuncToPred {l=l1} {ts}
    in IsNotElem notL1EqL2 subDelPred
    
-- Transformo una prueba de que se proyectó una lista con un solo elemento a una prueba de que se elimino tal elemento
fromIsProjectRightToDeleteLabelAtPred : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} -> IsProjectRight [l] ts1 ts2 -> 
  DeleteLabelAtPred l ts1 ts2
fromIsProjectRightToDeleteLabelAtPred IPR_EmptyVect = EmptyRecord
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelElem isElem delElem IPR_EmptyLabels) impossible
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelElem isElem delElem IPR_EmptyVect) impossible
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelElem isElem delElem (IPR_ProjLabelElem subElem subDel subProjRight)) impossible
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelElem isElem delElem (IPR_ProjLabelNotElem subNotElem subProjRight)) impossible
fromIsProjectRightToDeleteLabelAtPred (IPR_ProjLabelNotElem notElem subPrjRight) = 
  let subDelFromRec = fromIsProjectRightToDeleteLabelAtPred subPrjRight
      notEqual = ifNotElemThenNotEqual notElem
  in IsNotElem (symNot notEqual) subDelFromRec
    
        
hDeleteAtLabelHList : DecEq lty => {ts1 : LabelList lty} -> (l : lty) -> HList ts1 ->
  (ts2 : LabelList lty ** (HList ts2, DeleteLabelAtPred l ts1 ts2))
hDeleteAtLabelHList l hs =
  let (_, (ts2 ** (hs2, prjRightRes))) = hProjectByLabelsHList [l] hs
  in (ts2 ** (hs2, fromIsProjectRightToDeleteLabelAtPred prjRightRes))
  
hDeleteAtLabelIsNotElem : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} -> DeleteLabelAtPred l1 ts1 ts2 ->
  Not (ElemLabel l2 ts1) -> Not (ElemLabel l2 ts2)  
hDeleteAtLabelIsNotElem EmptyRecord notL2InTs1 l2InTs2 = noEmptyElem l2InTs2
hDeleteAtLabelIsNotElem IsElem notL2InTs1 l2InTs2 = notElemInCons notL2InTs1 l2InTs2
hDeleteAtLabelIsNotElem {l1} {l2} (IsNotElem {l2} {ty} notL1EqL3 delAtPred) notL2InTs1 Here = ifNotElemThenNotEqual notL2InTs1 Refl
hDeleteAtLabelIsNotElem {l1} {l2} (IsNotElem {l2=l3} {ty} notL1EqL3 delAtPred) notL2InTs1Cons (There l2InTs2) = 
  let notL2InTs1 = notElemInCons notL2InTs1Cons
      notL2InTs2  = hDeleteAtLabelIsNotElem delAtPred notL2InTs1
  in notL2InTs2 l2InTs2
  
hDeleteAtLabelIsLabelSet : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} -> DeleteLabelAtPred l ts1 ts2 ->
  IsLabelSet ts1 -> IsLabelSet ts2
hDeleteAtLabelIsLabelSet EmptyRecord _ = IsSetNil
hDeleteAtLabelIsLabelSet IsElem (IsSetCons notLInTs1 isSetTs1) = isSetTs1
hDeleteAtLabelIsLabelSet {l=l1} (IsNotElem {l2} {ty} notL1EqL2 delAtPred) (IsSetCons notL2InTs1 isSetTs1) = 
  let isSetTs2 = hDeleteAtLabelIsLabelSet delAtPred isSetTs1
      notL2InTs2 = hDeleteAtLabelIsNotElem delAtPred notL2InTs1
  in IsSetCons notL2InTs2 isSetTs2

-- *-* Definición de "hDeleteAtLabel" de hackage *-*
hDeleteAtLabel : DecEq lty => {ts1 : LabelList lty} -> (l : lty) -> Record ts1 ->
  (ts2 : LabelList lty ** (Record ts2, DeleteLabelAtPred l ts1 ts2))
hDeleteAtLabel l rec =
  let 
    isSetTs1 = recLblIsSet rec
    hs = recToHList rec
    (ts2 ** (hs2, delAtPred)) = hDeleteAtLabelHList l hs
    isSetTs2 = hDeleteAtLabelIsLabelSet delAtPred isSetTs1
  in (ts2 ** (hListToRec {prf=isSetTs2} hs2, delAtPred))


-- *** hAppend ***

-- hAppend para HList
(++) : HList ts1 -> HList ts2 -> HList (ts1 ++ ts2)
(++) [] hs2 = hs2
(++) (h1 :: hs1) hs2 = h1 :: (hs1 ++ hs2)

-- Si un elemento está en la lista de la izquierda, entonces también está en el append de esa con otra lista
ifIsElemThenIsInAppendLeft : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
    ElemLabel l ts1 -> ElemLabel l (ts1 ++ ts2)
ifIsElemThenIsInAppendLeft {ts1=((l,ty) :: ts1)} Here = Here
ifIsElemThenIsInAppendLeft {ts1=((l,ty) :: ts1)} {ts2} (There isThere) = 
  let subPrf = ifIsElemThenIsInAppendLeft {ts2=ts2} isThere
  in (There subPrf)

-- Si un elemento está en la lista de la derecha, entonces también está en el append de esa con otra lista
ifIsElemThenIsInAppendRight : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  ElemLabel l ts2 -> ElemLabel l (ts1 ++ ts2)
ifIsElemThenIsInAppendRight {ts1=[]} isElem = isElem
ifIsElemThenIsInAppendRight {ts1=((l1,ty1) :: ts1)} {ts2=[]} isElem = absurd $ noEmptyElem isElem
ifIsElemThenIsInAppendRight {l} {ts1=((l1,ty1) :: ts1)} {ts2=((l2,ty2) :: ts2)} isElem = 
  let subPrf = ifIsElemThenIsInAppendRight {ts1=ts1} {ts2=((l2,ty2)::ts2)} {l=l} isElem
  in There subPrf

-- Si un elemento pertenece a una de las dos listas, pertenece al append
ifIsInOneThenIsInAppend : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  Either (ElemLabel l ts1) (ElemLabel l ts2) -> ElemLabel l (ts1 ++ ts2)
ifIsInOneThenIsInAppend (Left isElem) = ifIsElemThenIsInAppendLeft isElem    
ifIsInOneThenIsInAppend {ts1} {ts2} {l} (Right isElem) = ifIsElemThenIsInAppendRight isElem     

-- Si un elemento pertenece a un append, entonces pertenece a alguna de ambas listas
ifIsInAppendThenIsInOne : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  ElemLabel l (ts1 ++ ts2) -> Either (ElemLabel l ts1) (ElemLabel l ts2)
ifIsInAppendThenIsInOne {ts1=[]} isElem = (Right isElem)
ifIsInAppendThenIsInOne {ts1=((l1,ty1) :: ts1)} Here = (Left Here)
ifIsInAppendThenIsInOne {l} {ts1=((l1,ty) :: ts1)} (There isThere) =
  case (ifIsInAppendThenIsInOne isThere) of
    Left isElem => Left $ There isElem
    Right isElem => Right isElem
    
-- Si un elemento no pertenece a un append, entonces no pertenece a ninguna de las listas concatenadas
ifNotInAppendThenNotInNeither : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  Not (ElemLabel l (ts1 ++ ts2)) -> (Not (ElemLabel l ts1), Not (ElemLabel l ts2))
ifNotInAppendThenNotInNeither {ts1=[]} {ts2=ts2} {l} notInAppend = (notInTs1, notInTs2)
   where
    notInTs1 : Not (ElemLabel l [])
    notInTs1 inTs1 = noEmptyElem inTs1
    
    notInTs2 : Not (ElemLabel l ts2)
    notInTs2 inTs2 = notInAppend inTs2
ifNotInAppendThenNotInNeither {ts1=((l2,ty) :: ts1)} {ts2} {l} notInAppend = (notInTs1, notInTs2)
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

-- Si un label no está en ninguna lista concatenada, entonces no está en el append
ifNotInEitherThenNotInAppend : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  Not (ElemLabel l ts1) -> Not (ElemLabel l ts2) -> Not (ElemLabel l (ts1 ++ ts2))
ifNotInEitherThenNotInAppend {ts1=[]} notInTs1 notInTs2 inAppend = notInTs2 inAppend
ifNotInEitherThenNotInAppend {ts1=((l1,ty1) :: ts1)} notInTs1 notInTs2 Here = notInTs1 Here
ifNotInEitherThenNotInAppend {ts1=((l1,ty1) :: ts1)} notInTs1 notInTs2 (There inThere) = 
  let notInAppend = ifNotInEitherThenNotInAppend (notElemInCons notInTs1) notInTs2
  in notInAppend inThere

-- Si dos LabelList concatenados son un conjunto, entonces cada uno es un conjunto por separado
ifAppendIsSetThenEachIsToo : DecEq lty => {ts1, ts2 : LabelList lty} -> IsLabelSet (ts1 ++ ts2) -> (IsLabelSet ts1, IsLabelSet ts2)
ifAppendIsSetThenEachIsToo {ts1=[]} isSet = (IsSetNil, isSet)
ifAppendIsSetThenEachIsToo {ts1=((l,ty) :: ts1)} (IsSetCons notInAppend isSetAppend) =
  let 
    subPrf = ifAppendIsSetThenEachIsToo isSetAppend
    notInTs1 = fst $ ifNotInAppendThenNotInNeither notInAppend
  in (IsSetCons notInTs1 (fst $ subPrf), snd subPrf)

-- *-* Definición de "hAppend" de hackage *-*
hAppend : DecEq lty => {ts1, ts2 : LabelList lty} -> Record ts1 -> Record ts2 -> IsLabelSet (ts1 ++ ts2) -> Record (ts1 ++ ts2)
hAppend rec1 rec2 isLabelSet =
  let
    hs1 = recToHList rec1
    hs2 = recToHList rec2
  in hListToRec {prf=isLabelSet} (hs1 ++ hs2)
    
-- "hAppendAuto" donde la prueba de labels no repetidos es calculada automáticamente
hAppendAuto : DecEq lty => {ts1, ts2 : LabelList lty} -> Record ts1 -> Record ts2 -> RecordOrUnit (ts1 ++ ts2)
hAppendAuto {ts1} {ts2} rec1 rec2 = mkTypeOrUnit (isLabelSet (ts1 ++ ts2)) (\isSet => hAppend rec1 rec2 isSet)

-- *** hDeleteLabels ***

-- Predicado que indica que una lista de labels fue eliminada de un record
data DeleteLabelsPred : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type where
  EmptyLabelList : DecEq lty => DeleteLabelsPred {lty=lty} [] ts ts
  DeleteFirstOfLabelList : DecEq lty => DeleteLabelAtPred l tsAux tsRes -> DeleteLabelsPred ls ts tsAux ->
    DeleteLabelsPred {lty=lty} (l :: ls) ts tsRes
    
deleteLabels : DecEq lty => List lty -> LabelList lty -> LabelList lty
deleteLabels [] ts = ts
deleteLabels (l :: ls) ts = 
  let subDelLabels = deleteLabels ls ts
  in deleteLabelAt l subDelLabels

fromDeleteLabelsFuncToPred : DecEq lty => {ls : List lty} -> {ts : LabelList lty} -> DeleteLabelsPred ls ts (deleteLabels ls ts)    
fromDeleteLabelsFuncToPred {ls=[]} {ts} = EmptyLabelList
fromDeleteLabelsFuncToPred {ls=l :: ls} {ts} = 
  let subDelLabelPred = fromDeleteLabelsFuncToPred {ls} {ts}
      delLabelAtPred = fromDeleteLabelAtFuncToPred {l} {ts=deleteLabels ls ts}
  in DeleteFirstOfLabelList {tsAux=deleteLabels ls ts} delLabelAtPred subDelLabelPred
    
hDeleteLabelsHList : DecEq lty => {ts1 : LabelList lty} -> (ls : List lty) -> HList ts1 ->
  (ts2 : LabelList lty ** (HList ts2, DeleteLabelsPred ls ts1 ts2))
hDeleteLabelsHList {ts1} [] hs = (ts1 ** (hs, EmptyLabelList))
hDeleteLabelsHList (l :: ls) hs1 = 
  let (ts3 ** (hs2, delLabelPred)) = hDeleteLabelsHList ls hs1
      (ts4 ** (hs3, delAtPred)) = hDeleteAtLabelHList l hs2
  in (ts4 ** (hs3, DeleteFirstOfLabelList delAtPred delLabelPred))

-- Si un LabelList es un conjunto, y se eliminan cualquier cantidad de labels de ésta, entonces el resultado sigue siendo un conjunto 
hDeleteLabelsIsLabelSet : DecEq lty => {ts1, ts2 : LabelList lty} -> {ls : List lty} -> DeleteLabelsPred ls ts1 ts2 ->
  IsLabelSet ts1 -> IsLabelSet ts2
hDeleteLabelsIsLabelSet EmptyLabelList isSetTs1 = isSetTs1
hDeleteLabelsIsLabelSet (DeleteFirstOfLabelList {tsAux=ts3} delAtLabel delLabels) isSetTs1 = 
  let isSetTs3 = hDeleteLabelsIsLabelSet delLabels isSetTs1
      isSetTs2 = hDeleteAtLabelIsLabelSet delAtLabel isSetTs3
  in isSetTs2
  
-- *-* Definición de "hDeleteLabels" de hackage *-*
hDeleteLabels : DecEq lty => {ts1 : LabelList lty} -> (ls : List lty) -> Record ts1 ->
  (ts2 : LabelList lty ** (Record ts2, DeleteLabelsPred ls ts1 ts2))
hDeleteLabels ls rec =
  let
    isSetTs1 = recLblIsSet rec
    hs = recToHList rec
    (ts2 ** (hs2, delLabelsPred)) = hDeleteLabelsHList ls hs
    isSetTs2 = hDeleteLabelsIsLabelSet delLabelsPred isSetTs1
  in
    (ts2 ** (hListToRec {prf=isSetTs2} hs2, delLabelsPred))

-- *** hLeftUnion ***

-- Predicado que indica que la unión por la izquierda de dos LabelList que son un conjunto es equivalente a la tercera
data IsLeftUnion : DecEq lty => LabelList lty -> LabelList lty -> LabelList lty -> Type where
  IsLeftUnionAppend : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> DeleteLabelsPred (labelsOf ts1) ts2 ts3 -> 
    IsLeftUnion ts1 ts2 (ts1 ++ ts3)
    
hLeftUnion_List : DecEq lty => LabelList lty -> LabelList lty -> LabelList lty
hLeftUnion_List ts1 ts2 = ts1 ++ (deleteLabels (labelsOf ts1) ts2)

fromHLeftUnionFuncToPred : DecEq lty => {ts1 : LabelList lty} -> {ts2 : LabelList lty} -> IsLeftUnion ts1 ts2 (hLeftUnion_List ts1 ts2)    
fromHLeftUnionFuncToPred {ts1} {ts2} = 
  let delLabelsPred = fromDeleteLabelsFuncToPred {ls=labelsOf ts1} {ts=ts2}
  in IsLeftUnionAppend delLabelsPred
  
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
ifDeleteLabelsThenAppendIsSetLemma_1_2_1 {ts1} {ts2} {l1} {l2=l1} {ty2} notElemCons notL2InTs1 Here =
  let inCons = ifIsInOneThenIsInAppend {l=l1} {ts1} {ts2=(l1,ty2) :: ts2} (Right Here)
  in notElemCons inCons
ifDeleteLabelsThenAppendIsSetLemma_1_2_1 notElemCons notL2InTs1 (There isThere) = notL2InTs1 isThere

ifDeleteLabelsThenAppendIsSetLemma_1_2 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} -> {ty : Type} ->
  IsLabelSet (ts1 ++ ((l,ty) :: ts2)) -> (Not (ElemLabel l ts1), Not (ElemLabel l ts2))  
ifDeleteLabelsThenAppendIsSetLemma_1_2 {ts1=[]} {l} {ty} {ts2} (IsSetCons notElem subIsSet) = (noEmptyElem, notElem)
ifDeleteLabelsThenAppendIsSetLemma_1_2 {ts1=(l1,ty1) :: ts1} {l=l2} {ty=ty2} {ts2} (IsSetCons notElem subIsSet) = 
  let (notInTs1, notInTs2) = ifDeleteLabelsThenAppendIsSetLemma_1_2 subIsSet
  in (ifDeleteLabelsThenAppendIsSetLemma_1_2_1 notElem notInTs1, notInTs2)

ifDeleteLabelsThenAppendIsSetLemma_1_3 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} ->
  DeleteLabelAtPred l1 ts1 ts2 -> Not (ElemLabel l2 ts1) -> Not (ElemLabel l2 ts2)
ifDeleteLabelsThenAppendIsSetLemma_1_3 EmptyRecord notInTs1 inTs2 = notInTs1 inTs2
ifDeleteLabelsThenAppendIsSetLemma_1_3 IsElem notInTs1 inTs2 = notInTs1 $ There inTs2
ifDeleteLabelsThenAppendIsSetLemma_1_3 (IsNotElem notEqual subDelAt) notInTs1 Here = notInTs1 Here
ifDeleteLabelsThenAppendIsSetLemma_1_3 {l1} {l2} {ts1=((l3,ty3) :: ts1)} {ts2=((l3,ty3) :: ts2)} (IsNotElem notEqual subDelAt) notInTs1 (There inTs2) =
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_1_3 {l1=l1} {ts1=ts1} {ts2=ts2} subDelAt (notElemInCons notInTs1)
  in subPrf inTs2

ifDeleteLabelsThenAppendIsSetLemma_1_4_1 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l1, l2 : lty} -> {ty2 : Type} ->
  Not (l1 = l2) -> Not (ElemLabel l1 (ts1 ++ ts2)) -> Not (ElemLabel l1 (ts1 ++ ((l2,ty2) :: ts2)))
ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {ts1=[]} notEqual notInAppend Here = notEqual Refl
ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {ts1=[]} notEqual notInAppend (There isThere) = notInAppend isThere
ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {l1} {l2} {ts1=(l1,ty3) :: ts1} notEqual notInAppend Here = notInAppend Here
ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {l1} {l2} {ts1=(l3,ty3) :: ts1} {ts2=ts2} {ty2=ty2} notEqual notInAppend (There isThere) = 
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {l1=l1} {l2=l2} {ts1=ts1} {ts2=ts2} {ty2=ty2} notEqual (notElemInCons notInAppend)
  in subPrf isThere

ifDeleteLabelsThenAppendIsSetLemma_1_4 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} -> {ty : Type} ->
  IsLabelSet (ts1 ++ ts2) -> Not (ElemLabel l ts1) -> Not (ElemLabel l ts2) -> IsLabelSet (ts1 ++ ((l,ty) :: ts2))
ifDeleteLabelsThenAppendIsSetLemma_1_4 {ts1=[]} isSet notInTs1 notInTs2 = IsSetCons notInTs2 isSet
ifDeleteLabelsThenAppendIsSetLemma_1_4 {l=l2} {ty=ty2} {ts1=(l1,ty1) :: ts1} {ts2} (IsSetCons notElem isSet) notInTs1 notInTs2 = 
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_1_4 {l=l2} {ty=ty2} isSet (notElemInCons notInTs1) notInTs2
      notEqual = symNot $ ifNotElemThenNotEqual notInTs1
      notElemCons = ifDeleteLabelsThenAppendIsSetLemma_1_4_1 {l2=l2} {ty2=ty2} {l1=l1} {ts1=ts1} {ts2=ts2} notEqual notElem
  in IsSetCons notElemCons subPrf

ifDeleteLabelsThenAppendIsSetLemma_1 : DecEq lty => {ts1, ts2, ts3 : LabelList lty} -> {l : lty} -> DeleteLabelAtPred l ts2 ts3 ->
  IsLabelSet (ts1 ++ ts2) -> IsLabelSet (ts1 ++ ts3)
ifDeleteLabelsThenAppendIsSetLemma_1 EmptyRecord isSet = isSet
ifDeleteLabelsThenAppendIsSetLemma_1 {ts1=[]} IsElem (IsSetCons notElem isSet) = isSet
ifDeleteLabelsThenAppendIsSetLemma_1 {l} {ts1=((l1,ty1) :: ts1)} {ts3} IsElem (IsSetCons notElem isSet) =
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

-- Si un LabelList es un conjunto, y se elimina un label de tal, entonces ese label no pertenece a la lista resultante
ifDeleteLabelsThenAppendIsSetLemma_2 : DecEq lty => {ts1, ts2 : LabelList lty} -> {l : lty} ->
  IsLabelSet ts1 -> DeleteLabelAtPred l ts1 ts2 -> Not (ElemLabel l ts2)
ifDeleteLabelsThenAppendIsSetLemma_2 isSet1 EmptyRecord elemLabel = noEmptyElem elemLabel
ifDeleteLabelsThenAppendIsSetLemma_2 (IsSetCons notElem isSet) IsElem elemLabel = notElem elemLabel
ifDeleteLabelsThenAppendIsSetLemma_2 (IsSetCons notElem isSet) (IsNotElem notEqual subDelAt) Here = notEqual Refl
ifDeleteLabelsThenAppendIsSetLemma_2 {l=l} (IsSetCons notElem isSet) (IsNotElem notEqual subDelAt) (There isThere) = 
  let subPrf = ifDeleteLabelsThenAppendIsSetLemma_2 {l=l} isSet subDelAt 
  in subPrf isThere

-- Lemma que indica que si se eliminan del 2ndo record los labels del 1ero, entonces agregar la resta al 1ero crea un conjunto
ifDeleteLabelsThenAppendIsSetLemma : DecEq lty => {ts1, ts2, tsDel : LabelList lty} -> IsLabelSet ts1 -> IsLabelSet ts2 -> 
  DeleteLabelsPred (labelsOf ts1) ts2 tsDel -> IsLabelSet (ts1 ++ tsDel)
ifDeleteLabelsThenAppendIsSetLemma {ts1=[]} isSet1 isSet2 EmptyLabelList = isSet2
ifDeleteLabelsThenAppendIsSetLemma {ts1=((l1,ty1) :: ts1)} {tsDel} (IsSetCons notElem subIsSet1) isSet2 (DeleteFirstOfLabelList {tsAux=ts3} subDelAt subDel) =
  let
    subPrf = ifDeleteLabelsThenAppendIsSetLemma {ts1=ts1} subIsSet1 isSet2 subDel
    resIsSet = ifDeleteLabelsThenAppendIsSetLemma_1 {ts1=ts1} {ts2=ts3} {ts3=tsDel} subDelAt subPrf
    isSet3 = snd $ ifAppendIsSetThenEachIsToo subPrf
    isNotInTsDel = ifDeleteLabelsThenAppendIsSetLemma_2 isSet3 subDelAt
    isNotInAppend = ifNotInEitherThenNotInAppend notElem isNotInTsDel
  in IsSetCons isNotInAppend resIsSet
   
-- *-* Definición de "hLeftUnion" de hackage *-*
hLeftUnion : DecEq lty => {ts1, ts2 : LabelList lty} -> Record ts1 -> Record ts2 ->
   (tsRes : LabelList lty ** (Record tsRes, IsLeftUnion ts1 ts2 tsRes))
hLeftUnion {ts1} {ts2} rec1 rec2 = 
  let
    isSet1 = recLblIsSet rec1
    isSet2 = recLblIsSet rec2
    (tsDel ** (recDel, prfDel)) = hDeleteLabels (labelsOf ts1) rec2
    recRes = hAppend rec1 recDel (ifDeleteLabelsThenAppendIsSetLemma {ts1=ts1} {ts2=ts2} {tsDel=tsDel} isSet1 isSet2 prfDel)
   in
    (ts1 ++ tsDel ** (recRes, IsLeftUnionAppend prfDel))

-- *** hLookupByLabel ***

-- Predicado que indica que un label en una lista de labels tiene un tipo en particular
data HasField : (l : lty) -> LabelList lty -> Type -> Type where
  HasFieldHere : HasField l ((l,ty) :: ts) ty
  HasFieldThere : HasField l1 ts ty1 -> HasField l1 ((l2,ty2) :: ts) ty1
  
-- Prueba de que no existe label que tenga un tipo en una lista vacía de labels
noEmptyHasField : Not (HasField l [] ty)  
noEmptyHasField HasFieldHere impossible
noEmptyHasField (HasFieldThere _) impossible

-- Dado un HList, si se tiene una prueba de que el label tiene un tipo en la lista de sus labels, retorna el valor correspondiente
-- en el HList
hLookupByLabel_HList : DecEq lty => {ts : LabelList lty} -> (l : lty) -> HList ts -> HasField l ts ty -> ty
hLookupByLabel_HList _ (val :: _) HasFieldHere = val
hLookupByLabel_HList l (_ :: ts) (HasFieldThere hasFieldThere) = hLookupByLabel_HList l ts hasFieldThere

-- *-* Definición de "hLookupByLabel" de hackage *-*
hLookupByLabel : DecEq lty => {ts : LabelList lty} -> (l : lty) -> Record ts -> HasField l ts ty -> ty
hLookupByLabel {ts} {ty} l rec hasField = hLookupByLabel_HList {ts} {ty} l (recToHList rec) hasField

-- hLookupByLabel que obtiene la prueba de HasField de forma automática
hLookupByLabelAuto : DecEq lty => {ts : LabelList lty} -> (l : lty) -> Record ts -> {auto hasField : HasField l ts ty} -> ty
hLookupByLabelAuto {ts} {ty} l rec {hasField} = hLookupByLabel_HList {ts} {ty} l (recToHList rec) hasField

-- *** hUpdateAtLabel ***

hUpdateAtLabel_HList : DecEq lty => {ts : LabelList lty} -> (l : lty) -> ty -> HList ts -> HasField l ts ty -> HList ts
hUpdateAtLabel_HList l val1 (val2 :: hs) HasFieldHere = val1 :: hs
hUpdateAtLabel_HList l val1 (val2 :: hs) (HasFieldThere hasFieldThere) = val2 :: (hUpdateAtLabel_HList l val1 hs hasFieldThere)

-- *-* Definición de "hUpdateAtLabel" de hackage *-*
hUpdateAtLabel : DecEq lty => {ts : LabelList lty} -> (l : lty) -> ty -> Record ts -> HasField l ts ty -> Record ts
hUpdateAtLabel {ts} l val rec hasField =
  let
    isLabelSet = recLblIsSet rec
    hs = recToHList rec
  in
    hListToRec {prf=isLabelSet} (hUpdateAtLabel_HList {ts=ts} l val hs hasField)
    
-- hUpdateAtLabel que obtiene la prueba de "HasField" de forma automática    
hUpdateAtLabelAuto : DecEq lty => {ts : LabelList lty} -> (l : lty) -> ty -> Record ts -> {auto hasField : HasField l ts ty} -> Record ts
hUpdateAtLabelAuto {ts} l val rec {hasField} = hUpdateAtLabel {ts} l val rec hasField
