{-
  Caso de estudio de records extensibles en Idris.
  
  Este caso consiste en diseñar un mini-lenguaje de programación que permita definir expresiones aritméticas utilizando variables con alcance local, y diseñar un intérprete de ese lenguaje utilizando records extensibles.

-}

module CasoDeEstudio

import Data.List
import Extensible_Records

%default total
%access public export

{-
hLookupByLabel : DecEq lty => {ts : LabelList lty} -> (l : lty) -> Record ts -> HasField l ts ty -> ty

hLookupByLabelAuto : DecEq lty => {ts : LabelList lty} -> (l : lty) -> Record ts -> {auto hasField : HasField l ts ty} -> ty

hLeftUnion : DecEq lty => {ts1, ts2 : LabelList lty} -> Record ts1 -> Record ts2 -> 
  (tsRes : LabelList lty ** (Record tsRes, IsLeftUnion ts1 ts2 tsRes))
  
consRec : DecEq lty => {ts : LabelList lty} -> {t : Type} -> 
  (lbl : lty) -> (val : t)->  Record ts -> {notElem : Not (ElemLabel lbl ts)} -> Record ((lbl,t) :: ts)
  
consRecAuto : DecEq lty => {ts : LabelList lty} -> {t : Type} -> (lbl : lty) -> (val : t) -> Record ts -> 
  RecordOrUnit ((lbl,t) :: ts)
  
  IsProjectRight : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type
  IsLeftUnion : DecEq lty => LabelList lty -> LabelList lty -> LabelList lty -> Type
  
  TypeOrUnit : Dec p -> Type -> Type
TypeOrUnit (Yes prf) res = res
TypeOrUnit (No _) _ = ()

-- Dada una condición construye un tipo, o si falla la condición retorna top ("()")
mkTypeOrUnit : (d : Dec p) -> (cnst : p -> res) -> TypeOrUnit d res
mkTypeOrUnit (Yes prf) cnst = cnst prf
mkTypeOrUnit (No _) _ = ()

RecordOrUnit : DecEq lty => LabelList lty -> Type
RecordOrUnit ts = TypeOrUnit (isLabelSet ts) (Record ts)

deleteLabelAt : DecEq lty => lty -> LabelList lty -> LabelList lty

hLeftUnion_List : DecEq lty => LabelList lty -> LabelList lty -> LabelList lty

fromHLeftUnionFuncToPred : DecEq lty => (ts1 : LabelList lty) -> (ts2 : LabelList lty) -> IsLeftUnion ts1 ts2 (hLeftUnion_List ts1 ts2)    
-}

{-
deleteLabelsList : DecEq lty => List lty -> LabelList lty -> LabelList lty
deleteLabelsList [] ts = ts
deleteLabelsList (l :: ls) ts = 
  let subDelLabels = deleteLabelsList ls ts
  in deleteLabelAt l subDelLabels -}

-- ** ** Funciones sobre "List lty" en vez de "LabelList lty" ** **

-- Elimina el 1ero
deleteAtList : DecEq lty => lty -> List lty -> List lty
deleteAtList _ [] = []
deleteAtList l1 (l2 :: ls) with (decEq l1 l2)
  deleteAtList l1 (l1 :: ls) | Yes Refl = ls
  deleteAtList l1 (l2 :: ls) | No _ = l2 :: deleteAtList l1 ls

deleteList : DecEq lty => List lty -> List lty -> List lty
deleteList [] ls = ls
deleteList (l :: ls1) ls2 =
  let subDelete = deleteList ls1 ls2
  in deleteAtList l subDelete

leftUnion : DecEq lty => List lty -> List lty -> List lty
leftUnion ls1 ls2 = ls1 ++ (deleteList ls1 ls2)

projectRightList : DecEq lty => List lty -> List lty -> List lty
projectRightList [] ls2 = ls2
projectRightList ls1 [] = []
projectRightList ls1 (l :: ls2) with (isElem l ls1)
 projectRightList ls1 (l :: ls2) | Yes lInLs = 
   let delLFromLs1 = deleteElem ls1 lInLs
   in projectRightList delLFromLs1 ls2
 projectRightList ls1 (l :: ls2) | No notLInLs = l :: projectRightList ls1 ls2

data IsProjectRight_List :  List lty -> List lty -> List lty -> Type where
  IPR_EmptyLabels_List : IsProjectRight_List {lty} [] ls ls
  IPR_EmptyVect_List :  IsProjectRight_List {lty} ls [] []
  IPR_ProjLabelElem_List : (isElem : Elem l ls1) -> DeleteElemPred ls1 isElem lsNew ->
                      IsProjectRight_List {lty} lsNew ls2 res1 -> IsProjectRight_List ls1 (l :: ls2) res1      
  IPR_ProjLabelNotElem_List : Not (Elem l ls1) -> IsProjectRight_List {lty} ls1 ls2 res1 -> 
                       IsProjectRight_List ls1 (l :: ls2) (l :: res1)

data DeleteLabelAtPred_List : lty -> List lty -> List lty -> Type where
  EmptyRecord_List : {l : lty} -> DeleteLabelAtPred_List l [] []
  IsElem_List : {l : lty} -> DeleteLabelAtPred_List l (l :: ls) ls
  IsNotElem_List : {l1 : lty} -> Not (l1 = l2) -> DeleteLabelAtPred_List l1 ls1 ls2 -> 
    DeleteLabelAtPred_List l1 (l2 :: ls1) (l2 :: ls2)

data DeleteLabelsPred_List : List lty -> List lty -> List lty -> Type where
  EmptyLabelList_List : DeleteLabelsPred_List {lty} [] ls ls
  DeleteFirstOfLabelList_List : DeleteLabelAtPred_List l lsAux lsRes -> DeleteLabelsPred_List ls1 ls2 lsAux ->
    DeleteLabelsPred_List {lty} (l :: ls1) ls2 lsRes

data IsLeftUnion_List : List lty -> List lty -> List lty -> Type where
  IsLeftUnionAppend_List : {ls1, ls2, ls3 : List lty} -> DeleteLabelsPred_List ls1 ls2 ls3 -> 
    IsLeftUnion_List ls1 ls2 (ls1 ++ ls3)


fromDeleteLabelAtListFuncToPred : DecEq lty => {l : lty} -> {ls : List lty} -> DeleteLabelAtPred_List l ls (deleteAtList l ls)
fromDeleteLabelAtListFuncToPred {l} {ls = []} = EmptyRecord_List
fromDeleteLabelAtListFuncToPred {l=l1} {ls = (l2 :: ls)} with (decEq l1 l2)
  fromDeleteLabelAtListFuncToPred {l=l1} {ls = (l1 :: ls)} | Yes Refl = IsElem_List
  fromDeleteLabelAtListFuncToPred {l=l1} {ls = (l2 :: ls)} | No notL1EqL2 = 
    let subDelPred = fromDeleteLabelAtListFuncToPred {l=l1} {ls}
    in IsNotElem_List notL1EqL2 subDelPred  
  
fromDeleteLabelsListFuncToPred : DecEq lty => {ls1, ls2 : List lty} -> DeleteLabelsPred_List ls1 ls2 (deleteList ls1 ls2)
fromDeleteLabelsListFuncToPred {ls1 = []} {ls2} = EmptyLabelList_List
fromDeleteLabelsListFuncToPred {ls1 = (l :: ls1)} {ls2} =
  let subDelListPred = fromDeleteLabelsListFuncToPred {ls1} {ls2}
      delAtPred = fromDeleteLabelAtListFuncToPred {l} {ls=deleteList ls1 ls2}
  in DeleteFirstOfLabelList_List {lsAux=deleteList ls1 ls2} delAtPred subDelListPred

fromLeftUnionFuncToPred : DecEq lty => {ls1, ls2 : List lty} -> IsLeftUnion_List {lty} ls1 ls2 (leftUnion ls1 ls2)   
fromLeftUnionFuncToPred {ls1} {ls2} =
  let delPred = fromDeleteLabelsListFuncToPred {ls1} {ls2}
  in IsLeftUnionAppend_List delPred

fromIsProjRightFuncToPred : DecEq lty => {ls1, ls2 : List lty} -> IsProjectRight_List ls1 ls2 (projectRightList ls1 ls2)
fromIsProjRightFuncToPred {ls1=[]} {ls2} = IPR_EmptyLabels_List
fromIsProjRightFuncToPred {ls1=l1 :: ls1} {ls2=[]} = IPR_EmptyVect_List
fromIsProjRightFuncToPred {ls1=l1 :: ls1} {ls2=l2 :: ls2} with (isElem l2 (l1 :: ls1))
  fromIsProjRightFuncToPred {ls1=l1 :: ls1} {ls2=l2 :: ls2} | Yes l2InLs1 =
    let delElemPred = fromCompToDeleteElemPred (l1 :: ls1) l2InLs1
        subPrf = fromIsProjRightFuncToPred {ls1= deleteElem (l1 :: ls1) l2InLs1} {ls2}
    in IPR_ProjLabelElem_List l2InLs1 delElemPred subPrf
  fromIsProjRightFuncToPred {ls1=l1 :: ls1} {ls2=l2 :: ls2} | No notL2InLs1 = 
    let subPrf = fromIsProjRightFuncToPred {ls1=l1 :: ls1} {ls2}
    in IPR_ProjLabelNotElem_List notL2InLs1 subPrf
    
-- Ningun valor de lista 1 esta en la lista 2
data Excluyent : List t -> List t -> Type where
  ExcluyentNil : Excluyent [] xs
  ExcluyentCons : Not (Elem x1 xs2) -> Excluyent xs1 xs2 -> Excluyent (x1 :: xs1) xs2
    
ifNotExcluyentThenConsIsnt : Not (Excluyent xs1 xs2) -> Not (Excluyent (x1 :: xs1) xs2)        
ifNotExcluyentThenConsIsnt notXs1Excluyent (ExcluyentCons _ xs1Excluyent) = notXs1Excluyent xs1Excluyent

ifIsElemThenConsNotExcluyent : Excluyent xs1 xs2 -> Elem x1 xs2 -> Not (Excluyent (x1 :: xs1) xs2)        
ifIsElemThenConsNotExcluyent xs1Excluyent x1InXs2 (ExcluyentCons notX1InXs2 _) = notX1InXs2 x1InXs2

isExcluyent : DecEq t => (xs1 : List t) -> (xs2 : List t) -> Dec (Excluyent xs1 xs2)
isExcluyent [] xs2 = Yes ExcluyentNil
isExcluyent (x1 :: xs1) xs2 with (isExcluyent xs1 xs2)
  isExcluyent (x1 :: xs1) xs2 | No notXs1Excluyent = No $ ifNotExcluyentThenConsIsnt notXs1Excluyent
  isExcluyent (x1 :: xs1) xs2 | Yes xs1Excluyent with (isElem x1 xs2)
    isExcluyent (x1 :: xs1) xs2 | Yes xs1Excluyent | No notX1InXs2 = Yes $ ExcluyentCons notX1InXs2 xs1Excluyent
    isExcluyent (x1 :: xs1) xs2 | Yes xs1Excluyent | Yes x1InXs2 = No $ ifIsElemThenConsNotExcluyent xs1Excluyent x1InXs2
    

-- Todos los valores de la lista 1 estan en la lista 2
{-data Incluyent : List t -> List t -> Type where
  IncluyentNil : Incluyent [] xs
  IncluyentCons : Elem x1 xs2 -> Incluyent xs1 xs2 -> Incluyent (x1 :: xs1) xs2

ifNotIncluyentThenConsIsnt : Not (Incluyent xs1 xs2) -> Not (Incluyent (x1 :: xs1) xs2)        
ifNotIncluyentThenConsIsnt notXs1Incluyent (IncluyentCons _ xs1Incluyent) = notXs1Incluyent xs1Incluyent

ifIsNotElemThenConsNotIncluyent : Incluyent xs1 xs2 -> Not (Elem x1 xs2) -> Not (Incluyent (x1 :: xs1) xs2)        
ifIsNotElemThenConsNotIncluyent xs1Incluyent notX1InXs2 (IncluyentCons x1InXs2 _) = notX1InXs2 x1InXs2
            
isIncluyent : DecEq t => (xs1 : List t) -> (xs2 : List t) -> Dec (Incluyent xs1 xs2)
isIncluyent [] xs2 = Yes IncluyentNil
isIncluyent (x1 :: xs1) xs2 with (isIncluyent xs1 xs2)
  isIncluyent (x1 :: xs1) xs2 | No notXs1Incluyent = No $ ifNotIncluyentThenConsIsnt notXs1Incluyent
  isIncluyent (x1 :: xs1) xs2 | Yes xs1Incluyent with (isElem x1 xs2)
    isIncluyent (x1 :: xs1) xs2 | Yes xs1Incluyent | No notX1InXs2 = No $ ifIsNotElemThenConsNotIncluyent xs1Incluyent notX1InXs2
    isIncluyent (x1 :: xs1) xs2 | Yes xs1Incluyent | Yes x1InXs2 = Yes $ IncluyentCons x1InXs2 xs1Incluyent -}
  
-- Arbol sintactico del lenguaje de expresiones aritmeticas
data VarDec : String -> Type where
  (:=) : (var : String) -> Nat -> VarDec var

infixr 2 :=

data LocalVariables : List String -> Type where
  Nil : LocalVariables []
  (::) : VarDec l -> LocalVariables ls -> LocalVariables (l :: ls)  

-- fvs: Lista de variables libres
-- cvs: Lista de variables cerradas (ya definidas en local)
data Exp : List String -> List String -> Type where
  Add : Exp fvs1 cvs1 -> Exp fvs2 cvs2 -> IsLeftUnion_List fvs1 fvs2 fvsRes -> 
    IsLeftUnion_List cvs1 cvs2 cvsRes -> Exp fvsRes cvsRes 
  Var : (l : String) -> Exp [l] []
  Cons : Nat -> Exp [] []
  Local : LocalVariables localVars -> Exp fvsInner cvsInner -> IsSet localVars -> Excluyent localVars cvsInner ->
    IsProjectRight_List localVars fvsInner fvsOuter -> Exp fvsOuter (cvsInner ++ localVars)


-- DSL del lenguaje
var : (l : String) -> Exp [l] []
var l = Var l

cons : Nat -> Exp [] []
cons n = Cons n

add : Exp fvs1 cvs1 -> Exp fvs2 cvs2 -> Exp (leftUnion fvs1 fvs2) (leftUnion cvs1 cvs2)
add {fvs1} {fvs2} {cvs1} {cvs2} e1 e2 = Add e1 e2 (fromLeftUnionFuncToPred {ls1=fvs1} {ls2=fvs2}) 
  (fromLeftUnionFuncToPred {ls1=cvs1} {ls2=cvs2})

localPred : (vars : LocalVariables localVars) -> (innerExp : Exp fvsInner cvsInner) -> 
  {isSet : IsSet localVars} -> {isExcluyent : Excluyent localVars cvsInner} ->
  Exp (projectRightList localVars fvsInner) (cvsInner ++ localVars)
localPred {localVars} {fvsInner} {cvsInner} vars innerExp {isSet} {isExcluyent} = 
  Local vars innerExp isSet isExcluyent (fromIsProjRightFuncToPred {ls1=localVars} {ls2=fvsInner})

local : (vars : LocalVariables localVars) -> (innerExp : Exp fvsInner cvsInner) ->
  TypeOrUnit (isSet localVars) (TypeOrUnit (isExcluyent localVars cvsInner) 
  (Exp (projectRightList localVars fvsInner) (cvsInner ++ localVars)))
local {localVars} {fvsInner} {cvsInner} vars innerExp = 
  mkTypeOrUnit (isSet localVars)
    (\localIsSet => 
      mkTypeOrUnit (isExcluyent localVars cvsInner) (\localIsExcluyent =>
        Local vars innerExp localIsSet localIsExcluyent (fromIsProjRightFuncToPred {ls1=localVars} {ls2=fvsInner})))
    




-- *** Interprete ***
AllNats : List String -> LabelList String
AllNats [] = []
AllNats (x :: xs) = (x, Nat) :: AllNats xs

data Ambiente : List String -> Type where
--  MkAmbiente : Record {lty=String} (AllNats ls) -> Incluyent fvs ls -> Ambiente ls fvs
  MkAmbiente : Record {lty=String} (AllNats ls) -> Ambiente ls

{-ifIncluyentInUnionThenIncluyentInBoth : IsLeftUnion_List xs1 xs2 xs3 -> Incluyent xs3 ys -> (Incluyent xs1 ys, Incluyent xs2 ys)
ifIncluyentInUnionThenIncluyentInBoth {xs1 = []} (IsLeftUnionAppend_List EmptyLabelList_List) isInc = (IncluyentNil, isInc)
ifIncluyentInUnionThenIncluyentInBoth {xs1 = x1 :: xs1} (IsLeftUnionAppend_List (DeleteFirstOfLabelList_List delAt delLabels)) (IncluyentCons x1InCons isInc) = ?incluyent_Union_rhs

ifIsInIncluyentThenIsInOriginal : Incluyent xs1 xs2 -> Elem x xs1 -> Elem x xs2
ifIsInIncluyentThenIsInOriginal IncluyentNil xInXs1 = absurd $ noEmptyElem xInXs1
ifIsInIncluyentThenIsInOriginal {x=x1} (IncluyentCons x2InXs2 isInc) Here = x2InXs2
ifIsInIncluyentThenIsInOriginal {x=x1} (IncluyentCons x2InXs2 isInc) (There x1InXs1) = ifIsInIncluyentThenIsInOriginal isInc x1InXs1

ifIsInVariablesThenHasNatField : Elem l ls -> HasField l (AllNats ls) Nat
ifIsInVariablesThenHasNatField Here = HasFieldHere
ifIsInVariablesThenHasNatField (There inThere) = HasFieldThere (ifIsInVariablesThenHasNatField inThere) -}



-- hProjectByLabelsWithPred : DecEq lty => {ts1 : LabelList lty} -> (ls : List lty) -> Record ts1 -> IsSet ls -> (ts2 : LabelList lty ** (Record ts2, IsProjectLeft ls ts1 ts2))

ifNotElemThenNotElemNats : Not (Elem x xs) -> Not (ElemLabel x (AllNats xs))
ifNotElemThenNotElemNats {xs = []} notXInXs xInLabelXs = absurd $ noEmptyElem xInLabelXs
ifNotElemThenNotElemNats {xs = x1 :: xs} notXInXs Here = notXInXs Here
ifNotElemThenNotElemNats {xs = x1 :: xs} notXInXs (There there) = 
  let notInCons = notElemInCons notXInXs
      subPrf = ifNotElemThenNotElemNats notInCons
  in absurd $ subPrf there

splitRecordByAppend : Record (AllNats (ls1 ++ ls2)) -> (Record (AllNats ls1), Record (AllNats ls2))

splitRecordByUnionList : IsLeftUnion_List ls1 ls2 lsRes -> Record (AllNats lsRes) -> (Record (AllNats ls1), Record (AllNats ls2))
splitRecordByUnionList {ls1 = []} (IsLeftUnionAppend_List EmptyLabelList_List) rec = (emptyRec, rec)
splitRecordByUnionList {ls1 = l1 :: ls1} (IsLeftUnionAppend_List (DeleteFirstOfLabelList_List delAt delLabels)) rec =
  let (recLs1, recLs2) = splitRecordByAppend rec
  in ?splitRecordByUnionList
 
-- MkRecord : IsLabelSet ts ->                         HList ts ->                         Record ts
-- MkRecord : IsLabelSet (AllNats (ls1 ++ ls3)) ->     HList (AllNats (ls1 ++ ls3)) ->     Record (AllNats (ls1 ++ ls3))
-- MkRecord : IsLabelSet ((l1, Nat) :: AllNats ls1) -> HList ((l1, Nat) :: AllNats ls1) -> Record ((l1, Nat) :: AllNats ls1)
-- MkRecord : IsLabelSet (AllNats ls2) ->              HList (AllNats ls2) ->              Record (AllNats ls2)

-- IsLeftUnionAppend_List : DeleteLabelsPred_List ls1 ls2 ls3 -> IsLeftUnion_List ls1 ls2 (ls1 ++ ls3)
-- IsLeftUnionAppend_List : DeleteLabelsPred_List ls1 ls2 lsAux -> IsLeftUnion_List ls1 ls2 (ls1 ++ lsAux)

ifNotElemThenInDeleteIsNotElem : DeleteElemPred ls1 isElem ls2 -> Not (Elem l ls1) -> Not (Elem l ls2)
ifNotElemThenInDeleteIsNotElem DeleteElemPredHere notLInLs1 lInLs2 = notElemInCons notLInLs1 lInLs2
ifNotElemThenInDeleteIsNotElem (DeleteElemPredThere delThere) notLInLs1 Here = notLInLs1 Here
ifNotElemThenInDeleteIsNotElem (DeleteElemPredThere delThere) notLInLs1 (There there) = 
  let subPrf = ifNotElemThenInDeleteIsNotElem delThere (notElemInCons notLInLs1)
  in subPrf there

ifNotElemThenInProjectRightIsNotElemWithNats : {ls1, ls2, lsRes : List String} -> 
  IsProjectRight_List ls1 ls2 lsRes -> Not (ElemLabel l (AllNats lsRes)) -> Not (Elem l ls1) ->
  Not (ElemLabel l (AllNats ls2))
ifNotElemThenInProjectRightIsNotElemWithNats IPR_EmptyLabels_List notLInLsRes _ lInLs2 = notLInLsRes lInLs2  
ifNotElemThenInProjectRightIsNotElemWithNats IPR_EmptyVect_List _ _ lInLs2 = noEmptyElem lInLs2
ifNotElemThenInProjectRightIsNotElemWithNats (IPR_ProjLabelElem_List isElem delElem prjRight) notLInLsRes notLInLs1 Here = notLInLs1 isElem
ifNotElemThenInProjectRightIsNotElemWithNats (IPR_ProjLabelElem_List isElem delElem prjRight) notLInLsRes notLInLs1 (There there) = 
  let lNotInLsNew = ifNotElemThenInDeleteIsNotElem delElem notLInLs1
      subPrf = ifNotElemThenInProjectRightIsNotElemWithNats prjRight notLInLsRes lNotInLsNew
  in subPrf there
ifNotElemThenInProjectRightIsNotElemWithNats (IPR_ProjLabelNotElem_List _ _) notLInLsRes _ Here = notLInLsRes Here
ifNotElemThenInProjectRightIsNotElemWithNats (IPR_ProjLabelNotElem_List notElem prjRight) notLInLsResCons notLInLs1 (There there) = 
  let notElemNats = ifNotElemThenNotElemNats notElem
      notLInLsRes = notElemInCons notLInLsResCons
      subPrf = ifNotElemThenInProjectRightIsNotElemWithNats prjRight notLInLsRes notLInLs1
  in subPrf there
  

deleteElemFromLocalVariables : (isElem : Elem l ls1) -> DeleteElemPred ls1 isElem ls2 ->
  LocalVariables ls1 -> LocalVariables ls2

lookupInLocalVars : Elem l localVars -> LocalVariables localVars -> Nat

expIsSet : {fvs, cvs : List String} -> Exp fvs cvs -> IsSet fvs




-- NOTA: Este de abajo tira error de no-totalidad
addLocalVarsToEnv : Ambiente fvs -> IsProjectRight_List localVars fvsInner fvs -> LocalVariables localVars -> IsSet fvsInner ->
  Ambiente fvsInner
addLocalVarsToEnv env IPR_EmptyLabels_List _ _ = env
addLocalVarsToEnv env IPR_EmptyVect_List _ _ = env
addLocalVarsToEnv env (IPR_ProjLabelElem_List {l} isElem delElem prjRight) vars (IsSetCons notLInInner isSet) = 
  let subVars = deleteElemFromLocalVariables isElem delElem vars
      natVal = lookupInLocalVars isElem vars
      (MkAmbiente subRec) = addLocalVarsToEnv env prjRight subVars isSet
      resRec = consRec l natVal subRec {notElem = ifNotElemThenNotElemNats notLInInner}
  in (MkAmbiente resRec)
addLocalVarsToEnv (MkAmbiente (MkRecord (IsSetCons notSetElem isSetRec) (n :: ns))) 
  (IPR_ProjLabelNotElem_List {l} notIsElem prjRight) vars (IsSetCons notLInLs2 isSet) = 
  let tailRec = MkRecord isSetRec ns
      tailEnv = MkAmbiente tailRec  
      (MkAmbiente subRec) = addLocalVarsToEnv tailEnv prjRight vars isSet 
      resRec = consRec l n subRec {notElem = ifNotElemThenNotElemNats notLInLs2}
  in (MkAmbiente resRec)

-- Interpreta una expresion dado un ambiente con valores para cada variable
interpEnv : Ambiente fvs -> Exp fvs cvs -> Nat
interpEnv (MkAmbiente rec) (Add e1 e2 isUnionFvs _) = 
  let (recE1, recE2) = splitRecordByUnionList isUnionFvs rec
      interpE1 = interpEnv (MkAmbiente recE1) e1
      interpE2 = interpEnv (MkAmbiente recE2) e2
   in interpE1 + interpE2
interpEnv (MkAmbiente rec) (Var l) = hLookupByLabel l rec HasFieldHere
interpEnv env (Cons c) = c
interpEnv env (Local vars subExp isSet isExcluyent prjRight) = 
  let isSetInner = expIsSet subExp
      newEnv = addLocalVarsToEnv env prjRight vars isSetInner
  in interpEnv newEnv subExp
  
  
interp : Exp [] cvs -> Nat
interp = interpEnv (MkAmbiente {ls=[]} emptyRec)
    


-- *** Ejemplos ***
expTest1 : Exp ["x", "y"] []
expTest1 = add (var "x") (add (cons 1) (var "y"))

expTest2 : Exp [] ["x"]
expTest2 = local ["x" := 10] $ cons 1

expTest3 : Exp [] ["x", "y"]
expTest3 = local (["x" := 10, "y" := 9]) $ add (var "x") (var "y")
