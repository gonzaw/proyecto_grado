{-
  Caso de estudio de records extensibles en Idris.
  
  Este caso consiste en diseñar un mini-lenguaje de programación que permita definir expresiones aritméticas utilizando variables con alcance local, y diseñar un intérprete de ese lenguaje utilizando records extensibles.

-}

module CasoDeEstudio

import Data.List
import Extensible_Records

%default total
%access public export

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
projectRightList ls1 [] = []
projectRightList ls1 (l :: ls2) with (isElem l ls1)
 projectRightList ls1 (l :: ls2) | Yes lInLs = 
   let delLFromLs1 = deleteElem ls1 lInLs
   in projectRightList delLFromLs1 ls2
 projectRightList ls1 (l :: ls2) | No notLInLs = l :: projectRightList ls1 ls2

projectRightOfEmptyIsTheOther : DecEq lty => {ls : List lty} -> projectRightList [] ls = ls
projectRightOfEmptyIsTheOther {ls=[]} = Refl
projectRightOfEmptyIsTheOther {ls=l :: ls} = cong $ projectRightOfEmptyIsTheOther {ls}

data IsProjectRight_List :  List lty -> List lty -> List lty -> Type where
  IPR_EmptyVect_List :  IsProjectRight_List {lty} ls [] []
  IPR_ProjLabelElem_List : (isElem : Elem l ls1) -> DeleteElemPred ls1 isElem lsNew ->
                      IsProjectRight_List {lty} lsNew ls2 res1 -> IsProjectRight_List ls1 (l :: ls2) res1      
  IPR_ProjLabelNotElem_List : Not (Elem l ls1) -> IsProjectRight_List {lty} ls1 ls2 res1 -> 
                       IsProjectRight_List ls1 (l :: ls2) (l :: res1)

projectRightOfEmptyIsTheOtherPred : DecEq lty => {ls : List lty} -> IsProjectRight_List [] ls ls
projectRightOfEmptyIsTheOtherPred {ls=[]} = IPR_EmptyVect_List
projectRightOfEmptyIsTheOtherPred {ls=l :: ls} = IPR_ProjLabelNotElem_List noEmptyElem (projectRightOfEmptyIsTheOtherPred {ls})

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
fromIsProjRightFuncToPred {ls1} {ls2=[]} = IPR_EmptyVect_List
fromIsProjRightFuncToPred {ls1} {ls2=l2 :: ls2} with (isElem l2 ls1)
  fromIsProjRightFuncToPred {ls1} {ls2=l2 :: ls2} | Yes l2InLs1 =
    let delElemPred = fromCompToDeleteElemPred ls1 l2InLs1
        subPrf = fromIsProjRightFuncToPred {ls1= deleteElem ls1 l2InLs1} {ls2}
    in IPR_ProjLabelElem_List l2InLs1 delElemPred subPrf
  fromIsProjRightFuncToPred {ls1} {ls2=l2 :: ls2} | No notL2InLs1 = 
    let subPrf = fromIsProjRightFuncToPred {ls1} {ls2}
    in IPR_ProjLabelNotElem_List notL2InLs1 subPrf
      
-- Arbol sintactico del lenguaje de expresiones aritmeticas
data VarDec : String -> Type where
  (:=) : (var : String) -> Nat -> VarDec var

infixr 2 :=

-- fvs: Lista de variables libres
data Exp : List String -> Type where
  Add : Exp fvs1 -> Exp fvs2 -> IsLeftUnion_List fvs1 fvs2 fvsRes -> Exp fvsRes 
  Var : (l : String) -> Exp [l]
  Cons : Nat -> Exp []
  Let : VarDec var -> Exp fvsInner -> DeleteLabelAtPred_List var fvsInner fvsOuter -> Exp fvsOuter
  
-- DSL del lenguaje
var : (l : String) -> Exp [l]
var l = Var l

cons : Nat -> Exp []
cons n = Cons n

add : Exp fvs1 -> Exp fvs2 -> Exp (leftUnion fvs1 fvs2)
add {fvs1} {fvs2} e1 e2 = Add e1 e2 (fromLeftUnionFuncToPred {ls1=fvs1} {ls2=fvs2})

eLet : VarDec var -> Exp fvs -> Exp (deleteAtList var fvs)
eLet {var} {fvs} varDec e = Let varDec e (fromDeleteLabelAtListFuncToPred {l=var} {ls=fvs})

data LocalVariables : List String -> Type where
  Nil : LocalVariables []
  (::) : VarDec l -> LocalVariables ls -> LocalVariables (l :: ls)  


deleteLabelIsProjectingCons : DecEq lty => {ls1, ls2 : List lty} -> DeleteLabelAtPred_List l (projectRightList ls1 ls2) (projectRightList (l :: ls1) ls2)
deleteLabelIsProjectingCons {ls1} {ls2=[]} = EmptyRecord_List
deleteLabelIsProjectingCons {ls1} {ls2=l2 :: ls2} with (isElem l2 ls1)
  deleteLabelIsProjectingCons {ls1} {ls2=l2 :: ls2} | Yes l2InLs1 = ?delLabelCons_1
  deleteLabelIsProjectingCons {ls1} {ls2=l2 :: ls2} | No notL2InLs1 = ?delLabelCons_2

localPred : (vars : LocalVariables localVars) -> (innerExp : Exp fvsInner) -> 
  {isSet : IsSet localVars} -> Exp (projectRightList localVars fvsInner)
localPred {localVars=[]} {fvsInner} _ innerExp = rewrite (projectRightOfEmptyIsTheOther {ls=fvsInner}) in innerExp
localPred {localVars=l :: localVars} {fvsInner = fvsInner} (varDec :: vars) innerExp {isSet = (IsSetCons _ isSet)} = 
  let subExp = localPred vars innerExp {isSet}  
  in Let varDec subExp deleteLabelIsProjectingCons    
    

local : (vars : LocalVariables localVars) -> (innerExp : Exp fvsInner) ->
  TypeOrUnit (isSet localVars) (Exp (projectRightList localVars fvsInner))
local {localVars} {fvsInner} vars innerExp = 
  mkTypeOrUnit (isSet localVars)
    (\localIsSet => localPred vars innerExp {isSet=localIsSet})


-- *** Subset de una lista ***
data IsSubSet : List lty -> List lty -> Type where
  IsSubSetNil : IsSubSet [] ls
  IsSubSetCons : IsSubSet ls1 ls2 -> Elem l ls2 -> IsSubSet (l :: ls1) ls2
  
-- *** Interprete ***
AllNats : List lty -> LabelList lty
AllNats [] = []
AllNats (x :: xs) = (x, Nat) :: AllNats xs

labelsOfAllNats : labelsOf (AllNats ls) = ls
labelsOfAllNats {ls = []} = Refl
labelsOfAllNats {ls = l :: ls} = cong $ labelsOfAllNats {ls}

ifNotElemThenNotInNats : Not (Elem x xs) -> Not (ElemLabel x (AllNats xs))
ifNotElemThenNotInNats {xs = []} notXInXs xInLabelXs = absurd $ noEmptyElem xInLabelXs
ifNotElemThenNotInNats {xs = x1 :: xs} notXInXs Here = notXInXs Here
ifNotElemThenNotInNats {xs = x1 :: xs} notXInXs (There there) = 
  let notInCons = notElemInCons notXInXs
      subPrf = ifNotElemThenNotInNats notInCons
  in absurd $ subPrf there

data Ambiente : List String -> Type where
  MkAmbiente : Record {lty=String} (AllNats ls) -> Ambiente ls

ifAppendIsSubSetThenSoIsTheRight : DecEq lty => {ls1, ls2, ls3 : List lty} -> IsSubSet (ls1 ++ ls2) ls3 -> IsSubSet ls2 ls3

ifIsSubSetThenLeftUnionIsSubSet : DecEq lty => {ls1, ls2, lsSub1, lsSub2 : List lty} -> IsSubSet ls1 ls2 -> 
  IsLeftUnion_List lsSub1 lsSub2 ls1 -> (IsSubSet lsSub1 ls2, IsSubSet lsSub2 ls2)
ifIsSubSetThenLeftUnionIsSubSet subSet (IsLeftUnionAppend_List delLabels) = (isSubSetLeft subSet delLabels, isSubSetRight subSet delLabels)
  where
    isSubSetLeft :  DecEq lty => {rs2, rs3, rsSub1, rsSub2 : List lty} -> IsSubSet (rSub1 ++ rs3) rs2 -> 
  DeleteLabelsPred_List rsSub1 rsSub2 rs3 -> IsSubSet rsSub1 rs2
    isSubSetLeft {rsSub1 = []} _ _ = IsSubSetNil
    isSubSetLeft {rsSub1 = r :: rsSub1} subSet1 (DeleteFirstOfLabelList_List delAt delLabels) = ?isSubSetLeft_rhs_2_2x
    
    isSubSetRight :  DecEq lty => {rs2, rs3, rsSub1, rsSub2 : List lty} -> IsSubSet (rSub1 ++ rs3) rs2 -> 
  DeleteLabelsPred_List rsSub1 rsSub2 rs3 -> IsSubSet rsSub2 rs2
    isSubSetRight {rsSub1 = []} subSet2 EmptyLabelList_List = ifAppendIsSubSetThenSoIsTheRight subSet2
    isSubSetRight {rsSub1 = r :: rsSub1} subSet2 (DeleteFirstOfLabelList_List delAt delLabels) = ?isSubSetRight_rhs_1_2

-- NOTA: No puede parametrizarse por cualquier tipo Type porque necesitaria poder comparar sus tipos. Ej un "t1 : Type" y "t2 : Type" no necesariamente serian el mismo, y no es decidible igualarlos
ifHasFieldInElemThenItHasThere : DecEq lty => {ls : List lty} -> Elem l ls -> HasField l (AllNats ls) Nat
ifHasFieldInElemThenItHasThere {ls = []} elem = absurd $ noEmptyElem elem
ifHasFieldInElemThenItHasThere {l = l2} {ls = l2 :: ls} Here = HasFieldHere
ifHasFieldInElemThenItHasThere {l = l1} {ls = l2 :: ls} (There later) = HasFieldThere $ ifHasFieldInElemThenItHasThere later

-- NOTA: No puede parametrizarse por cualquier tipo Type porque necesitaria poder comparar sus tipos. Ej un "t1 : Type" y "t2 : Type" no necesariamente serian el mismo, y no es decidible igualarlos
ifIsSubSetThenHasFieldInIt : DecEq lty => {ls1, ls2 : List lty} -> IsSubSet ls1 ls2 -> 
  HasField l (AllNats ls1) Nat -> HasField l (AllNats ls2) Nat
ifIsSubSetThenHasFieldInIt {ls1 = []} _ hasField = absurd $ noEmptyHasField hasField
ifIsSubSetThenHasFieldInIt {l=l1} {ls1 = (l2 :: ls1)} subSet hasField with (decEq l1 l2)
  ifIsSubSetThenHasFieldInIt {l=l1} {ls1 = (l1 :: ls1)} (IsSubSetCons subSet elem) hasField | Yes Refl = 
    ifHasFieldInElemThenItHasThere elem
  ifIsSubSetThenHasFieldInIt {l=l1} {ls1 = (l1 :: ls1)} (IsSubSetCons subSet elem) HasFieldHere | No notL1EqL2 = absurd $ notL1EqL2 Refl
  ifIsSubSetThenHasFieldInIt {l=l1} {ls1 = (l2 :: ls1)} (IsSubSetCons subSet elem) (HasFieldThere hasFieldThere) | No notL1EqL2 = 
    ifIsSubSetThenHasFieldInIt subSet hasFieldThere

ifIsSubSetThenIsSubSetOfCons : IsSubSet ls1 ls2 -> IsSubSet ls1 (l :: ls2)
ifIsSubSetThenIsSubSetOfCons IsSubSetNil = IsSubSetNil
ifIsSubSetThenIsSubSetOfCons {l=l1} (IsSubSetCons {l=l2} subSet l1InLs2) = 
  let subPrf = ifIsSubSetThenIsSubSetOfCons subSet
  in IsSubSetCons subPrf (There l1InLs2)

ifDeleteLabelFromSetThenIsNotElem : DeleteLabelAtPred_List l ls1 ls2 -> IsSet ls1 -> Not (Elem l ls2)

ifConsIsElemThenIsSubSet : IsSubSet ls1 (l :: ls2) -> Elem l ls2 -> IsSubSet ls1 ls2

ifIsSubSetThenSoIfYouDeleteLabel : DeleteLabelAtPred_List l ls1 ls3 -> IsSubSet ls3 ls2 -> IsSubSet ls1 (l :: ls2)

ifListsAreSetThenLeftUnionIsSet : IsLeftUnion_List ls1 ls2 ls3 -> IsSet ls1 -> IsSet ls2 -> IsSet ls3

ifIsSetThenDeleteAtIsSet : DeleteLabelAtPred_List l ls1 ls2 -> IsSet ls1 -> IsSet ls2

expIsSet : Exp fvs -> IsSet fvs
expIsSet (Add e1 e2 fvsLeftUnion) =
  let e1IsSet = expIsSet e1
      e2IsSet = expIsSet e2
  in ifListsAreSetThenLeftUnionIsSet fvsLeftUnion e1IsSet e2IsSet
expIsSet (Var l) = IsSetCons noEmptyElem IsSetNil
expIsSet (Cons n) = IsSetNil
expIsSet (Let (v := n) e delAt) = ifIsSetThenDeleteAtIsSet delAt $ expIsSet e

ifIsElemThenHasFieldNat : Elem l ls -> HasField l (AllNats ls) Nat
ifIsElemThenHasFieldNat Here = HasFieldHere
ifIsElemThenHasFieldNat (There later) = HasFieldThere $ ifIsElemThenHasFieldNat later

-- Interpreta una expresion dado un ambiente con valores para cada variable
interpEnv : Ambiente fvsEnv -> IsSubSet fvs fvsEnv -> Exp fvs -> Nat
interpEnv env subSet (Add e1 e2 isUnionFvs) = 
  -- La union es un subconjunto del ambiente, entonces se interpretan por separado y se suman
  let (subSet1, subSet2) = ifIsSubSetThenLeftUnionIsSubSet subSet isUnionFvs
      res1 = interpEnv env subSet1 e1
      res2 = interpEnv env subSet2 e2
  in res1 + res2
interpEnv {fvsEnv} (MkAmbiente rec) subSet (Var l) = 
  -- Al ser un subconjunto del ambiente, la variable existe en el y se puede obtener
  let hasField = HasFieldHere {l} {ty = Nat} {ts = []}
      hasFieldInEnv = ifIsSubSetThenHasFieldInIt  subSet hasField
  in hLookupByLabel l rec hasFieldInEnv
interpEnv env subSet (Cons c) = c
interpEnv {fvsEnv} env subSet (Let (var := n) e delAt) with (isElem var fvsEnv)
  -- Si la variable existe en el ambiente, entonces se sustituye su valor y se interpreta la subexpresion con ese nuevo ambiente
  interpEnv {fvsEnv} env subSet (Let (var := n) e delAt) | Yes varInEnv = 
    let
        -- Se actualiza el ambiente con el valor de la variable
        (MkAmbiente recEnv) = env
        hasField = ifIsElemThenHasFieldNat varInEnv 
        newRec = hUpdateAtLabel var n recEnv hasField
        newEnv = MkAmbiente newRec
        
        -- Conociendo que las variables libres son un conjunto, se prueba que el inner es subconjunto del ambiente
        fvsInnerIsSet = expIsSet e
        notVarInFvs = ifDeleteLabelFromSetThenIsNotElem delAt fvsInnerIsSet
        consSubSet = ifIsSubSetThenSoIfYouDeleteLabel delAt subSet {l = var}
        newSubSet = ifConsIsElemThenIsSubSet consSubSet varInEnv
    in interpEnv newEnv newSubSet e
    
  -- Si la variable no existe en el ambiente, se le agrega y se interpreta la subexpresion con ese nuevo ambiente
  interpEnv {fvsEnv} env subSet (Let (var := n) e delAt) | No notVarInEnv = 
    let (MkAmbiente recEnv) = env
        newRec = consRec var n recEnv {notElem = ifNotElemThenNotInNats notVarInEnv}
        newEnv = MkAmbiente newRec {ls = (var :: fvsEnv)}
        newSubSet = ifIsSubSetThenSoIfYouDeleteLabel delAt subSet {l = var}
    in interpEnv newEnv newSubSet e


{-interpEnv (MkAmbiente rec) (Add e1 e2 isUnionFvs) = 
  let (recE1, recE2) = splitRecordByUnionList isUnionFvs rec
      interpE1 = interpEnv (MkAmbiente recE1) e1
      interpE2 = interpEnv (MkAmbiente recE2) e2
   in interpE1 + interpE2
interpEnv (MkAmbiente rec) (Var l) = hLookupByLabel l rec HasFieldHere
interpEnv env (Cons c) = c
interpEnv env (Local vars subExp isSet prjRight) = 
  let isSetInner = expIsSet subExp
      newEnv = addLocalVarsToEnv env prjRight vars isSetInner
  in interpEnv newEnv subExp -}
  
  
interp : Exp [] -> Nat
interp = interpEnv (MkAmbiente {ls=[]} emptyRec) IsSubSetNil

{-

ifNotElemThenNotElemNats : Not (Elem x xs) -> Not (ElemLabel x (AllNats xs))
ifNotElemThenNotElemNats {xs = []} notXInXs xInLabelXs = absurd $ noEmptyElem xInLabelXs
ifNotElemThenNotElemNats {xs = x1 :: xs} notXInXs Here = notXInXs Here
ifNotElemThenNotElemNats {xs = x1 :: xs} notXInXs (There there) = 
  let notInCons = notElemInCons notXInXs
      subPrf = ifNotElemThenNotElemNats notInCons
  in absurd $ subPrf there

getTailFromRecord : Record (l :: ls) -> Record ls
getTailFromRecord (MkRecord (IsSetCons notElem isSet) (n :: ns)) = MkRecord isSet ns

ifDelLabelAtThenNotElemInRes : DeleteLabelAtPred_List l ls1 ls2 -> IsSet ls1 -> Not (Elem l ls2)
ifDelLabelAtThenNotElemInRes EmptyRecord_List _ lInLs2 = noEmptyElem lInLs2
ifDelLabelAtThenNotElemInRes IsElem_List (IsSetCons notLInLs2 _) lInLs2 = notLInLs2 lInLs2
ifDelLabelAtThenNotElemInRes (IsNotElem_List notEq _) (IsSetCons _ _) Here = notEq Refl
ifDelLabelAtThenNotElemInRes (IsNotElem_List _ delAt) (IsSetCons _ ls1IsSet) (There there) = 
  ifDelLabelAtThenNotElemInRes delAt ls1IsSet there

ifNotInEitherThenNotInAppendList : Not (Elem x xs1) -> Not (Elem x xs2) -> Not (Elem x (xs1 ++ xs2))
ifNotInEitherThenNotInAppendList {xs1 = []} _ notXInXs2 xInAppend = notXInXs2 xInAppend
ifNotInEitherThenNotInAppendList {xs1 = x1 :: xs1} notXInXs1 _ Here = notXInXs1 Here
ifNotInEitherThenNotInAppendList {xs1 = x1 :: xs1} notXInXs1 notXInXs2 (There there) =
  ifNotInEitherThenNotInAppendList (notElemInCons notXInXs1) notXInXs2 there


ifNotInAppendThenNotInLists : Not (Elem x (xs1 ++ xs2)) -> (Not (Elem x xs1), Not (Elem x xs2))
ifNotInAppendThenNotInLists notElem = (lemmaLeft notElem, lemmaRight notElem)
  where
    lemmaLeft : Not (Elem y (ys1 ++ ys2)) -> Not (Elem y ys1)
    lemmaLeft {ys1 = []} notYInApp yInYs1 = noEmptyElem yInYs1
    lemmaLeft {ys1 = y1 :: ys1} notYInApp Here = notYInApp Here
    lemmaLeft {ys1 = y1 :: ys1} notYInApp (There there) = 
      let subPrf = lemmaLeft {ys1} (notElemInCons notYInApp) 
      in subPrf there
    
    lemmaRight : Not (Elem y (ys1 ++ ys2)) -> Not (Elem y ys2)
    lemmaRight {ys1 = []} notYInApp yInYs1 = notYInApp yInYs1
    lemmaRight {ys1 = y1 :: ys1} notYInApp yInYs1 = lemmaRight (notElemInCons notYInApp) yInYs1

ifAppendIsSetThenListsAreSet : IsSet (xs1 ++ xs2) -> (IsSet xs1, IsSet xs2)
ifAppendIsSetThenListsAreSet isSet = (lemmaLeft isSet, lemmaRight isSet)
  where
    lemmaLeft : IsSet (ys1 ++ ys2) -> IsSet ys1
    lemmaLeft {ys1 = []} appIsSet = IsSetNil
    lemmaLeft {ys1 = y1 :: ys1} (IsSetCons notElem appIsSet) = 
      let subPrf = lemmaLeft appIsSet
          (notY1InYs1, _) = ifNotInAppendThenNotInLists notElem
      in  IsSetCons notY1InYs1 subPrf
    
    lemmaRight : IsSet (ys1 ++ ys2) -> IsSet ys2
    lemmaRight {ys1 = []} appIsSet = appIsSet
    lemmaRight {ys1 = y1 :: ys1} (IsSetCons notElem appIsSet) = lemmaRight appIsSet
    

--ifListsAreSetThenAppendIsSet : IsSet xs1 -> IsSet xs2 -> IsSet (xs1 ++ xs2)

ifListsAreSetThenLeftUnionIsSet_Lemma_1_1_1 : Not (Elem x1 (xs1 ++ x :: xs2)) -> Not (Elem x1 (xs1 ++ xs2))
ifListsAreSetThenLeftUnionIsSet_Lemma_1_1_1 {xs1 = []} notElem x1InAppend = notElemInCons notElem x1InAppend
ifListsAreSetThenLeftUnionIsSet_Lemma_1_1_1 {xs1 = x2 :: xs1} notElem Here = notElem Here
ifListsAreSetThenLeftUnionIsSet_Lemma_1_1_1 {xs1 = x2 :: xs1} notElem (There there) =
  ifListsAreSetThenLeftUnionIsSet_Lemma_1_1_1 (notElemInCons notElem) there

ifListsAreSetThenLeftUnionIsSet_Lemma_1_1 : IsSet (xs1 ++ x :: xs2) -> IsSet (xs1 ++ xs2)
ifListsAreSetThenLeftUnionIsSet_Lemma_1_1 {xs1 = []} (IsSetCons _ isSet) = isSet
ifListsAreSetThenLeftUnionIsSet_Lemma_1_1 {xs1 = x1 :: xs1} (IsSetCons notElem isSet) = 
  let subPrf = ifListsAreSetThenLeftUnionIsSet_Lemma_1_1 isSet
      notElemRes = ifListsAreSetThenLeftUnionIsSet_Lemma_1_1_1 notElem
  in IsSetCons notElemRes subPrf

-- ifDelLabelAtThenNotElemInRes : DeleteLabelAtPred_List l ls1 ls2 -> IsSet ls1 -> Not (Elem l ls2)

--ifListsAreSetThenLeftUnionIsSet_Lemma_1_2 : IsSet (ls1 ++ ls3) -> IsSet (ls1 ++ l2 :: ls2) -> IsSet (ls1 ++ l2 :: ls3)

-- TODO: Ver como probar este de abajo.
ifListsAreSetThenLeftUnionIsSet_Lemma_1 : DeleteLabelAtPred_List l ls2 ls3 -> IsSet (ls1 ++ ls2) -> IsSet (ls1 ++ ls3)
ifListsAreSetThenLeftUnionIsSet_Lemma_1 EmptyRecord_List isSetAppend = isSetAppend
ifListsAreSetThenLeftUnionIsSet_Lemma_1 IsElem_List isSetAppend = ifListsAreSetThenLeftUnionIsSet_Lemma_1_1 isSetAppend
ifListsAreSetThenLeftUnionIsSet_Lemma_1 {ls1} {ls2 = l2 :: ls2} {ls3 = l2 :: ls3} (IsNotElem_List notEq delAt) isSetAppend = 
  let ls1AppLs2IsSet = ifListsAreSetThenLeftUnionIsSet_Lemma_1_1 {xs1=ls1} {xs2=ls2} isSetAppend
      subPrf = ifListsAreSetThenLeftUnionIsSet_Lemma_1 {ls1} delAt ls1AppLs2IsSet
      --(ls1IsSet, ls2IsSet) = ifAppendIsSetThenListsAreSet ls1AppLs2IsSet
      --(_, ls3IsSet) = ifAppendIsSetThenListsAreSet subPrf
      --notL2InLs3 = ifDelLabelAtThenNotElemInRes delAt ls2IsSet
  --in ifListsAreSetThenLeftUnionIsSet_Lemma_1_2 subPrf isSetAppend
  in ?listSetDelAt_rhs
  --in ifListsAreSetThenAppendIsSet ls1IsSet (IsSetCons notL2InLs3 ls3IsSet) 

ifListsAreSetThenLeftUnionIsSet : IsLeftUnion_List ls1 ls2 ls3 -> IsSet ls1 -> IsSet ls2 -> IsSet ls3
ifListsAreSetThenLeftUnionIsSet (IsLeftUnionAppend_List EmptyLabelList_List) ls1IsSet ls2IsSet = ls2IsSet
ifListsAreSetThenLeftUnionIsSet {ls1 = l :: ls1} (IsLeftUnionAppend_List (DeleteFirstOfLabelList_List delAt delLabels)) 
  (IsSetCons notLInLs1 ls1IsSet) ls2IsSet = 
  let subLeftUnion = (IsLeftUnionAppend_List delLabels)
      subPrf = ifListsAreSetThenLeftUnionIsSet subLeftUnion ls1IsSet ls2IsSet
      (_, lsAuxIsSet) = ifAppendIsSetThenListsAreSet subPrf
      ls1AppLs3IsSet = ifListsAreSetThenLeftUnionIsSet_Lemma_1 {ls1} delAt subPrf
      notLInLs3 = ifDelLabelAtThenNotElemInRes delAt lsAuxIsSet
      notLInRes = ifNotInEitherThenNotInAppendList notLInLs1 notLInLs3
  in IsSetCons notLInRes ls1AppLs3IsSet
  
ifNotInListThenNotInProjectRight : IsProjectRight_List ls1 ls2 ls3 -> Not (Elem l ls2) -> Not (Elem l ls3)
ifNotInListThenNotInProjectRight IPR_EmptyLabels_List notLInLs2 lInLs3 = notLInLs2 lInLs3 
ifNotInListThenNotInProjectRight IPR_EmptyVect_List notLInLs2 lInLs3 = notLInLs2 lInLs3
ifNotInListThenNotInProjectRight (IPR_ProjLabelElem_List isElem delElem prjRight) notLInLs2 lInLs3 = 
  ifNotInListThenNotInProjectRight prjRight (notElemInCons notLInLs2) lInLs3
ifNotInListThenNotInProjectRight (IPR_ProjLabelNotElem_List notElem prjRight) notLInLs2 Here = notLInLs2 Here
ifNotInListThenNotInProjectRight (IPR_ProjLabelNotElem_List notElem prjRight) notLInLs2 (There there) = 
  ifNotInListThenNotInProjectRight prjRight (notElemInCons notLInLs2) there
 

ifListIsSetThenProjectRightIsSet : IsProjectRight_List ls1 ls2 ls3 -> IsSet ls2 -> IsSet ls3
ifListIsSetThenProjectRightIsSet IPR_EmptyLabels_List isSet = isSet
ifListIsSetThenProjectRightIsSet IPR_EmptyVect_List isSet = isSet
ifListIsSetThenProjectRightIsSet (IPR_ProjLabelElem_List lInLs1 delElem prjRight) (IsSetCons notLInLs2 ls2IsSet) = 
  ifListIsSetThenProjectRightIsSet prjRight ls2IsSet
ifListIsSetThenProjectRightIsSet (IPR_ProjLabelNotElem_List notLInLs1 prjRight) (IsSetCons notLInLs2 ls2IsSet) =
  let subPrf = ifListIsSetThenProjectRightIsSet prjRight ls2IsSet
      notLInRes = ifNotInListThenNotInProjectRight prjRight notLInLs2
  in IsSetCons notLInRes subPrf
  
expIsSet : {fvs : List String} -> Exp fvs -> IsSet fvs
expIsSet (Add e1 e2 fvsLeftUnion) =
  let e1IsSet = expIsSet e1
      e2IsSet = expIsSet e2
  in ifListsAreSetThenLeftUnionIsSet fvsLeftUnion e1IsSet e2IsSet
expIsSet (Var l) = IsSetCons noEmptyElem IsSetNil
expIsSet (Cons n) = IsSetNil
expIsSet (Local vars e varsIsSet prjRight) = 
  let eIsSet = expIsSet e
  in ifListIsSetThenProjectRightIsSet prjRight eIsSet


-- Interpreta una expresion dado un ambiente con valores para cada variable
interpEnv : Ambiente fvs -> Exp fvs -> Nat
interpEnv (MkAmbiente rec) (Add e1 e2 isUnionFvs) = 
  let (recE1, recE2) = splitRecordByUnionList isUnionFvs rec
      interpE1 = interpEnv (MkAmbiente recE1) e1
      interpE2 = interpEnv (MkAmbiente recE2) e2
   in interpE1 + interpE2
interpEnv (MkAmbiente rec) (Var l) = hLookupByLabel l rec HasFieldHere
interpEnv env (Cons c) = c
interpEnv env (Local vars subExp isSet prjRight) = 
  let isSetInner = expIsSet subExp
      newEnv = addLocalVarsToEnv env prjRight vars isSetInner
  in interpEnv newEnv subExp
  
  
interp : Exp [] -> Nat
interp = interpEnv (MkAmbiente {ls=[]} emptyRec)
    

-}


-- *** Ejemplos ***
expTest1 : Exp ["x", "y"]
expTest1 = add (var "x") (add (cons 1) (var "y"))

expTest2 : Exp []
expTest2 = local ["x" := 10] $ cons 1

expTest3 : Exp []
expTest3 = local (["x" := 10, "y" := 9]) $ add (var "x") (var "y")

expTest4 : Exp []
expTest4 = eLet ("x" := 10) $ var "x"

expTest5 : Exp ["y"]
expTest5 = eLet ("x" := 10) $ add (var "x") (var "y")

expTest6 : Exp []
expTest6 = eLet ("y" := 5) expTest5
