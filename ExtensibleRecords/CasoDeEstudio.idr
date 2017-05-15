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
      
-- Arbol sintactico del lenguaje de expresiones aritmeticas
data VarDec : String -> Type where
  (:=) : (var : String) -> Nat -> VarDec var

infixr 2 :=

-- fvs: Lista de variables libres
data Exp : List String -> Type where
  Add : Exp fvs1 -> Exp fvs2 -> IsLeftUnion_List fvs1 fvs2 fvsRes -> Exp fvsRes 
  Var : (l : String) -> Exp [l]
  Lit : Nat -> Exp []
  Let : VarDec var -> Exp fvsInner -> DeleteLabelAtPred_List var fvsInner fvsOuter -> Exp fvsOuter
  
-- DSL del lenguaje
var : (l : String) -> Exp [l]
var l = Var l

lit : Nat -> Exp []
lit n = Lit n

add : Exp fvs1 -> Exp fvs2 -> Exp (leftUnion fvs1 fvs2)
add {fvs1} {fvs2} e1 e2 = Add e1 e2 (fromLeftUnionFuncToPred {ls1=fvs1} {ls2=fvs2})

eLet : VarDec var -> Exp fvs -> Exp (deleteAtList var fvs)
eLet {var} {fvs} varDec e = Let varDec e (fromDeleteLabelAtListFuncToPred {l=var} {ls=fvs})

data LocalVariables : List String -> Type where
  Nil : LocalVariables []
  (::) : VarDec l -> LocalVariables ls -> LocalVariables (l :: ls)  

localPred : (vars : LocalVariables localVars) -> (innerExp : Exp fvsInner) -> 
  {isSet : IsSet localVars} -> Exp (deleteList localVars fvsInner)
localPred {localVars=[]} {fvsInner} _ innerExp = innerExp
localPred {localVars=l :: localVars} (varDec :: vars) innerExp {isSet = (IsSetCons _ isSet)} = 
  let subExp = localPred vars innerExp {isSet}
  in eLet varDec subExp

local : (vars : LocalVariables localVars) -> (innerExp : Exp fvsInner) ->
  TypeOrUnit (isSet localVars) (Exp (deleteList localVars fvsInner))
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

ifAppendIsSubSetThenSoIsEach : DecEq lty => {ls1, ls2, ls3 : List lty} -> IsSubSet (ls1 ++ ls2) ls3 ->
  (IsSubSet ls1 ls3, IsSubSet ls2 ls3)
ifAppendIsSubSetThenSoIsEach {ls1=[]} subSet = (IsSubSetNil, subSet)
ifAppendIsSubSetThenSoIsEach {ls1=l1::ls1} {ls2} {ls3} (IsSubSetCons subSet elem) = 
  let (subPrfLeft, subPrfRight) = ifAppendIsSubSetThenSoIsEach {ls1} {ls2} {ls3} subSet
  in (IsSubSetCons subPrfLeft elem, subPrfRight)

ifIsSubSetOfEachThenIsSoAppend : DecEq lty => {ls1, ls2, ls3 : List lty} -> IsSubSet ls1 ls3 -> 
  IsSubSet ls2 ls3 -> IsSubSet (ls1 ++ ls2) ls3
ifIsSubSetOfEachThenIsSoAppend {ls1 = []} subSetLs1 subSetLs2 = subSetLs2
ifIsSubSetOfEachThenIsSoAppend {ls1 = l1 :: ls1} (IsSubSetCons subSetLs1 l1InLs3) subSetLs2 = 
  let subPrf = ifIsSubSetOfEachThenIsSoAppend subSetLs1 subSetLs2
  in IsSubSetCons subPrf l1InLs3
  
ifIsSubSetThenLeftUnionIsSubSet_Lemma_1 : DecEq lty => {ls1, ls2, ls3, ls4 : List lty} -> IsSubSet (ls1 ++ ls2) ls3 -> 
  Elem l ls3 -> DeleteLabelAtPred_List l ls4 ls2 -> IsSubSet (ls1 ++ ls4) ls3
ifIsSubSetThenLeftUnionIsSubSet_Lemma_1 subSet elem EmptyRecord_List = subSet
ifIsSubSetThenLeftUnionIsSubSet_Lemma_1 subSet elem IsElem_List = 
  let
    (ls1SubSetLs3, ls2SubSetLs3) = ifAppendIsSubSetThenSoIsEach subSet
    ls2ConsSubSetLs3 = IsSubSetCons ls2SubSetLs3 elem
  in ifIsSubSetOfEachThenIsSoAppend ls1SubSetLs3 ls2ConsSubSetLs3
ifIsSubSetThenLeftUnionIsSubSet_Lemma_1 subSet lInLs3 (IsNotElem_List notEq delAt) = 
  let
    (ls1SubSetLs3, ls2ConsSubSetLs3) = ifAppendIsSubSetThenSoIsEach subSet
    IsSubSetCons ls2SubSetLs3 l2InLs3 = ls2ConsSubSetLs3
    ls1AppLs2SubSetLs3 = ifIsSubSetOfEachThenIsSoAppend ls1SubSetLs3 ls2SubSetLs3
    subPrf = ifIsSubSetThenLeftUnionIsSubSet_Lemma_1 ls1AppLs2SubSetLs3 lInLs3 delAt
    (_, ls4SubSetLs3) = ifAppendIsSubSetThenSoIsEach subPrf
    ls4ConsSubSetLs3 = IsSubSetCons ls4SubSetLs3 l2InLs3
  in ifIsSubSetOfEachThenIsSoAppend ls1SubSetLs3 ls4ConsSubSetLs3
  
ifIsSubSetThenLeftUnionIsSubSet_Lemma_2 : DecEq lty => {ls1, ls2, ls3, ls4 : List lty} -> IsSubSet (ls1 ++ ls2) ls3 ->
  DeleteLabelsPred_List ls1 ls4 ls2 -> IsSubSet ls4 ls3
ifIsSubSetThenLeftUnionIsSubSet_Lemma_2 {ls1=[]} subSet EmptyLabelList_List = subSet
ifIsSubSetThenLeftUnionIsSubSet_Lemma_2 {ls1=l1 :: ls1} (IsSubSetCons subSet elem) (DeleteFirstOfLabelList_List delAt delLabels) = 
  let isSubSetAux = ifIsSubSetThenLeftUnionIsSubSet_Lemma_1 subSet elem delAt
  in ifIsSubSetThenLeftUnionIsSubSet_Lemma_2 isSubSetAux delLabels 
  
ifIsSubSetThenLeftUnionIsSubSet : DecEq lty => {ls1, ls2, lsSub1, lsSub2 : List lty} -> IsSubSet ls1 ls2 -> 
  IsLeftUnion_List lsSub1 lsSub2 ls1 -> (IsSubSet lsSub1 ls2, IsSubSet lsSub2 ls2)
ifIsSubSetThenLeftUnionIsSubSet subSet (IsLeftUnionAppend_List delLabels) = (isSubSetLeft subSet delLabels, isSubSetRight subSet delLabels)
  where
    isSubSetLeft :  DecEq lty => {rs2, rs3, rsSub1, rsSub2 : List lty} -> IsSubSet (rsSub1 ++ rs3) rs2 -> 
  DeleteLabelsPred_List rsSub1 rsSub2 rs3 -> IsSubSet rsSub1 rs2
    isSubSetLeft {rsSub1} {rs3} {rs2} subSet delLabels = fst $ ifAppendIsSubSetThenSoIsEach subSet
    
    isSubSetRight :  DecEq lty => {rs2, rs3, rsSub1, rsSub2 : List lty} -> IsSubSet (rsSub1 ++ rs3) rs2 -> 
  DeleteLabelsPred_List rsSub1 rsSub2 rs3 -> IsSubSet rsSub2 rs2
    isSubSetRight {rsSub1 = []} subSet2 EmptyLabelList_List = subSet2
    isSubSetRight {rsSub1 = r :: rsSub1} (IsSubSetCons subSet elem) (DeleteFirstOfLabelList_List delAt delLabels) = 
      let auxIsSubSet = ifIsSubSetThenLeftUnionIsSubSet_Lemma_1 subSet elem delAt
      in ifIsSubSetThenLeftUnionIsSubSet_Lemma_2 auxIsSubSet delLabels
      
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

ifIsSubSetThenIsSubSetWhenAddingElem : IsSubSet ls1 ls2 -> IsSubSet (l :: ls1) (l :: ls2)
ifIsSubSetThenIsSubSetWhenAddingElem subSet = IsSubSetCons (ifIsSubSetThenIsSubSetOfCons subSet) Here

ifConsIsElemThenIsSubSet : IsSubSet ls1 (l :: ls2) -> Elem l ls2 -> IsSubSet ls1 ls2
ifConsIsElemThenIsSubSet IsSubSetNil isElem = IsSubSetNil
ifConsIsElemThenIsSubSet (IsSubSetCons isSubSet Here) isElem = 
  let subPrf = ifConsIsElemThenIsSubSet isSubSet isElem
  in IsSubSetCons subPrf isElem
ifConsIsElemThenIsSubSet (IsSubSetCons isSubSet (There later)) isElem = 
  let subPrf = ifConsIsElemThenIsSubSet isSubSet isElem
  in IsSubSetCons subPrf later

ifIsSubSetThenSoIfYouDeleteLabel : DeleteLabelAtPred_List l ls1 ls3 -> IsSubSet ls3 ls2 -> IsSubSet ls1 (l :: ls2)
ifIsSubSetThenSoIfYouDeleteLabel EmptyRecord_List subSet = IsSubSetNil
ifIsSubSetThenSoIfYouDeleteLabel IsElem_List subSet = ifIsSubSetThenIsSubSetWhenAddingElem subSet
ifIsSubSetThenSoIfYouDeleteLabel (IsNotElem_List notEq delAt) (IsSubSetCons subSet elem) = 
  let subPrf = ifIsSubSetThenSoIfYouDeleteLabel delAt subSet
  in IsSubSetCons subPrf (There elem)

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
interpEnv env subSet (Lit c) = c
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
  
interp : Exp [] -> Nat
interp = interpEnv (MkAmbiente {ls=[]} emptyRec) IsSubSetNil
