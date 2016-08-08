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
    

-- *** Ejemplos ***
expTest1 : Exp ["x", "y"] []
expTest1 = add (var "x") (add (cons 1) (var "y"))

expTest2 : Exp [] ["x"]
expTest2 = local ["x" := 10] $ cons 1

expTest3 : Exp [] ["x", "y"]
expTest3 = local (["x" := 10, "y" := 9]) $ add (var "x") (var "y")


-- VIEJO
{-data Exp = 
  Add Exp Exp -- Suma de expresiones
  | Var String -- Definición de variables
  | Const Nat -- Constantes numéricas
  | Local (List (String, Nat)) Exp -- Definición de ambientes locales, con definiciones de variables con solo constantes -}

-- Predicado que indica que una lista de labels siempre tiene el mismo tipo
--data AllHaveType : LabelList lty -> Type -> Type where
--  AllHaveTypeNil : AllHaveType [] ty
--  AllHaveTypeCons : AllHaveType ts ty -> AllHaveType ((l, ty) :: ts) ty 
  
-- Builder de expresiones parametrizado por la lista de variables libres de la expresión
--TODO: Ver como definir bien
{-data ExpBuilder : LabelList String -> Exp -> Type where
  AddBuilder : IsLeftUnion ts1 ts2 tsRes -> ExpBuilder ts1 e1 -> ExpBuilder ts2 e2 -> ExpBuilder tsRes (Add e1 e2)
  VarBuilder : ExpBuilder [(l, Nat)] (Var l)
  ConstBuilder : ExpBuilder [] (Const n)
  LocalBuilder : 
                 -- Las variables locales definidas no deben repetirse
                 IsLabelSet lsRes -> 
                 --
                 IsProjectRight ts1 lsRes tsRes ->
                 ExpBuilder ts1 eSub -> 
                 ExpBuilder tsRes (Local lsRes eSub) -}

{-data IsProjectLeft : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type where
  IPL_EmptyLabels : DecEq lty => IsProjectLeft {lty=lty} [] ts []
  IPL_EmptyVect : DecEq lty => IsProjectLeft {lty=lty} ls [] []
  IPL_ProjLabelElem : DecEq lty => (isElem : Elem (fst t) ls) -> DeleteElemPred ls isElem lsNew ->
                      IsProjectLeft {lty=lty} lsNew ts res1 -> IsProjectLeft ls (t :: ts) (t :: res1)      
  IPL_ProjLabelNotElem : DecEq lty => Not (Elem (fst t) ls) -> IsProjectLeft {lty=lty} ls ts res1 -> 
                       IsProjectLeft ls (t :: ts) res1

-- Predicado que indica que la proyección derecha de un hProjectByLabels es efectivamente tal proyección    
data IsProjectRight : DecEq lty => List lty -> LabelList lty -> LabelList lty -> Type where
  IPR_EmptyLabels : DecEq lty => IsProjectRight {lty=lty} [] ts ts
  IPR_EmptyVect : DecEq lty => IsProjectRight {lty=lty} ls [] []
  IPR_ProjLabelElem : DecEq lty => (isElem : Elem (fst t) ls) -> DeleteElemPred ls isElem lsNew ->
                      IsProjectRight {lty=lty} lsNew ts res1 -> IsProjectRight ls (t :: ts) res1      
  IPR_ProjLabelNotElem : DecEq lty => Not (Elem (fst t) ls) -> IsProjectRight {lty=lty} ls ts res1 -> 
                       IsProjectRight ls (t :: ts) (t :: res1)-}

-- Ambiente local de valores de expresiones. Se trata de un record extensibles de valores de variables, cuyos valores solo pueden
-- ser Nat
--data Ambiente : LabelList String -> Type where
--  IsEnv : AllHaveType ts Nat -> Record {lty=String} ts -> Ambiente ts

-- TODO: Ver como ir agregando con "consRec" y que compile
{-addLocalDefinitions : Ambiente tsIn -> List (String, Nat) -> (tsOut : LabelList String ** Ambiente tsOut)
addLocalDefinitions envIn ls = ?addLocalDefinitions_rhs  -}
  
-- TODO: Ver como interpretar una variable como string
{-interpVariable : Ambiente ts -> String -> Nat
interpVariable env var = ?interpVariable_rhs-}
  
-- Intérprete
{-interp : Ambiente ts -> Exp -> Nat
interp env (Add e1 e2) = (interp env e1) + (interp env e2)
-- Aca necesitaria una prueba de que 'v' esta en el ambiente, para hacer lookup 
interp env (Var var) = interpVariable env var
interp env (Const c) = c
interp {ts} env (Local def e) = 
  let (tsOut ** subEnv) = addLocalDefinitions {tsIn=ts} env def
  in interp {ts=tsOut} subEnv e-}
 
    
