{-
  Caso de estudio de records extensibles en Idris.
  
  Este caso consiste en diseñar un mini-lenguaje de programación que permita definir expresiones aritméticas utilizando variables con alcance local, y diseñar un intérprete de ese lenguaje utilizando records extensibles.

-}

module CasoDeEstudio

import Data.List
import Extensible_Records

%default total

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

hLeftUnion_List : DecEq lty => LabelList lty -> LabelList lty -> LabelList lty

fromHLeftUnionFuncToPred : DecEq lty => (ts1 : LabelList lty) -> (ts2 : LabelList lty) -> IsLeftUnion ts1 ts2 (hLeftUnion_List ts1 ts2)    
-}

-- Arbol sintactico del lenguaje de expresiones aritmeticas
data Exp : LabelList String -> Type where
  Add : Exp ts1 -> Exp ts2 -> IsLeftUnion ts1 ts2 tsRes -> Exp tsRes
  Var : (l : String) -> Exp [(l, Nat)]
  Cons : Nat -> Exp []
  Local : Exp tsSub -> IsLabelSet tsLocal -> IsProjectRight (labelsOf tsLocal) tsSub tsOuter -> Exp tsOuter

-- DSL del lenguaje
var : (l : String) -> Exp [(l, Nat)]
var l = Var l

cons : Nat -> Exp []
cons n = Cons n

add : Exp ts1 -> Exp ts2 -> Exp (hLeftUnion_List ts1 ts2)
add {ts1} {ts2} e1 e2 = Add e1 e2 (fromHLeftUnionFuncToPred {ts1} {ts2})

-- TODO: Ver como hacer para que en vez de "LabelList String" sea "List String" y use otros hLeftUnion/etc
-- Eso para que sea mas simple
-- TODO: Ademas falta agregar otra estructura que tenga los "x:=10,y:=11" en el Local

expTest : ?Exp_Type_1
expTest = add (var "x") (add (cons 1) (var "y"))
--TODO: Ver como Idris "calcula" automaticamente ese tipo, con "proof" o algo de eso

{-data Exp = 
  Add Exp Exp -- Suma de expresiones
  | Var String -- Definición de variables
  | Const Nat -- Constantes numéricas
  | Local (List (String, Nat)) Exp -- Definición de ambientes locales, con definiciones de variables con solo constantes -}

-- Predicado que indica que una lista de labels siempre tiene el mismo tipo
data AllHaveType : LabelList lty -> Type -> Type where
  AllHaveTypeNil : AllHaveType [] ty
  AllHaveTypeCons : AllHaveType ts ty -> AllHaveType ((l, ty) :: ts) ty 
  
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
data Ambiente : LabelList String -> Type where
  IsEnv : AllHaveType ts Nat -> Record {lty=String} ts -> Ambiente ts

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
 
    
