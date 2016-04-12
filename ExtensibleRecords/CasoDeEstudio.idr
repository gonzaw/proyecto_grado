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
-}

-- Expresiones del lenguaje
data Exp = 
  Add Exp Exp -- Suma de expresiones
  | Var String -- Definición de variables
  | Const Nat -- Constantes numéricas
  | Local (List (String, Nat)) Exp -- Definición de ambientes locales, con definiciones de variables con solo constantes

-- Predicado que indica que una lista de labels siempre tiene el mismo tipo
data AllHaveType : LabelList lty -> Type -> Type where
  AllHaveTypeNil : AllHaveType [] ty
  AllHaveTypeCons : AllHaveType ts ty -> HasField l ts ty -> AllHaveType ((l, ty) :: ts) ty 

-- Ambiente local de valores de expresiones. Se trata de un record extensibles de valores de variables, cuyos valores solo pueden
-- ser Nat
data Ambiente : LabelList String -> Type where
  IsEnv : AllHaveType ts Nat -> Record {lty=String} ts -> Ambiente ts

-- TODO: Crear un "CanInterpExp" que tenga lo necesario para cada caso
data Exp

-- TODO: Ver como ir agregando con "consRec" y que compile
addLocalDefinitions : Ambiente tsIn -> List (String, Nat) -> (tsOut : LabelList String ** Ambiente tsOut)
addLocalDefinitions envIn ls = ?addLocalDefinitions_rhs  
  
-- TODO: Ver como interpretar una variable como string
interpVariable : Ambiente ts -> String -> Nat
interpVariable env var = ?interpVariable_rhs
  
-- Intérprete
interp : Ambiente ts -> Exp -> Nat
interp env (Add e1 e2) = (interp env e1) + (interp env e2)
-- Aca necesitaria una prueba de que 'v' esta en el ambiente, para hacer lookup 
interp env (Var var) = interpVariable env var
interp env (Const c) = c
interp {ts} env (Local def e) = 
  let (tsOut ** subEnv) = addLocalDefinitions {tsIn=ts} env def
  in interp {ts=tsOut} subEnv e
 
    
