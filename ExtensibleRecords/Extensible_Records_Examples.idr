{-
  Aqui se muestran ejemplos de funciones de Extensible_Records
-}

module Extensible_Records_Examples

import Extensible_Records
import Data.List

%default total

-- Funciones que permiten forzar la unificación con tipo o su negación, según si se quiere forzar que una proposición se cumpla o no
getYes : (d : Dec p) -> case d of { No _ => (); Yes _ => p}
getYes (No _ ) = ()
getYes (Yes prf) = prf

getNo : (d : Dec p) -> case d of { No _ => Not p; Yes _ => ()}
getNo (No cnt) = cnt
getNo (Yes _ ) = ()

-- *** hListToRec ***
recEx1 : Record [("Nombre", String), ("Edad", Nat)]
recEx1 = hListToRec {prf=(getYes $ isLabelSet [("Nombre", String), ("Edad", Nat)])} ["Juan",10]

-- *** consRec ***

recEx2 : Record [("Apellido", String), ("Nombre", String), ("Edad", Nat)]
recEx2 = consRec "Apellido" "Sanchez" recEx1 {notElem=(getNo $ isElemLabel "Apellido" [("Nombre", String), ("Edad", Nat)])}

-- *** recToHList ***
hListEx1 : HList [("Nombre", String), ("Edad", Nat)]
hListEx1 = recToHList recEx1

-- *** recLblIsSet ***
labelSetEx1 : IsLabelSet [("Nombre", String), ("Edad", Nat)]
labelSetEx1 = recLblIsSet recEx1

-- *** consRecAuto ***
recEx3 : Record [("Apellido", String), ("Nombre", String), ("Edad", Nat)]
recEx3 = consRecAuto "Apellido" "Sanchez" recEx1

-- *** hListToRecAuto ***
recEx4 : Record [("Apellido", String), ("Nombre", String), ("Edad", Nat)]
recEx4 = hListToRecAuto [("Apellido", String), ("Nombre", String), ("Edad", Nat)] ["Sanchez", "Juan", 10]

-- *** hProjectByLabelsWithPred ***
recEx5_1 : ?recEx5_1_ty
recEx5_1 = fst . getProof $ hProjectByLabelsWithPred ["Apellido", "Edad"] recEx4 (getYes $ isSet ["Apellido", "Edad"])

-- *** hProjectByLabelsWithPredAuto ***
recEx5_2 : ?recEx2_2_ty
recEx5_2 = fst . getProof $ hProjectByLabelsWithPredAuto ["Apellido", "Edad"] recEx4

-- *** hProjectByLabel ***
recEx5_3 : ?recEx5_3_ty
--recEx5_3 : Record [("Apellido", String), ("Edad", Nat)]
recEx5_3 = hProjectByLabels ["Apellido", "Edad"] recEx4 (getYes $ isSet ["Apellido", "Edad"])

-- *** hProjectByLabelsAuto ***
recEx5_4 : ?recEx5_4_ty
--recEx5_4 : Record [("Apellido", String), ("Edad", Nat)]
recEx5_4 = hProjectByLabelsAuto ["Apellido", "Edad"] recEx4

-- *** hDeleteAtLabel ***
recEx6 : ?recEx6_ty
recEx6 = fst . getProof $ hDeleteAtLabel "Nombre" recEx4

-- *** hAppend ***
recEx7 : Record [("Calle", String)]
recEx7 = consRecAuto "Calle" "Bvar Artigas" emptyRec

recEx8 : Record [("Apto", Nat)]
recEx8 = consRecAuto "Apto" 2013 emptyRec

recEx9 : Record [("Calle", String), ("Apto", Nat)]
recEx9 = hAppend recEx7 recEx8 (getYes $ isLabelSet [("Calle", String), ("Apto", Nat)])

-- *** hAppendAuto ***
recEx10 : Record [("Calle", String), ("Apto", Nat)]
recEx10 = hAppendAuto recEx7 recEx8

-- *** hDeleteLabels ***
recEx11_1 : ?recEx11_1_ty
recEx11_1 = fst . getProof $ hDeleteLabels ["Apellido", "Edad"] recEx4

-- *** hLeftUnion ***
recEx12 : ?recEx12_ty
recEx12 = fst . getProof $ hLeftUnion recEx10 (hListToRecAuto [("Calle", String), ("Nombre", String)] ["Av Brasil", "Juan"])

-- *** hLookupByLabel ***
val1 : Nat
val1 = hLookupByLabel "Edad" recEx1 (HasFieldThere HasFieldHere)

val2 : String
val2 = hLookupByLabelAuto "Nombre" recEx1

-- *** hUpdateAtLabel ***
recEx13 : Record [("Nombre", String), ("Edad", Nat)]
recEx13 = hUpdateAtLabel "Edad" 100 recEx1 (HasFieldThere HasFieldHere)

recEx14 : Record [("Nombre", String), ("Edad", Nat)]
recEx14 = hUpdateAtLabelAuto "Nombre" "Pedro" recEx1
