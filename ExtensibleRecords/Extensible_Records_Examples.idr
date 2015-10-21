{-
  Aqui se muestran ejemplos de funciones de Extensible_Records
-}

module Extensible_Records_Examples

import Extensible_Records
import Data.List

%default total

-- Auxiliares
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

-- *** hProjectByLabels ***
-- TODO: Cuando este implementada hRearrange usar este test de nuevo
--recEx5 : Record [("Edad", Nat), ("Apellido", String)]
--recEx5 = fst . getProof $ hProjectByLabels ["Edad", "Apellido"] recEx4

-- *** hDeleteAtLabel ***
-- TODO: No compila por problema de unificacion de "ls" y el tipo
--recEx6 : Record [("Apellido", String), ("Edad", Nat)]
--recEx6 = fst . getProof $ hDeleteAtLabel "Nombre" recEx4

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
-- TODO: No compila por problema de unificacion de "ls" y el tipo
--recEx11 : Record [("Nombre", String)]
--recEx11 = fst . getProof $ hDeleteLabels ["Apellido","Edad"] recEx4
-- TODO: Ver si es puede inferir este tipo de abajo
--recEx11 : ?recEx11Type
--recEx11 = fst . getProof $ hDeleteLabels ["Apellido","Edad"] recEx4
