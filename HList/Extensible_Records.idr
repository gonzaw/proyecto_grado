{-
  En este archivo se van a intentar definir records extensibles.
  
  Basicamente, se definen los records como una lista heterogenea de labels. Un label tiene un titulo y un tipo. Un record, para un label,
  debe tener un valor de ese tipo. A su vez, se definen relaciones que indican cuando un label es identico a otro (cuando tienen el mismo
  titulo), y cuando un label esta repetido en un vector de labels. Se utiliza una metodologia similar a las pruebas de Data.Vect.Elem
-}
import Data.Vect

%default total

namespace Record

  infix 5 :=

  -- Un campo tiene un label (que debe tener igualdad decidible) y un tipo
  data Field : lbl -> Type -> Type where
    (:=) : DecEq lbl => (field_label : lbl) -> 
         (value : b) -> Field field_label b

  -- Relacion de inclusion. "InLabel l ls" indica que el label "l" ya existe en el vector de label types "ls". Esta repetido si ya existe
  -- otro labeltype con el mismo label
  data InLabel : lty -> Vect n (lty, Type) -> Type where
    InHere : InLabel lbl ((lbl,ty) :: ls)
    InThere : InLabel lbl1 ls -> InLabel lbl1 ((lbl2,ty) :: ls)

   -- Ninguna label puede estar en un vector vacio
  noEmptyInLabel : InLabel lbl [] -> Void
  noEmptyInLabel (InHere) impossible
  
  -- Un label que no esta en la cabeza ni cola de la lista no esta en la lista
  neitherInHereNorInThere : {lbl1, lbl2 : lty} -> {ls : Vect n (lty, Type)} -> Not (lbl1 = lbl2) -> Not (InLabel lbl1 ls) 
                             -> Not (InLabel lbl1 ((lbl2, ty) :: ls))
  neitherInHereNorInThere l1neql2 l1ninls InHere = l1neql2 Refl
  neitherInHereNorInThere l1neql2 l1ninls (InThere l1inls) = l1ninls l1inls

  -- Si un label no esta en la cola, entonces no esta en el head de la lista
  ifNotInThereThenNotInHere : {lbl1, lbl2 : lty} -> {ls : Vect n (lty, Type)} -> Not (InLabel lbl1 ((lbl2, ty) :: ls)) 
                            -> Not (InLabel lbl1 ls)
  ifNotInThereThenNotInHere l1nincons l1inls = l1nincons (InThere l1inls)
  
  -- Funcion de decision que indica si un label esta repetido en una lista de labels o no
  isInLabelList : DecEq lty => (lbl : lty) -> (ls : Vect n (lty, Type)) -> Dec (InLabel lbl ls)       
  isInLabelList lbl [] = No noEmptyInLabel
  isInLabelList lbl1 ((lbl2, ty) :: ls) with (decEq lbl1 lbl2)
    isInLabelList lbl1 ((lbl1, ty) :: ls) | Yes Refl = Yes InHere
    isInLabelList lbl1 ((lbl2, ty) :: ls) | No l1neql2 with (isInLabelList lbl1 ls)
      isInLabelList lbl1 ((lbl2, ty) :: ls) | No l1neql2 | Yes l1inls = Yes (InThere l1inls)
      isInLabelList lbl1 ((lbl2, ty) :: ls) | No l1neql2 | No l1ninls = No (neitherInHereNorInThere l1neql2 l1ninls)
  
 
  
  -- Records
  -- Un record contiene una lista de labels no repetidos (no se repiten si tienen titulos distintos). A cada label se le asocia un valor
  -- del tipo correspondiente. Se debe pasar una prueba que el label no esta en el resto del record (para no tener labels repetidos)
  using (lbl : lty, ls : Vect n (lty, Type))
    data Record : DecEq lty => Vect n (lty, Type) -> Type where
      NilRec : DecEq lty => Record {lty} []
      Rec : DecEq lty => Field lbl a -> Record ls -> (prf : Not (InLabel lbl ls)) -> Record ((lbl, a) :: ls)

    -- FieldType l ls ty indica que el label "l" de la lista "ls" tiene el tipo "ty"
    data FieldType : lty -> Vect n (lty, Type) -> Type -> Type where
      First : FieldType lbl ((lbl, ty) :: ls) ty
      Later : FieldType lbl ls ty -> FieldType lbl (a :: ls) ty
      
      
  -- Funcion que ayuda a obtener pruebas automaticas
  getNo : (res : Dec p) -> case res of { Yes _ => () ; No _ => Not p }
  getNo (Yes prf) = ()
  getNo (No contra) = contra


  -- *** Obtener un elemento ***

  -- Dado un label, obtiene el elemento de un record
  getField' : DecEq lty => (lbl : lty) -> Record ls -> FieldType lbl ls ty -> ty
  getField' lbl (Rec (_ := val) _ _) First = val
  getField' lbl (Rec _ rs _) (Later prfLater) = getField' lbl rs prfLater

  -- Misma funcion, donde se automatiza la prueba de que tiene el tipo
  getField : DecEq lty => (lbl : lty) -> Record ls -> 
               {default tactics { search } prf : FieldType lbl ls ty} -> ty
  getField lbl rs {prf} = getField' lbl rs prf

  -- *** Actualizar un elemento ***

  -- Toma una funcion t -> t y actualiza un elemento del record con esa funcion
  updateField' : DecEq lty => (lbl : lty) -> Record ls -> (ty -> ty) -> FieldType lbl ls ty -> Record ls
  updateField' lbl (Rec (lbl := val) rs prf) f First = Rec (lbl := f val) rs prf 
  updateField' lbl (Rec field rs prf) f (Later prfLater) = Rec field (updateField' lbl rs f prfLater) prf

  -- Misma funcion, donde se automatiza la prueba de que tiene el tipo
  updateField : DecEq lty => (lbl : lty) -> Record ls -> (ty -> ty) ->
               {default tactics { search } prf : FieldType lbl ls ty} -> Record ls
  updateField l rs f {prf} = updateField' l rs f prf


  -- *** Actualizar un elemento cambiando su tipo ***

  -- Actualiza el tipo de un label en una lista
  updLblType : DecEq lty => (ls : Vect n (lty,Type)) -> (lbl : lty) -> (tydes : Type) -> FieldType lbl ls tysrc -> Vect n (lty, Type)
  updLblType {tysrc=tysrc} ((lbl, tysrc) :: ls) lbl tydes First = (lbl, tydes) :: ls
  updLblType {tysrc=tysrc} ((lbl1, tyaux) :: ls) lbl tydes (Later prfLater) = (lbl1,tyaux) :: (updLblType ls lbl tydes prfLater)
  
  -- Transforma InLabels equivalentes
  transInLabel : InLabel lbl1 ((lbl2, ty1) :: ls) -> InLabel lbl1 ((lbl2, ty2) :: ls)
  transInLabel InHere = InHere
  transInLabel (InThere x) = InThere x
  
  -- Si tengo una prueba que el label "l" esta en la lista "ls", entonces modificar su tipo no cambia la prueba
  updPrfType : DecEq lty => {lbl1, lbl2 : lty} -> {ls : Vect n (lty,Type)} -> {prfLater : FieldType lbl1 ls tysrc}
              -> Not (InLabel lbl2 ls) -> 
             Not (InLabel lbl2 (updLblType ls lbl1 tydes prfLater))
  updPrfType {lbl1=lbl1} {ls= (lbl1, tysrc) :: ls2} {lbl2=lbl2} {tydes=tydes} l2ninls l2inupd {prfLater = First} = 
    let l2inupd_2 = the (InLabel lbl2 ((lbl1, tydes) :: ls2) ) l2inupd
        l2inupd_3 = transInLabel l2inupd_2 {lbl1=lbl2} {lbl2=lbl1} {ty1=tydes} {ty2=tysrc} {ls=ls2}
    in l2ninls l2inupd_3
  updPrfType {lbl1=lbl1} {ls= (lblaux, tyaux) :: ls2} {lbl2=lbl2} {tydes=tydes} l2ninls l2inupd {prfLater = (Later prfLaterOther)} with
             (decEq lbl2 lblaux)
    updPrfType {lbl1=lbl1} {ls= (lbl2, tyaux) :: ls2} {lbl2=lbl2} {tydes=tydes} l2ninls l2inupd | Yes Refl = l2ninls InHere
    updPrfType {lbl1=lbl1} {ls= (lblaux, tyaux) :: ls2} {lbl2=lbl2} {tydes=tydes} l2ninls l2inupd {prfLater = (Later prfLaterOther)} 
               | No contra = 
          let l2ninls_2 = ifNotInThereThenNotInHere l2ninls
              l2ninls_3 = updPrfType {lbl1=lbl1} {lbl2=lbl2} {tydes=tydes} {ls=ls2} {prfLater=prfLaterOther} l2ninls_2
          in neitherInHereNorInThere contra l2ninls_3 l2inupd

  -- Actualiza elementos, y puede cambiar su tipo
  updateFieldType' : DecEq lty => (lbl : lty) -> Record ls -> (tysrc -> tydes) -> (prf : FieldType lbl ls tysrc) 
    -> Record (updLblType ls lbl tydes prf)
  updateFieldType' lbl (Rec (lbl := val) rs prf) f First = Rec (lbl := f val) rs prf
  updateFieldType' {tydes=tydes} lbl (Rec field rs prf {lbl=lbl2} ) f (Later prfLater) =
                   Rec field (updateFieldType' lbl rs f prfLater) (updPrfType prf {lbl2=lbl2} {lbl1=lbl} {tydes=tydes} {prfLater=prfLater})


   -- Misma funcion, donde se automatiza la prueba de que tiene el tipo
  updateFieldType : DecEq lty => (lbl : lty) -> Record ls -> (tysrc -> tydes) ->
               {default tactics { search } prf : FieldType lbl ls tysrc} -> Record (updLblType ls lbl tydes prf)
  updateFieldType l rs f {prf} = updateFieldType' l rs f prf

  namespace Ej1
    --Ejemplos simples de records extensibles
    Age : (String,Type)
    Age = ("Age", Nat)

    AgeWrong : (String,Type)
    AgeWrong = ("Age", String)

    Name : (String,Type)
    Name = ("Name", String)
    
    -- Este ejemplo compila, y devuelve un record con un unico valor
    example1 : Record [Age]
    example1 = Rec ("Age" := 2) NilRec prf
      where
        prf = getNo (isInLabelList "Age" [])
    
    -- Este ejemplo tambien compila. Esto muestra como agregar campos a records
    example2 : Record [Name, Age]
    example2 = Rec ("Name" := "John") example1 prf
      where
        prf = getNo (isInLabelList "Name" [Age])

    -- Este caso no compila. Se esta intentando agregar un label "AgeWrong" con el mismo titulo que "Age" (aunque tienen tipos distintos, 
    -- uno Nat y otro String). La busqueda automatica de la prueba falla con esto    
    {-example3 : Record [AgeWrong, Age]
    example3 = Rec ("AgeWrong" := "Wrong") example1 prf
      where
        prf = getNo (isInLabel "AgeWrong" [Age])-}

    -- Ejemplo de obtener datos de un record
    ex2Age : Nat
    ex2Age = getField "Age" example2
  
    ex2Name : String
    ex2Name = getField "Name" example2
  
    -- Es typesafe. Por ejemplo, este caso de abajo tira error de compilacion
    {-ex1Name : String
    ex1Name = getField "Name" example1-}

    -- Ejemplo de actualizar datos de un record  
    example2_updated : Record [Name, Age]
    example2_updated = updateField "Age" example2 (+1)

    -- Ejemplo de actualizar datos mas el tipo de un record
    AgeString : (String, Type)
    AgeString = ("Age", String)
    
    example2_updated_type : Record [Name, AgeString]
    example2_updated_type = updateFieldType "Age" example2 fun
      where
        fun : Nat -> String
        fun n = "The age is: " ++ (show n)
