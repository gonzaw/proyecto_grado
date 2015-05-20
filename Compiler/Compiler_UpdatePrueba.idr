%default total

-- Expresiones de tipo
data TyExp = TyNat | TyBool

Val : TyExp -> Type
Val TyNat = Nat
Val TyBool = Bool

-- Familia de expresiones
-- En el tipo se guarda el tipo de la expresion y el valor que se computa en el momento 
data Exp : (t : TyExp) -> Val t -> Type where
  ValE : {t : TyExp} -> (v : Val t) -> Exp t v  
  PlusE : (e1 : Exp TyNat v1) -> (e2 : Exp TyNat v2) -> Exp TyNat (v1 + v2)
  IfE : {t : TyExp} -> (b : Exp TyBool vBool) -> 
        (e1 : Exp t v1) -> (e2 : Exp t v2) -> Exp t (ifThenElse vBool v1 v2)
 
-- Evaluador
eval : {t : TyExp} -> Exp t v -> Val t
eval {v=v} exp = v

-- Stack
-- El stack contiene una lista de tipos con sus valores correspondientes
Stack : Type
Stack = List (t : TyExp ** Val t)
  
-- Codigo intermedio      
data Code : Stack -> Stack -> Type where
  SkipC : Code s s
  (++) : (c1 : Code s0 s1) -> (c2 : Code s1 s2) -> Code s0 s2
  PushC : {t : TyExp} -> (v : Val t) -> Code s ((t ** v) :: s)
  AddC : Code ((TyNat ** v1) :: (TyNat ** v2) :: s) ((TyNat ** (v1 + v2)) :: s)
  IfC : (c1 : Code s0 ((t ** v1) :: s)) -> (c2 : Code s0 ((t ** v2) :: s)) -> 
        Code ((TyBool ** vBool) :: s0) ((t ** ifThenElse vBool v1 v2) :: s)
        
-- Ejecutador de codigo
exec : (s0 : Stack) -> (code : Code s0 s1) -> Stack
exec stack code {s1=s1} = s1

-- Compilador
compile : {t : TyExp} -> (e : Exp t v) -> Code s ((t ** v) :: s)
compile (ValE v) = PushC v
compile (PlusE e1 e2) = (compile e2) ++ (compile e1) ++ AddC
compile (IfE b e1 e2) = (compile b) ++ (IfC (compile e1) (compile e2))

-- Teorema de correctitud
theorem_compile : {t : TyExp} -> (e : Exp t v) -> (s : Stack) ->
             (t ** (eval e)) :: s = exec s (compile e)
theorem_compile exp stack = Refl
