%default total

-- Expresiones de tipo
data TyExp = TyNat | TyBool

Val : TyExp -> Type
Val TyNat = Nat
Val TyBool = Bool

-- Familia de expresiones
data Exp : TyExp -> Type where
  ValE : {t : TyExp} -> (v : Val t) -> Exp t
  PlusE : (e1 : Exp TyNat) -> (e2 : Exp TyNat) -> Exp TyNat
  IfE : {t : TyExp} -> (b : Exp TyBool) -> (e1 : Exp t) -> (e2 : Exp t) -> Exp t
 
-- Evaluador
eval : {t : TyExp} -> Exp t -> Val t
eval (ValE v) = v
eval (PlusE e1 e2) = (eval e1) + (eval e2)
eval (IfE b e1 e2) = if (eval b) then (eval e1) else (eval e2)

-- Stack
StackType : Type
StackType = List TyExp

data Stack : StackType -> Type where
  EmptyS : Stack []
  SCons : {t : TyExp} -> {sType : StackType} -> (v : Val t) -> (s : Stack sType) -> Stack (t :: sType)
  
top :  {t : TyExp} -> {sType : StackType} -> (s : Stack (t :: sType)) -> Val t
top (SCons v s) = v

-- Codigo intermedio
data Code : StackType -> StackType -> Type where
  SkipC : Code s s
  (++) : (c1 : Code s0 s1) -> (c2 : Code s1 s2) -> Code s0 s2
  PushC : {t : TyExp} -> (v : Val t) -> Code s (t :: s)
  AddC : Code (TyNat :: TyNat :: s) (TyNat :: s)
  IfC : (c1 : Code s0 s1) -> (c2 : Code s0 s1) -> Code (TyBool :: s0) s1

-- Ejecutador de codigo
exec : (code : Code s0 s1) -> (stack : Stack s0) -> Stack s1
exec SkipC s = s
exec (c1 ++ c2) s = exec c2 (exec c1 s)
exec (PushC v) s = SCons v s
exec AddC (SCons n (SCons m s)) = SCons (n + m) s
exec (IfC c1 c2) (SCons True s) = exec c1 s
exec (IfC c1 c2) (SCons False s) = exec c2 s

-- Compilador
compile : {t : TyExp} -> (e : Exp t) -> Code s (t :: s)
compile (ValE v) = PushC v
compile (PlusE e1 e2) = (compile e2) ++ (compile e1) ++ AddC
compile (IfE b e1 e2) = (compile b) ++ (IfC (compile e1) (compile e2))


-- Lemma de decision sobre booleanos para probar teorema de correctitud
boolLemmaDec : (b : Bool) -> ((b = True) -> Void) -> (b = False)
boolLemmaDec False f = Refl
boolLemmaDec True f = absurd (f Refl)

-- Teorema de correctitud
theorem_compile : {t : TyExp} -> (e : Exp t) -> (s : Stack sType) ->
             SCons (eval e) s = exec (compile e) s
theorem_compile (ValE v) s = Refl
theorem_compile (PlusE e1 e2) s = ?theorem_compile_rhs_plus
theorem_compile (IfE b e1 e2) s with (decEq (eval b) True)
  theorem_compile (IfE b e1 e2) s | Yes prf = ?theorem_compile_rhs_if_true
  theorem_compile (IfE b e1 e2) s | No prfNo = ?theorem_compile_rhs_if_false



---------- Proofs ----------
 Main.theorem_compile_rhs_plus = proof
  intros
  let pfE2 = theorem_compile e2 s
  rewrite pfE2
  let pfE1 = theorem_compile e1 (SCons {t=TyNat} (eval e2) s)
  rewrite pfE1
  compute
  trivial

Main.theorem_compile_rhs_if_false = proof
  intros
  let pfB = theorem_compile b s
  rewrite pfB
  let pfFalse = boolLemmaDec (eval b) prfNo
  rewrite (sym pfFalse)
  compute
  let pfE2 = theorem_compile e2 s
  exact pfE2


Main.theorem_compile_rhs_if_true = proof
  intros
  let pfB = theorem_compile b s
  rewrite pfB
  rewrite (sym prf)
  compute
  let pfE1 = theorem_compile e1 s
  exact pfE1

