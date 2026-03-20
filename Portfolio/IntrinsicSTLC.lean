import Lean.Elab.Tactic
import Lean.Expr

inductive Typ
| fn : Typ -> Typ -> Typ
| nat

inductive Ctx
| nil
| conj : Ctx -> Typ -> Ctx

inductive IsIn : Ctx -> Typ -> Type
| ofConj : {Γ : Ctx} -> {ty : Typ} -> IsIn (.conj Γ ty) ty
| ofIH : IsIn Γ ty -> IsIn (.conj Γ ty') ty

inductive HasTyp : Ctx -> Typ -> Type
| var : IsIn Γ A -> HasTyp Γ A
| lam : HasTyp (.conj Γ A) B -> HasTyp Γ (.fn A B)
| app : HasTyp Γ (.fn A B) -> HasTyp Γ A -> HasTyp Γ B
| zero : HasTyp Γ .nat
| succ : HasTyp Γ .nat -> HasTyp Γ .nat
| natCaseOn : HasTyp Γ .nat 
  -> HasTyp Γ A 
  -> HasTyp (.conj Γ .nat) A 
  -> HasTyp Γ A
| fix : HasTyp (.conj Γ A) A -> HasTyp Γ A

@[reducible]
def size : Ctx -> Nat
| .nil => .zero
| .conj Γ _ => .succ (size Γ)

/-
lookup : {Γ : Context} → {n : ℕ} → (p : n < size Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p
-/

def lookup : (Γ : Ctx) -> (n : Nat) -> n < size Γ -> Typ
| .conj _ A, .zero, p => A
| .conj Γ _, .succ nn, p => lookup Γ nn (by simp_all)

def count : (Γ : Ctx) -> (n : Nat) -> (p : n < size Γ) -> IsIn Γ (lookup Γ n p)
| .conj Γ A, .zero, _ => @IsIn.ofConj Γ A
| .conj .., .succ _, _ => .ofIH (count _ _ _)

def ext {Γ Δ} (ρ : {A : Typ} -> IsIn Γ A -> IsIn Δ A) 
  : {A B : Typ} -> IsIn (.conj Γ B) A -> IsIn (.conj Δ B) A :=
  fun {A} {_} isin => match isin with
  | .ofConj => .ofConj
  | .ofIH isin' => .ofIH (ρ isin')

def rename {Γ Δ} (ρ : {A : Typ} -> IsIn Γ A -> IsIn Δ A)
  : {A : Typ} -> HasTyp Γ A -> HasTyp Δ A := fun hastyp =>
    match hastyp with
    | .var x => .var (ρ x)
    | .lam N => .lam (rename (ext ρ) N)
    | .app L M => .app (rename ρ L) (rename ρ M)
    | .zero => .zero
    | .succ M => .succ (rename ρ M)
    | .natCaseOn L M N => .natCaseOn 
      (rename ρ L) 
      (rename ρ M) 
      (rename (ext ρ) N)
    | .fix N => .fix (rename (ext ρ) N)

def exts {Γ Δ} (σ : {A : _} -> IsIn Γ A -> HasTyp Δ A) {A B} 
  : IsIn (.conj Γ B) A -> HasTyp (.conj Δ B) A :=
  fun isin => match isin with
  | .ofConj => .var .ofConj
  | .ofIH isin'  => rename .ofIH (σ isin')

def subst {Γ Δ} (σ : {A : _} -> IsIn Γ A -> HasTyp Δ A) {A}
  : HasTyp Γ A -> HasTyp Δ A := fun hastyp =>
    match hastyp with
    | .var x => σ x
    | .lam N => .lam (subst (exts σ) N)
    | .app L M => .app (subst σ L) (subst σ M)
    | .zero => .zero
    | .succ M => .succ (subst σ M)
    | .natCaseOn L M N => .natCaseOn
      (subst σ L)
      (subst σ M)
      (subst (exts σ) N)
    | .fix N => .fix (subst (exts σ) N)

def ssubst {Γ A B} (N : HasTyp (.conj Γ B) A) (M : HasTyp Γ B)
  : HasTyp Γ A := 
    let σ {A'} : IsIn (.conj Γ B) A' -> HasTyp Γ A'
    | .ofConj => M
    | .ofIH isin => .var isin
    subst σ N

inductive IsVal : HasTyp Γ A -> Type
| lamval {Γ A B} (N : HasTyp (.conj Γ A) B) : IsVal (.lam N)
| zval {Γ} : IsVal (HasTyp.zero (Γ := Γ))
| succval {Γ} (V : HasTyp Γ .nat) : IsVal V -> IsVal (.succ V)

inductive ReducesTo : HasTyp Γ A -> HasTyp Γ A -> Type
| appRcongr {L L' : HasTyp Γ (.fn A B)} {M : HasTyp Γ A} : ReducesTo L L' -> 
  ReducesTo (.app L M) (.app L' M)
| appLcongr {V : HasTyp Γ (.fn A B)} {M M' : HasTyp Γ A} : IsVal V -> ReducesTo M M' -> 
  ReducesTo (.app V M) (.app V M')
| lambeta {N : HasTyp (.conj Γ A) B} {W : HasTyp Γ A} : IsVal W -> 
  ReducesTo (.app (.lam N) W) (ssubst N W)
| succCongr {M M' : HasTyp Γ .nat} : ReducesTo M M' -> 
  ReducesTo (.succ M) (.succ M')
| natCaseOnCongr {L L' : HasTyp Γ .nat} {M : HasTyp Γ A} {N : HasTyp (.conj Γ .nat) A} : ReducesTo L L' -> 
  ReducesTo (.natCaseOn L M N) (.natCaseOn L' M N)
| betazero {M : HasTyp Γ A} {N : HasTyp (.conj Γ .nat) A} :
  ReducesTo (.natCaseOn .zero M N) M
| betasucc {V : HasTyp Γ .nat} {M : HasTyp Γ A} {N : HasTyp (.conj Γ .nat) A} : IsVal V -> 
  ReducesTo (.natCaseOn (.succ V) M N) (ssubst N V)
| betafix {N : HasTyp (.conj Γ A) A} :
  ReducesTo (.fix N) (ssubst N (.fix N))


def classify {A : Typ} : (M : HasTyp .nil A) -> IsVal M ⊕ ΣN, ReducesTo M N
| .lam N => .inl (.lamval _)
| .app L M => match classify L with
  | .inr ⟨L', red⟩ => .inr <| .mk (.app L' M) (.appRcongr red)
  | .inl (.lamval N) => match classify M with
    | .inl val => .inr <| .mk (ssubst N M) (.lambeta val)
    | .inr ⟨M', red⟩ => .inr <| .mk (.app (.lam N) M') (.appLcongr (.lamval N) red)
| .zero => .inl .zval
| .succ M => match classify M with
  | .inl v => .inl <| .succval _ v
  | .inr ⟨M', red⟩ => .inr <| .mk (.succ M') (.succCongr red)
| .natCaseOn L M N => match classify L with
  | .inl .zval => .inr <| .mk M .betazero
  | .inl (.succval L' v) => .inr <| .mk (ssubst N L') (.betasucc v)
  | .inr ⟨L', red⟩ => .inr <| .mk (.natCaseOn L' M N) (.natCaseOnCongr red)
| .fix N => .inr <| .mk (ssubst N (.fix N)) .betafix

inductive ReductionSequence : HasTyp Γ A -> HasTyp Γ A -> Type
| start : (M : HasTyp Γ A) -> ReductionSequence M M
| conj : (L : HasTyp Γ A) -> ReducesTo L M -> ReductionSequence M N -> ReductionSequence L N

def length : ReductionSequence M N -> Nat
| .start _ => .zero
| .conj _ _ redseq => .succ (length redseq)

inductive BoundedReductionSequence (M : HasTyp .nil A) (bound : Nat)
| atbound : (redseq : ReductionSequence M N) -> length redseq = bound -> BoundedReductionSequence M bound
| terminates : 
    (redseq : ReductionSequence M N) -> length redseq < bound -> IsVal N -> BoundedReductionSequence M bound

def generateReductionSequence : (bound : Nat) -> (L : HasTyp .nil A) -> BoundedReductionSequence L bound
| .zero, L => .atbound (.start _) rfl
| .succ bound', L => match classify L with
  | .inl v => .terminates (.start _) (by simp [length]) v
  | .inr ⟨L', red⟩ => match generateReductionSequence bound' L' with
    | .atbound redseq x => .atbound (.conj L red redseq) (by simpa [length])
    | .terminates redseq p v => .terminates (.conj L red redseq) (by simpa [length]) v

/- syntax (name := count_macro) "#" term:arg : term -/
/- macro_rules -/
/- | `(# $arg) => do -/
/-   pure (<- `(HasTyp.var (count $arg (by simp)))) -/
/- def plus : HasTyp Γ (.fn .nat (.fn .nat .nat)) := -/
/-   .fix <| .lam <| .lam -/
/-   <| .natCaseOn (# 1) (# 0) (.succ <| .app (.app (# 3) (# 0)) (# 1)) -/
/- def two : HasTyp Γ .nat := .succ <| .succ .zero -/
/- #reduce generateReductionSequence 100 (.app (.app plus two) two) -/

