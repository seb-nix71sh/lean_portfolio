import Portfolio.WType

@[reducible]
def Ext (σ : Cont) : Type -> Type :=
  fun α => (op : σ.ops) × ((σ.ar op) -> α)

@[reducible]
def Ext.W {σ} (x : Ext σ σ.W) : σ.W := 
  .sup x.1 x.2 

@[reducible]
def Alg (σ : Cont) (α : Type) : Type := Ext σ α -> α

def cata (alg : Alg σ α) : σ.W -> α :=
  fun ⟨op, f⟩ => alg ⟨op, fun x => cata alg (f x)⟩

@[reducible]
def lAlg (σ : Cont) (γ η : Type) := Ext σ (γ × η) -> γ

@[reducible]
def rAlg (σ : Cont) (γ η : Type) := Ext σ (γ × η) -> η

def mutu (lalg : lAlg σ γ η) (ralg : rAlg σ γ η) : (σ.W -> γ) × (σ.W -> η) := 
  let alg x : γ × η := (lalg x, ralg x)
  ((cata alg · |>.fst), (cata alg · |>.snd))

def zygo (alga : lAlg σ γ η) (algb : Alg σ η) : σ.W -> γ := fun mu =>
  (mutu alga (algb ∘ (fun ext => ⟨ext.1, Prod.snd ∘ ext.2⟩)) |>.fst) mu

@[reducible]
def IExt (ζ : ICont I) (P : I -> Type) : I -> Type :=
  fun i => (op : ζ.ops i) × ({i' : I} -> ζ.ar i op i' -> P i')

@[reducible]
def IExt.W {ζ : ICont I} (x : (i : I) -> IExt ζ ζ.IW i) : (i : I) -> ζ.IW i := 
  fun i => IW.sup (x i).1 (x i).2

@[reducible]
def IExt.W' {ζ : ICont I} : {i : I} -> (x : IExt ζ ζ.IW i) -> ζ.IW i := 
  fun x => IW.sup x.1 x.2

@[reducible]
def IAlg (ζ : ICont I) (P : I -> Type) : Type :=
  {i : I} -> IExt ζ P i -> P i

def icata {P : I -> Type} (ialg : IAlg ζ P) : {i : I} -> ζ.IW i -> P i :=
  fun ⟨iop, if_⟩ => ialg ⟨iop, fun x => icata ialg (if_ x)⟩


