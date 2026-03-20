structure Cont where
  ops : Type
  ar : ops -> Type

inductive W (ops : Type) (ar : ops -> Type)
| sup : (op : ops) -> (ar op -> W ops ar) -> W ops ar

def Cont.W (cont : Cont) : Type := _root_.W cont.ops cont.ar

structure ICont (I : Type) where
  ops : I -> Type
  ar : (i : I) -> ops i -> I -> Type

inductive IW (I : Type) 
  (ops : I -> Type)
  (ar : (i : I) -> ops i -> I -> Type) : I -> Type
| sup : {i : I} -> (op : ops i) -> ({i' : I} -> ar i op i' -> IW I ops ar i') -> IW I ops ar i

def ICont.IW (icont : ICont I) : I -> Type := 
  _root_.IW I icont.ops icont.ar

@[reducible]
def ICont.concat (ica icb : ICont I) : ICont I where
  ops := fun i => ica.ops i ⊕ icb.ops i
  ar := fun i x i' => match x with
  | .inl v => ica.ar i v i'
  | .inr v => icb.ar i v i'

structure Embedding (I IJ : Type) where
  to : I -> IJ
  from_ : IJ -> Option I
  subtype_p : ∀i, .some i = from_ (to i)

@[reducible]
def ICont.concat_embedding (p : Embedding I IJ) (ica : ICont I) (icb : ICont IJ) : ICont IJ where
  ops := fun ij => match p.from_ ij with
  | .none => icb.ops ij
  | .some x => ica.ops x ⊕ icb.ops ij
  ar := fun ij x ij' => match h : p.from_ ij with
  | .none => by rw [h] at x; simp at x; exact icb.ar ij x ij'
  | .some xx => match h' : p.from_ ij' with
   | .none => by rw [h] at x; simp at x; exact match x with
    | .inl x' => Empty
    | .inr x' => icb.ar _ x' ij'
   | .some xxx => by rw [h] at x; simp at x; exact match x with
    | .inl x' => ica.ar _ x' xxx
    | .inr x' => icb.ar _ x' ij'


