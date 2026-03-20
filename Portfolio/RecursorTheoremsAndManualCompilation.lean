

-- example inductive type to analyze
inductive Mytyp
| unit 
| w_nat (n : Nat)
| recur : Mytyp -> Mytyp -> Mytyp
| recur2 : List Mytyp -> Mytyp

-- theorems

theorem mytyp_rec_at_unit : @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons .unit = at_unit := rfl

theorem mytyp_rec_at_w_nat : @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons (.w_nat n) = at_w_nat n := rfl

theorem mytyp_rec_at_recur : @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons (.recur x y) = at_recur x y 
  (@Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons x) 
  (@Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons y) 
  := rfl

theorem mytyp_rec_at_recur' :
    let myrec := @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons
    myrec (.recur x y) = at_recur x y (myrec x) (myrec y)
    := rfl

theorem mytyp_rec_at_recur2 :
    @Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons (.recur2 l) 
    = 
    at_recur2 l (@Mytyp.rec_1 mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons l)
    := rfl

theorem mytyp_rec_1_at_nil : @Mytyp.rec_1 mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons .nil = at_nil := rfl

theorem mytyp_rec_1_at_cons : @Mytyp.rec_1 mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons (.cons x xs) = at_cons x xs
  (@Mytyp.rec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons x) 
  (@Mytyp.rec_1 mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons xs)
  := rfl



-- manual compilation of recursor
mutual
def Mytyp.crec_1
  (mota : Mytyp -> Type)
  (motb : List Mytyp -> Type)
  (at_unit : mota .unit)
  (at_w_nat : (n : Nat) -> mota (.w_nat n))
  (at_recur : (x y : Mytyp) -> mota x -> mota y -> mota (.recur x y))
  (at_recur2 : (l : List Mytyp) -> motb l -> mota (.recur2 l))
  (at_nil : motb .nil)
  (at_cons : (head : Mytyp) -> (tail : List Mytyp) -> mota head -> motb tail -> motb (.cons head tail))
  (x : List Mytyp)
  : motb x
  := match x with
  | .nil => at_nil
  | .cons x xs => at_cons x xs 
    (Mytyp.crec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons x) 
    (Mytyp.crec_1 mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons xs)

def Mytyp.crec
  (mota : Mytyp -> Type)
  (motb : List Mytyp -> Type)
  (at_unit : mota .unit)
  (at_w_nat : (n : Nat) -> mota (.w_nat n))
  (at_recur : (x y : Mytyp) -> mota x -> mota y -> mota (.recur x y))
  (at_recur2 : (l : List Mytyp) -> motb l -> mota (.recur2 l))
  (at_nil : motb .nil)
  (at_cons : (head : Mytyp) -> (tail : List Mytyp) -> mota head -> motb tail -> motb (.cons head tail))
  (x : Mytyp)
  : mota x 
  := match x with
  | .unit => at_unit
  | .w_nat nn => at_w_nat nn
  | .recur x y => at_recur x y 
    (Mytyp.crec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons x) 
    (Mytyp.crec mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons y) 
  | .recur2 l => at_recur2 l 
    (Mytyp.crec_1 mota motb at_unit at_w_nat at_recur at_recur2 at_nil at_cons l)

end


-- example
#eval @Mytyp.crec 
  (fun _ => Nat) 
  (fun _ => Nat) 
  .zero 
  (fun x => x.succ) 
  (fun _ _ _ x => x.succ) 
  (fun _ x => x.succ) 
  .zero
  (fun _ _ _ x => x.succ) 
  .unit
