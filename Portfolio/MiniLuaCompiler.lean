import Std
import Qq
import Init.Control.Reader

open Qq
open Lean Elab Term Command
open Expr

syntax (name := recur_stx) "recur" : term
@[term_elab recur_stx]
def recur_stx_elab : TermElab := fun _ et => do
  let .some decl_nm <- getDeclName? | throwError "could not get decl name"
  let e <- elabTerm (mkIdent decl_nm) et
  return e

inductive PreLuaRepr
| nil
| bool (b : Bool)
| str (s : String)
| num (x : Int)
deriving DecidableEq, BEq, Repr

def PreLuaRepr.compile : PreLuaRepr -> String
| .nil => "nil"
| .bool b => toString b
| .str s => "\"" ++ s ++ "\""
| .num x => toString x

inductive Arity
| z
| lam : Arity -> Arity -> Arity
deriving DecidableEq, BEq, Repr

def Arity.asUsualArity : Arity -> Nat
| .z => 0
| .lam _ x => 1 + x.asUsualArity

inductive LuaRepr : Arity -> Type
| fvar (id : String) 
  : LuaRepr ar
| val (v : PreLuaRepr) 
  : LuaRepr .z
| tval : List ((Σi_ar, LuaRepr i_ar) × (Σv_ar, LuaRepr v_ar))
  -> LuaRepr .z
| lam (binder : String) (binder_ar : Arity) {rhs_ar : Arity} (rhs : LuaRepr rhs_ar) 
  : LuaRepr (.lam binder_ar rhs_ar)
| app {binder_ar dom_ar : Arity}  (fn : LuaRepr (.lam binder_ar dom_ar)) 
  : LuaRepr binder_ar -> LuaRepr dom_ar
| let (binding_nm : String) {binding_ar} (binding_repr : LuaRepr binding_ar) {body_ar} (cont : LuaRepr body_ar)
  : LuaRepr body_ar
| cons_do (effectful : LuaRepr .z) (cont : LuaRepr ar')
  : LuaRepr ar'
| raw (s : String)  
  : LuaRepr ar
deriving Repr

namespace LuaRepr

def beq : {ar ar' : _} -> LuaRepr ar -> LuaRepr ar' -> Bool
| _, _, .val x, .val y => x == y
| _, _, .tval .nil, .tval .nil => .true
| _, _, 
  .tval (.cons ⟨⟨i_xl, xl⟩, ⟨i_xr, xr⟩⟩ xs), 
  .tval (.cons ⟨⟨i_yl, yl⟩, ⟨i_yr, yr⟩⟩ ys) => 
    i_xl == i_yl && i_xr == i_yr && xl.beq yl && xr.beq yr 
    && LuaRepr.beq (.tval xs) (.tval ys)
| _, _, .lam _ binder_ar rhs, .lam _ binder_ar' rhs' =>
  binder_ar == binder_ar' && LuaRepr.beq rhs rhs'
| _, _, .app f x, .app f' x' =>
  LuaRepr.beq f f' && LuaRepr.beq x x'
| _, _, .raw (ar := ar) s, .raw (ar := ar') s' => 
  ar == ar' && s == s'
| _, _, _, _ => .false

instance LuaRepr_beq {ar} : BEq (LuaRepr ar) where
  beq := LuaRepr.beq

def LuaCompile := {ar : Arity} -> LuaRepr ar -> ReaderM ({ar' : Arity} -> LuaRepr ar' -> String) String

def root : LuaCompile := fun r => do
  let k <- read
  return k r


def compile_table_index : LuaCompile
| _, .val (.str s) => return s
| _, x => root x

partial def compile_table (start? : Bool) : LuaCompile
| _, .tval .nil => if start? then return "{}" else return " }"
| _, .tval l@(.cons ⟨⟨_i_ar, i⟩, ⟨_v_ar, v⟩⟩ xs) => if start?
  then return "{ " ++ (<- recur .false (.tval l))
  else return (<- compile_table_index i) ++ " = " ++ (<- root v) ++  ", " ++ (<- recur .false (.tval xs))
| _, x => root x

partial def compile_lam (start? : Bool) : LuaCompile
|_,  .lam binder ar rhs => match start? with
  | .true => return "function(" ++ (<- recur .false (.lam binder ar rhs))
  | .false => return binder ++ ")" ++ " return " ++ (<- root rhs) ++ " end"
| _, x => root x

instance [HAppend α α α] : HAppend α (Id α) α where
  hAppend := fun x y => x ++ y.run

partial def compile {ar} : LuaRepr ar -> String
| .fvar id => id
| .val v => v.compile
| .tval l => compile_table .true (.tval l) |>.run recur
| f@(.lam _ _ _) => compile_lam .true f |>.run recur
| .app fn arg =>
  let compiled_fn := match fn with 
    | .raw s => s
    | .fvar id => id
    | _ => "(" ++ (LuaRepr.compile_lam .true fn |>.run recur) ++ ")"
  compiled_fn ++ "(" ++ recur arg ++ ")"
| .let bnm bv cont => "local " ++ bnm ++ " = " ++ recur bv ++ "; " ++ recur cont
| .cons_do do_luarepr cont_luarepr =>
  recur do_luarepr ++ "; " ++ recur cont_luarepr
| .raw s => s

end LuaRepr

def lua_add_repr : LuaRepr (.lam .z (.lam .z .z)) := .raw "function (x,y) return x + y end"
def lua_add_repr' : LuaRepr (.lam .z (.lam .z .z)) := 
  .lam "x" _ <| .lam "y" _ <| .raw "x + y"
def lua_zero : LuaRepr .z := .raw "0"
def lua_succ : LuaRepr (.lam .z .z) := .raw "succ"
def lua_one : LuaRepr .z := .app lua_succ lua_zero
def lua_two : LuaRepr .z := .app lua_succ lua_one
def lua_one_plus_two : LuaRepr .z := .app (.app lua_add_repr' lua_two) lua_one

/-- info: "((function(x) return function(y) return x + y end end)(succ(succ(0))))(succ(0))" -/
#guard_msgs in
#eval lua_one_plus_two.compile

def lua_succ' : LuaRepr (.lam .z .z) := .fvar "succ"
def lua_one' : LuaRepr .z := .app lua_succ' lua_zero
def lua_two' : LuaRepr .z := .app lua_succ' lua_one'
def print' : LuaRepr (.lam .z .z) := .raw "print"
def lua_one_plus_two' : LuaRepr .z := .let "succ" (binding_ar := .lam .z .z) (.raw "function (x) return x + 1 end") <| .app print' <| .app (.app lua_add_repr' lua_two') lua_one'


/--
info: "local succ = function (x) return x + 1 end; print(((function(x) return function(y) return x + y end end)(succ(succ(0))))(succ(0)))"
-/
#guard_msgs in
#eval lua_one_plus_two'.compile


