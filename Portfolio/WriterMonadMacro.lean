import Mathlib.Control.Monad.Writer
import Qq

open Lean Elab Term Meta PrettyPrinter Syntax Do
open Qq

open Std

deriving instance Lean.ToExpr for String.Pos.Raw
deriving instance Lean.ToExpr for Substring.Raw
deriving instance Lean.ToExpr for Lean.SourceInfo
deriving instance Lean.ToExpr for Lean.Syntax

inductive LetSepKind
| non_arrow | arrow
deriving ToExpr, Repr

inductive LetLHSKind
| non_pat | pat
deriving ToExpr, Repr

structure LetKind where
  sepKind : LetSepKind
  lhsKind : LetLHSKind
  deriving ToExpr, Repr

structure LetBinding where
  bindings : HashMap Name (Expr × Dynamic)
  kind : LetKind
  rhs_stx : Syntax

deriving instance TypeName for 
  Nat, String, Bool

inductive Prod'
| mk : Nat -> Nat -> Prod'

deriving instance TypeName for Prod'

abbrev MyWriter := WriterT (Array LetBinding)

def mkBindingValExpr (id_nm : Name) : DoElabM Q(Name × Expr × Dynamic) := do
  let lctx <- getLCtx
  let decl := lctx.getFromUserName! id_nm
  let nm_expr : Q(Name) := q($id_nm)
  let typ_expr : Q(Expr) := toExpr decl.type
  let dynval_expr : Q(Dynamic) <- mkAppM ``Dynamic.mk #[decl.toExpr]
  pure q(($nm_expr, $typ_expr, $dynval_expr))

def mkBindingsFieldExpr_aux : Array Q(Name × Expr × Dynamic) -> Q(HashMap Name (Expr × Dynamic)) -> Q(HashMap Name (Expr × Dynamic))
| ar, hme => if h : ar.size == 0 then hme
  else
    let e := ar.back (by grind)
    mkBindingsFieldExpr_aux ar.pop q(($hme).insert ($e).1 ($e).2)
termination_by ar _ => ar.size
decreasing_by grind

def mkBindingsFieldExpr (binding_val_exprs : Array Q(Name × Expr × Dynamic)) : Q(HashMap Name (Expr × Dynamic))  :=
  mkBindingsFieldExpr_aux binding_val_exprs q(HashMap.ofArray #[])

def mkTellTerm (ids : Array Name) (kind : LetKind) (rhs_stx : Syntax) : DoElabM Expr := do
  let vals_array_e := mkBindingsFieldExpr (<- ids.mapM mkBindingValExpr)
  let lb_e <- mkAppM ``LetBinding.mk #[vals_array_e, toExpr kind, toExpr rhs_stx]
  let tell_arg <- mkAppM ``Array.mkArray1 #[lb_e]
  let ctx <- read
  let mtype := ctx.monadInfo.m
  let synth_type <- mkAppM ``MonadWriter #[q(Array LetBinding), mtype]
  let e <- mkAppOptM ``MonadWriter.tell #[
    q(Array LetBinding),
    mtype,
    <- synthInstance synth_type,
    tell_arg
  ]
  .pure e

open Lean Parser Term

def let'_stx := leading_parser
  "let' " >> letDecl

def let'_arrow_stx := leading_parser withPosition <|
  "let' " >> (doIdDecl <|> doPatDecl)

def let'_else_stx  := leading_parser withPosition <|
  "let' " >> termParser >> " := " >> termParser >>
  (checkColGe >> " | " >> doSeqIndent) >> optional (checkColGe >> doSeqIndent)

syntax (name := let'_stx_pdescr) let'_stx : doElem
syntax (name := let'_arrow_stx_pdescr) let'_arrow_stx : doElem
syntax (name := let'_else_stx_pdescr) let'_else_stx : doElem


def elabDoLet' (let_stx : Syntax) (nm_ar : Array Name) (kind : LetKind) (body : Syntax) (do_cont : DoElemCont) : DoElabM Expr := do
  Do.elabDoLetOrReassign (.let .none) (.mk let_stx) {
    resultName := <- mkFreshUserName `__x
    resultType := q(Unit)
    k := do
      let e <- mkTellTerm nm_ar kind body
      do_cont.mkBindUnlessPure e
  }

def elabDoLet'Arrow (id : Ident) (ty : Option Term) (nm_ar : Array Name) (kind : LetKind) (body : Syntax) (do_cont : DoElemCont) : DoElabM Expr := do
  elabDoIdDecl id ty (.mk body) do
    let e <- mkTellTerm nm_ar kind body
    do_cont.mkBindUnlessPure e

@[doElem_elab let'_stx_pdescr]
def let'_elab : DoElab := fun stx do_cont => do
  match stx with
  | `(doElem|let' $id:ident $[: $ty]? := $body) => do
    let as_let_stx <- `(letDecl|$id $[: $ty]? := $body)
    elabDoLet' as_let_stx #[(getId id)] ⟨.non_arrow, .non_pat⟩ body do_cont
  | `(doElem|let' $x:term $[: $ty]? := $body) => do
    let as_let_stx <- `(letDecl| $x:term $[: $ty]? := $body)
    let vars <- Elab.Do.getLetDeclVars as_let_stx
    elabDoLet' as_let_stx (vars.map getId) ⟨.non_arrow, .pat⟩ body do_cont
  | _ => throwUnsupportedSyntax

@[doElem_elab let'_arrow_stx_pdescr]
def let'_arrow_elab : DoElab := fun stx do_cont => do
  match stx with
  | `(doElem|let' $id:ident $[: $ty]? <- $body) =>
    elabDoIdDecl id ty (.mk body) do
      let e <- mkTellTerm #[getId id] ⟨.arrow, .non_pat⟩ body
      do_cont.mkBindUnlessPure e
  | `(doElem|let' $pat:term <- $body $[| $otherwise? $(rest?)?]?) =>
    let rest? := rest?.join
    let x := mkIdentFrom pat (<- mkFreshUserName `__id_from_pat)
    elabDoIdDecl x .none (.mk body) do
      match otherwise? with
      | .some otherwise => 
        elabDoElem (<- `(doElem|let' $pat:term := $x | $otherwise $(rest?)?)) do_cont
      | _ => 
        elabDoElem (<- `(doElem|let' $pat:term := $x)) do_cont
  | _ => throwUnsupportedSyntax

def do'_stx  := leading_parser:argPrec
  ppAllowUngrouped >> "do' " >> doSeq

syntax (name := do'_stx_pdescr) do'_stx : term

@[macro do'_stx_pdescr]
def let_to_let' : Macro
| `(term|do' $x) => do
  let replacer1 := replaceM (m := MacroM) fun
    | .node info `Lean.Parser.Term.doLet args => .pure <| .some <| 
      .node info `let'_stx_pdescr #[.node .none `let'_stx <| args.eraseIdx! 1]
    | .node info `Lean.Parser.Term.doLetArrow args => .pure <| .some <|
      .node info `let'_arrow_stx_pdescr #[.node .none `let'_arrow_stx <| args.eraseIdx! 1]
    | _ => .pure .none
  let replacer2 := replaceM (m := MacroM) fun
    | .atom inf "let" => .pure <| .some <| .atom inf "let'"
    | _ => .pure .none
  let new_stx <- replacer2 <| <- replacer1 x
  let new_do <- `(do $(.mk new_stx))
  .pure new_do
| _ => Macro.throwUnsupported

def LetBinding.pp_rhs_stx (lb : LetBinding) : TermElabM String := do
  let rhs_format <- formatTerm lb.rhs_stx
  .pure rhs_format.pretty'

def LetBinding.pp_typeNames (lb : LetBinding) : TermElabM String := do
  .pure (repr lb.bindings.keys).pretty'


def LetBinding.pp (lb : LetBinding) : TermElabM String := do
  let kind_str := (repr lb.kind).pretty'
  .pure (kind_str ++ "\n" ++ (<- lb.pp_rhs_stx) ++ "\n" ++ (<- lb.pp_typeNames))

-- testing

def simplemonval : IO Nat := .pure 7

set_option backward.do.legacy false
def myLoggedTest' : MyWriter TermElabM Unit := do'
  let x : Nat := 7
  let z : Prod' := ⟨111, 7⟩ 
  let .mk a b : Prod' := z
  let xx <- simplemonval
  IO.println a

/--
info: 111
#[{ sepKind := LetSepKind.non_arrow, lhsKind := LetLHSKind.non_pat }
7
[`x], { sepKind := LetSepKind.non_arrow, lhsKind := LetLHSKind.non_pat }
⟨111, 7⟩
[`z], { sepKind := LetSepKind.non_arrow, lhsKind := LetLHSKind.pat }
z
[`a, `b], { sepKind := LetSepKind.arrow, lhsKind := LetLHSKind.non_pat }
simplemonval
[`xx]]
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let r <- myLoggedTest'
  let s <- r.2.mapM LetBinding.pp
  dbg_trace s
