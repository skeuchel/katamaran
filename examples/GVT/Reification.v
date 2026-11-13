(* Reification of the erased symbolic propositions (Erasure.ESymProp) produced
   by the symbolic executor into Ltac2 data, and reflection of that data back
   into a Gallina Prop with named, freshened variables. The main entry point is
   the Ltac1 tactic [reify_vc], which replaces a goal
   [VerificationConditionWithErasure p] with a readable Prop that is
   convertible to it.

   This is specific to the RiscvPmp case study: symbolic variable names
   (LVar) are assumed to be string literals. Copy of
   case_study/RiscvPmp/Reification.v for the GVT signature. *)

From iris.proofmode Require Import string_ident.

From Katamaran Require Import
     Context
     Environment
     Syntax.BinOps
     Syntax.TypeDecl
     Syntax.UnOps
     RiscvPmp.Base
     RiscvPmp.GVT.Sig
     RiscvPmp.GVT.Logic.

Import RiscvPmpExecutor.

From Ltac2 Require Import
     Ltac2
     Printf.

(* Importing Ltac2 makes it the default proof mode again; force Ltac1. *)
Set Default Proof Mode "Classic".

Import Erasure.

(* ------------------------------------------------------------------------ *)
(* Generic helpers                                                           *)
(* ------------------------------------------------------------------------ *)

Ltac2 rec nat_to_int (n : constr) : int :=
  lazy_match! n with
  | O => 0
  | S ?m => Int.add 1 (nat_to_int m)
  | _ => Control.throw (Tactic_failure (Some (fprintf "reify: expected a nat literal but got '%t'" n)))
  end.

(* [string_init n f] is the string of length [n] whose [i]-th character is
   [f i]. Ltac2 strings are mutable but have a fixed length, so we allocate the
   whole string up front and fill it in. *)
Ltac2 string_init (n : int) (f : int -> char) : string :=
  let r := String.make n (Char.of_int 0) in
  let rec fill (i : int) :=
    if Int.lt i n then (String.set r i (f i); fill (Int.add i 1)) else () in
  fill 0;
  r.

Ltac2 rec list_remove (l : 'a list) (n : int) : 'a list :=
  match l with
  | [] => []
  | x :: xs => if Int.equal n 0 then xs else x :: list_remove xs (Int.sub n 1)
  end.

(* ------------------------------------------------------------------------ *)
(* Named variables                                                           *)
(* ------------------------------------------------------------------------ *)
(* Turn the names of symbolic variables into valid, fresh identifiers (using
   Iris's StringToIdent) and introduce variables carrying those names. *)

(* Turn the name of a symbolic variable into a valid identifier using Iris's
   StringToIdent. Names like "L.1" are not identifiers, so
   we sanitise them first (and let Fresh.fresh pick the final name). *)
Ltac2 sanitise_char (c : char) : char :=
  let i := Char.to_int c in
  if Bool.or (Bool.and (Int.le 48 i) (Int.le i 57))      (* 0-9 *)
       (Bool.or (Bool.and (Int.le 65 i) (Int.le i 90))   (* A-Z *)
          (Bool.or (Bool.and (Int.le 97 i) (Int.le i 122)) (* a-z *)
             (Bool.or (Int.equal i 95) (Int.equal i 39)))) (* _ ' *)
  then c else Char.of_int 95. (*i.e. `_` *)

Ltac2 sanitise_string (s : string) : string :=
  (* Drop the ".<n>" suffix of renamed variables ("L.1" ↦ "L"); Fresh.fresh
     makes the names unique again. *)
  let len := String.length s in
  let rec find_dot (i : int) :=
    if Int.lt i len then (if Int.equal (Char.to_int (String.get s i)) 46 then i else find_dot (Int.add i 1))
    else len in
  let n := find_dot 0 in
  let r := string_init n (fun i => sanitise_char (String.get s i)) in
  (* identifiers cannot start with a digit or a quote *)
  if Int.equal n 0 then "x"
  else
    let i0 := Char.to_int (String.get r 0) in
    if Bool.or (Bool.and (Int.le 48 i0) (Int.le i0 57)) (Int.equal i0 39)
    then String.concat "" ["x"; r] else r.

Ltac2 binder_ident (name : string) : ident :=
  let s := sanitise_string name in
  match Ident.of_string s with
  | Some id => id
  | None =>
      (* e.g. a reserved word *)
      StringToIdent.string_to_ident (String.concat "" [s; "_"])
  end.

(* [with_var name lt k] builds a lambda [fun x : Val lt => k x], where [x] is a fresh
   variable named after [lv], and [k] receives the variable together with its
   type so that terms inside can refer to it. *)
Ltac2 with_var (name : string) (lt : constr) (k : constr -> constr) : constr :=
  let base := binder_ident name in
  let id := Fresh.fresh (Fresh.Free.of_goal ()) base in
  Constr.in_context id constr:(Val $lt)
    (fun () => Control.refine (fun () => k (Control.hyp id))).

(* ------------------------------------------------------------------------ *)
(* Reified representation                                                    *)
(* ------------------------------------------------------------------------ *)
(* Erased symbolic propositions as Ltac2 data, following ETerm, EFormula and
   ESymProp. [constr] fields are kept for what is simply spliced back into the
   result: operators, values and types. *)

Ltac2 Type rec term := [
  | Var (int)                                        (* de Bruijn index *)
  | Val (constr)                                     (* v *)
  | Binop (constr, term, term)                       (* op t1 t2 *)
  | Unop (constr, term)                              (* op t *)
  | Tuple (eenv)                                     (* ts *)
  | Union (constr, constr, term)                     (* U K t *)
  | Record (constr, eenv)                            (* R ts *)
  ]
(* An environment of terms, innermost entry first. The nil constructor only
   records the type B of the bindings, Ty for an Env and N∷Ty for a NamedEnv;
   a snoc has B, the binding and the term. *)
with eenv := [
  | EnvNil (constr)
  | EnvSnoc (constr, constr, term, eenv)
  ].

Ltac2 Type rec formula := [
  | User (constr, eenv)                              (* p ts *)
  | Bool (term)
  | Relop (constr, term, term)                       (* op t1 t2 *)
  | FTrue
  | FFalse
  | And (formula, formula)
  | Or (formula, formula)
  ].

Ltac2 Type rec symprop := [
  | AngelicBin (symprop, symprop)
  | DemonicBin (symprop, symprop)
  | Error
  | Block
  | AssertK (formula, symprop)
  | AssumeK (formula, symprop)
  | Angelic (string, constr, symprop)                (* name σ k *)
  | Demonic (string, constr, symprop)
  | AssertVarEq (int, term, symprop)                 (* n t k *)
  | AssumeVarEq (int, term, symprop)
  ].

(* ------------------------------------------------------------------------ *)
(* Reification: ESymProp to Ltac2 data                                       *)
(* ------------------------------------------------------------------------ *)
(* Pattern matching is not supported and neither is the debug information,
   which inst_symprop ignores. *)

(* Split a `MkB lv lt` binder into its name and type, ignoring the implicit
   arguments (pattern matching on MkB fails on the real VC). *)
Ltac2 split_binder (b : constr) : constr * constr :=
  match Constr.Unsafe.kind b with
  | Constr.Unsafe.App _ args =>
      if Int.equal (Array.length args) 4
      then (Array.get args 2, Array.get args 3)
      else Control.zero (Tactic_failure (Some (fprintf "reify: unexpected binder '%t'" b)))
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unexpected binder '%t'" b)))
  end.

(* Evaluate binops on two Vals directly. *)
Ltac2 mk_binop (op : constr) (a : term) (b : term) : term :=
  match a, b with
  | Val v1, Val v2 => Val (Std.eval_vm None constr:(bop.eval $op $v1 $v2))
  | _, _ => Binop op a b
  end.

Ltac2 mk_unop (op : constr) (a : term) : term :=
  match a with
  | Val v => Val (Std.eval_vm None constr:(uop.eval $op $v))
  | _ => Unop op a
  end.

Ltac2 rec reify_term (st : constr) : term :=
  lazy_match! st with
  | @eterm_var _ _ ?n => Var (nat_to_int n)
  | eterm_val _ ?v => Val v
  | @eterm_binop _ _ _ ?op ?t1 ?t2 => mk_binop op (reify_term t1) (reify_term t2)
  | @eterm_unop _ _ ?op ?t => mk_unop op (reify_term t)
  | @eterm_tuple _ ?ts => Tuple (reify_env ts)
  | @eterm_union ?u ?k ?t => Union u k (reify_term t)
  | eterm_record ?r ?ts => Record r (reify_env ts)
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unknown ETerm constructor in '%t'" st)))
  end

with reify_env (e : constr) : eenv :=
  lazy_match! e with
  | @env.nil ?b _ => EnvNil b
  | @env.snoc ?b _ _ ?e' ?bb ?t => EnvSnoc b bb (reify_term t) (reify_env e')
  | @nenv.nil ?n ?ty _ => EnvNil constr:(Binding $n $ty)
  | @nenv.snoc ?n ?ty _ _ ?e' ?bb ?t =>
      EnvSnoc constr:(Binding $n $ty) bb (reify_term t) (reify_env e')
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unexpected environment '%t'" e)))
  end.

Ltac2 rec reify_formula (f : constr) : formula :=
  lazy_match! f with
  | @eformula_user ?p ?ts => User p (reify_env ts)
  | eformula_bool ?t => Bool (reify_term t)
  | @eformula_relop _ ?op ?t1 ?t2 => Relop op (reify_term t1) (reify_term t2)
  | eformula_true => FTrue
  | eformula_false => FFalse
  | eformula_and ?a ?b => And (reify_formula a) (reify_formula b)
  | eformula_or ?a ?b => Or (reify_formula a) (reify_formula b)
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unknown EFormula constructor in '%t'" f)))
  end.

Ltac2 rec reify_sp (sp : constr) : symprop :=
  lazy_match! sp with
  | eangelic_binary ?a ?b => AngelicBin (reify_sp a) (reify_sp b)
  | edemonic_binary ?a ?b => DemonicBin (reify_sp a) (reify_sp b)
  | eerror _ => Error
  | eblock => Block
  | eassertk ?f ?k => AssertK (reify_formula f) (reify_sp k)
  | eassumek ?f ?k => AssumeK (reify_formula f) (reify_sp k)
  | eangelicv ?binder ?k =>
      let (lv, lt) := split_binder binder in
      Angelic (StringToIdent.coq_string_to_string lv) lt (reify_sp k)
  | edemonicv ?binder ?k =>
      let (lv, lt) := split_binder binder in
      Demonic (StringToIdent.coq_string_to_string lv) lt (reify_sp k)
  | @eassert_vareq _ _ ?n ?t ?k => AssertVarEq (nat_to_int n) (reify_term t) (reify_sp k)
  | @eassume_vareq _ _ ?n ?t ?k => AssumeVarEq (nat_to_int n) (reify_term t) (reify_sp k)
  | edebug _ ?k => reify_sp k
  | epattern_match _ _ _ =>
      Control.zero (Tactic_failure (Some (fprintf "reify: pattern matching is not supported in '%t'" sp)))
  | epattern_match_var _ _ _ _ =>
      Control.zero (Tactic_failure (Some (fprintf "reify: pattern matching is not supported in '%t'" sp)))
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unknown ESymProp constructor in '%t'" sp)))
  end.

(* ------------------------------------------------------------------------ *)
(* Reflection: Ltac2 data to Prop                                            *)
(* ------------------------------------------------------------------------ *)

(* The domain of the environment of values matching an environment of terms
   over B. *)
(* The names of a binding type [N∷Ty]. *)
Ltac2 binding_names (b : constr) : constr :=
  lazy_match! b with
  | Binding ?n _ => n
  end.

Ltac2 rec reflect_term (ctx : constr list) (t : term) : constr :=
  match t with
  | Var n => List.nth ctx n
  | Val v => v
  | Binop op a b =>
      let ra := reflect_term ctx a in
      let rb := reflect_term ctx b in
      Std.eval_unfold [(reference:(bop.eval), Std.AllOccurrences)] constr:(bop.eval $op $ra $rb)
  | Unop op a =>
      let ra := reflect_term ctx a in
      Std.eval_unfold [(reference:(uop.eval), Std.AllOccurrences)] constr:(uop.eval $op $ra)
  | Tuple e =>
      let vs := reflect_env ctx e in
      constr:(envrec.of_env _ $vs)
  | Union u k a =>
      let v := reflect_term ctx a in
      constr:(unionv_fold $u (existT $k $v))
  | Record r e =>
      let vs := reflect_env ctx e in
      constr:(recordv_fold $r $vs)
  end

with reflect_env (ctx : constr list) (e : eenv) : constr :=
  match e with
  | EnvNil b =>
      if Constr.equal b constr:(Ty) then constr:(@env.nil Ty Val)
      else let n := binding_names b in constr:(@nenv.nil $n Ty Val)
  | EnvSnoc b bb t rest =>
      let vs := reflect_env ctx rest in
      let v := reflect_term ctx t in
      if Constr.equal b constr:(Ty) then constr:(@env.snoc Ty Val _ $vs $bb $v)
      else let n := binding_names b in constr:(@nenv.snoc $n Ty Val _ $vs $bb $v)
  end.

Ltac2 rec reflect_formula (ctx : constr list) (f : formula) : constr :=
  match f with
  | User p e =>
      let vs := reflect_env ctx e in
      constr:(env.uncurry (𝑷_inst $p) $vs)
  | Bool t => let rt := reflect_term ctx t in constr:($rt = true)
  | Relop op a b =>
      let ra := reflect_term ctx a in
      let rb := reflect_term ctx b in
      Std.eval_unfold [(reference:(bop.eval_relop_prop), Std.AllOccurrences)] constr:(bop.eval_relop_prop $op $ra $rb)
  | FTrue => constr:(True)
  | FFalse => constr:(False)
  | And a b =>
      let ra := reflect_formula ctx a in
      let rb := reflect_formula ctx b in
      constr:($ra /\ $rb)
  | Or a b =>
      let ra := reflect_formula ctx a in
      let rb := reflect_formula ctx b in
      constr:($ra \/ $rb)
  end.

Ltac2 rec reflect_sp (ctx : constr list) (sp : symprop) : constr :=
  match sp with
  | AngelicBin a b =>
      let refla := reflect_sp ctx a in
      let reflb := reflect_sp ctx b in
      constr:($refla \/ $reflb)
  | DemonicBin a b =>
      let refla := reflect_sp ctx a in
      let reflb := reflect_sp ctx b in
      constr:($refla /\ $reflb)
  | Error => constr:(False)
  | Block => constr:(True)
  | AssertK f k =>
      let reflf := reflect_formula ctx f in
      let reflk := reflect_sp ctx k in
      constr:($reflf /\ $reflk)
  | AssumeK f k =>
      let reflf := reflect_formula ctx f in
      let reflk := reflect_sp ctx k in
      constr:(forall _ : $reflf, $reflk)
  | Angelic name lt k =>
      let lam := with_var name lt (fun x => reflect_sp (x :: ctx) k) in
      constr:(@ex (Val $lt) $lam)
  | Demonic name lt k =>
      let lam := with_var name lt (fun x => reflect_sp (x :: ctx) k) in
      match Constr.Unsafe.kind lam with
      | Constr.Unsafe.Lambda b c => Constr.Unsafe.make (Constr.Unsafe.Prod b c)
      | _ => Control.throw (Tactic_failure (Some (fprintf "reflect_sp: expected a lambda but got '%t'" lam)))
      end
  | AssertVarEq n t k =>
      (* the variable n is replaced by the term t in the continuation *)
      let ctx' := list_remove ctx n in
      let x := List.nth ctx n in
      let rt := reflect_term ctx' t in
      let rk := reflect_sp ctx' k in
      constr:($x = $rt /\ $rk)
  | AssumeVarEq n t k =>
      let ctx' := list_remove ctx n in
      let x := List.nth ctx n in
      let rt := reflect_term ctx' t in
      let rk := reflect_sp ctx' k in
      constr:(forall _ : ($x = $rt), $rk)
  end.

(* ------------------------------------------------------------------------ *)
(* Tactic                                                                    *)
(* ------------------------------------------------------------------------ *)

(* The Ltac1 entry point. Control.enter is needed for this to work with all:
   and ; on multiple goals. *)
Ltac reify_vc := ltac2:(Control.enter (fun () =>
  match! goal with
  | [ |- VerificationConditionWithErasure ?p ] =>
      let r := reflect_sp [] (reify_sp p) in
      constructor; change $r
  end)).
