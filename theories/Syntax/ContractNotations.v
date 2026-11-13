(******************************************************************************)
(* Copyright (c) 2026 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

(* Hoare-triple style notations for function contracts and lemmas.

   Syntax:

     {{ PRE }} fn f [arg₁; …; argₙ] τ {{ res, POST }} with [x₁ :: σ₁; …; xₘ :: σₘ]
     {{ PRE }} lem l [arg₁; …; argₙ] {{ POST }} with [x₁ :: σ₁; …; xₘ :: σₘ]

   where
   - [f] is a function symbol ([Fun] or [FunX]) with parameters [Δ] and result
     type [τ], and [l] is a lemma symbol ([Lem]) with parameters [Δ];
   - [arg₁; …; argₙ] describes the [n] parameters in [Δ], in order.
     Each [argᵢ] is either
       [y :: σ]         the parameter [y] of type [σ], also bound to the logic
                        variable [y], or
       [arg_pat σ Σ t]  a parameter of type [σ] that equals the term [t], over
                        the logic variables [Σ]; its name is the one in [Δ].
     Case studies can add notations for [arg_pat] to [arg_scope], e.g.
     MinimalCaps writes [(p, b, e, a) :: ty.cap] to destructure a capability
     into its fields;
   - [x₁ :: σ₁; …; xₘ :: σₘ] are further logic variables, e.g. for values that
     only occur in [PRE] and [POST]. [with […]] can be left out when [m = 0];
   - [PRE] and [POST] are assertions over all these logic variables, and for
     functions [POST] can also refer to the result [res :: τ].

   The logic variables of the contract are those of [arg₁], …, [argₙ], then
   [x₁], …, [xₘ]. Logic variables of the arguments with the same name and type
   are the same variable, e.g. a field shared by two destructured arguments.
   The names [x₁], …, [xₘ] must be new: different from each other and from
   the logic variables of the arguments.

   The notations report an error, saying what is wrong, when
   - one name is used for logic variables of different types;
   - a name after [with] is not new;
   - the argument list does not match [Δ] (the number of parameters, or their
     names or types), or the result type is not [τ]. *)

From Equations Require Import
     Equations.
From Katamaran Require Import
     Base
     Notations
     Prelude
     Symbolic.Worlds
     Syntax.Assertions
     Syntax.Predicates.

Import ctx.notations.
Import env.notations.

Declare Scope arg_scope.
Delimit Scope arg_scope with arg.

Module Type ContractNotationsOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import W : WorldsMixin B P)
  (Import AS : AssertionsOn B P W).

Module ContractNotations.

  (* Description of a single argument of a function or lemma. *)
  Inductive ArgBinding : Type :=
  (* A program variable [x] of type [σ], bound to the logic variable [x]. *)
  | arg_var (x : PVar) (σ : Ty)
  (* An argument of type [σ] that equals [t], over the logic variables [Σ]. *)
  | arg_pat (σ : Ty) (Σ : LCtx) (t : Term Σ σ).

  Definition ArgCtx : Type := Ctx ArgBinding.

  Definition arg_type (a : ArgBinding) : Ty :=
    match a with
    | arg_var _ σ   => σ
    | arg_pat σ _ _ => σ
    end.

  (* The name of the program variable; [y] is the name in the signature. *)
  Definition arg_name (a : ArgBinding) (y : PVar) : PVar :=
    match a with
    | arg_var x _   => x
    | arg_pat _ _ _ => y
    end.

  (* The logic variables introduced by an argument. *)
  Definition arg_lvars (a : ArgBinding) : LCtx :=
    match a with
    | arg_var x σ   => ε ▻ PVartoLVar x∷σ
    | arg_pat _ Σ _ => Σ
    end.

  (* The term that the argument is bound to in the local store. *)
  Definition arg_term (a : ArgBinding) : Term (arg_lvars a) (arg_type a) :=
    match a with
    | arg_var x σ   => term_var_in ctx.in_zero
    | arg_pat _ _ t => t
    end.

  (* Find the logic variable [x∷σ] in [Γ]. *)
  Fixpoint lvar_find (Γ : LCtx) (x : LVar) (σ : Ty) : option (x∷σ ∈ Γ) :=
    match Γ with
    | ε        => None
    | Γ ▻ y∷τ =>
        match eq_dec x y , eq_dec σ τ with
        | left ex , left eσ =>
            Some
              (match ex in (_ = y') return (x∷σ ∈ Γ ▻ y'∷τ) with
               | eq_refl =>
                   match eσ in (_ = τ') return (x∷σ ∈ Γ ▻ x∷τ') with
                   | eq_refl => ctx.in_zero
                   end
               end)
        | _ , _ => option.map ctx.in_succ (lvar_find Γ x σ)
        end
    end.

  (* [Σ1] extended with the logic variables of [Σ2] that are not in it yet,
     together with the inclusions of [Σ1] and [Σ2] into it. A variable of [Σ2]
     with the same name and type as one in [Σ1] (or earlier in [Σ2]) is
     identified with it. A variable with the same name as an earlier one but a
     different type is added as a separate variable, which then shadows the
     earlier one; the notations reject that case (see [lctx_clash]). *)
  Fixpoint lctx_union (Σ1 Σ2 : LCtx) :
    { Σ : LCtx & (Sub Σ1 Σ * Sub Σ2 Σ)%type } :=
    match Σ2 with
    | ε        => existT Σ1 (sub_id Σ1 , nenv.nil)
    | Σ2 ▻ x∷σ =>
        let u := lctx_union Σ1 Σ2 in
        match lvar_find (projT1 u) x σ with
        | Some xIn =>
            existT (projT1 u)
              (fst (projT2 u) ,
               nenv.snoc (snd (projT2 u)) (x∷σ) (term_var_in xIn))
        | None =>
            existT (projT1 u ▻ x∷σ)
              (subst (fst (projT2 u)) sub_wk1 ,
               nenv.snoc (subst (snd (projT2 u)) sub_wk1) (x∷σ)
                 (term_var_in ctx.in_zero))
        end
    end.

  (* The logic variables introduced by the arguments. Variables with the same
     name and type, e.g. a field shared by two destructured arguments, are the
     same logic variable. *)
  Fixpoint args_lvars (Γ : ArgCtx) : LCtx :=
    match Γ with
    | ε     => ε
    | Γ ▻ a => projT1 (lctx_union (args_lvars Γ) (arg_lvars a))
    end.

  (* The program variable context described by [Γ], where [Δ] is the program
     variable context of the signature. *)
  Fixpoint args_pctx (Γ : ArgCtx) (Δ : PCtx) : PCtx :=
    match Γ , Δ with
    | Γ ▻ a , Δ ▻ y∷_ => args_pctx Γ Δ ▻ arg_name a y∷arg_type a
    | _     , _       => ε
    end.

  Fixpoint args_store (Γ : ArgCtx) (Δ : PCtx) :
    SStore (args_pctx Γ Δ) (args_lvars Γ) :=
    match Γ , Δ with
    | Γ ▻ a , Δ ▻ y∷_ =>
        let u := lctx_union (args_lvars Γ) (arg_lvars a) in
        nenv.snoc
          (subst (args_store Γ Δ) (fst (projT2 u)))
          (arg_name a y∷arg_type a)
          (subst (arg_term a) (snd (projT2 u)))
    | ε     , _ => nenv.nil
    | _ ▻ _ , ε => nenv.nil
    end.

  (* The argument list of a contract for a function or lemma with program
     variable context [Δ], and for a function also the result type of the
     contract. *)
  Record FunSpec (Δ : PCtx) : Type :=
    MkFunSpec { funspec_args : ArgCtx; funspec_ret : Ty }.
  Record LemSpec (Δ : PCtx) : Type :=
    MkLemSpec { lemspec_args : ArgCtx }.
  #[global] Arguments funspec_args {Δ} _.
  #[global] Arguments funspec_ret {Δ} _.
  #[global] Arguments lemspec_args {Δ} _.

  (* [fn] and [lem] accept the function and lemma symbols of any program
     ([Fun], [FunX], [Lem]). The program variable context [Δ] is read off the
     type of the symbol by these classes. *)

  (* [FunSig A Δ]: [A] is the type of a function symbol with parameters [Δ];
     [LemSig A Δ] likewise for lemma symbols. They have no fields: finding an
     instance only serves to determine [Δ]. *)
  Class FunSig (A : Type) (Δ : PCtx) : Prop := fun_sig_intro {}.
  Class LemSig (A : Type) (Δ : PCtx) : Prop := lem_sig_intro {}.

  (* E.g. for [A = Fun ["a" ∷ ty.int] ty.int], applying [fun_sig] matches
     [F Δ τ] against [A], which gives [Δ = ["a" ∷ ty.int]]
     (and similar for lem_sig). *)
  #[export] Instance fun_sig {F : PCtx -> Ty -> Set} {Δ τ} : FunSig (F Δ τ) Δ := {}.
  #[export] Instance lem_sig {L : PCtx -> Set} {Δ} : LemSig (L Δ) Δ := {}.

  (* [A] is an input ([+]): only search once the type of the symbol is known,
     instead of inventing one of the form [F Δ τ]. [Δ] is an output ([-]). *)
  #[export] Hint Mode FunSig + - : typeclass_instances.
  #[export] Hint Mode LemSig + - : typeclass_instances.

  Definition fn {A : Type} (f : A) {Δ} `{FunSig A Δ} (args : ArgCtx) (ret : Ty) :
    FunSpec Δ := MkFunSpec Δ args ret.
  Definition lem {A : Type} (l : A) {Δ} `{LemSig A Δ} (args : ArgCtx) : LemSpec Δ :=
    MkLemSpec Δ args.
  #[global] Arguments fn {A} f {Δ _} args%_arg ret.
  #[global] Arguments lem {A} l {Δ _} args%_arg.

  (* The logic variables of the arguments, followed by the extra ones [Σ]
     (which [NoLVarError] below requires to have new names). *)
  Definition contract_lvars (Γ : ArgCtx) (Σ : LCtx) : LCtx :=
    args_lvars Γ ▻▻ Σ.

  Definition contract_store (Γ : ArgCtx) (Δ : PCtx) (Σ : LCtx) :
    SStore (args_pctx Γ Δ) (contract_lvars Γ Σ) :=
    subst (args_store Γ Δ) (sub_cat_left Σ).

  (* Name clashes: a logic variable named like an earlier one, but with a
     different type. [lctx_clash Σ1 Σ2] looks for the first clash in the steps
     of [lctx_union Σ1 Σ2]. *)
  Fixpoint lctx_clash (Σ1 Σ2 : LCtx) : option (LVar * Ty * Ty) :=
    match Σ2 with
    | ε        => None
    | Σ2 ▻ x∷σ =>
        match lctx_clash Σ1 Σ2 with
        | Some c => Some c
        | None   =>
            match ctx.resolve (projT1 (lctx_union Σ1 Σ2)) x with
            | Some τ => if eq_dec σ τ then None else Some (x , τ , σ)
            | None   => None
            end
        end
    end.

  (* The first name clash among the logic variables of the arguments [Γ], as
     [(x, τ, σ)]: [x] was introduced earlier with type [τ], and again by a
     later argument (or later in the same argument) with type [σ]. It follows
     the steps of [args_lvars Γ]: each argument's variables are checked against
     those of the arguments before it. *)
  Fixpoint args_clash (Γ : ArgCtx) : option (LVar * Ty * Ty) :=
    match Γ with
    | ε     => None
    | Γ ▻ a =>
        match args_clash Γ with
        | Some c => Some c
        | None   => lctx_clash (args_lvars Γ) (arg_lvars a)
        end
    end.

  (* Errors in the logic variables of a contract. *)
  Inductive LVarError : Type :=
  (* The arguments introduce [x] with the conflicting types [σ] and [τ]. *)
  | lvar_types_differ (x : LVar) (σ τ : Ty)
  (* [x] is listed after [with], but is introduced by the arguments. *)
  | lvar_with_bound (x : LVar)
  (* [x] is listed twice after [with]. *)
  | lvar_with_twice (x : LVar).

  (* The first variable of [Σ] that has the name of an earlier one in [Σ], or
     one in [Σa]. Only names are compared, so this does not get stuck on types
     with variables. *)
  Fixpoint with_error (Σa Σ : LCtx) : option LVarError :=
    match Σ with
    | ε       => None
    | Σ ▻ x∷_ =>
        match with_error Σa Σ with
        | Some e => Some e
        | None   =>
            match ctx.resolve Σ x , ctx.resolve Σa x with
            | Some _ , _      => Some (lvar_with_twice x)
            | None   , Some _ => Some (lvar_with_bound x)
            | None   , None   => None
            end
        end
    end.

  Definition lvar_error (Γ : ArgCtx) (Σ : LCtx) : option LVarError :=
    match with_error (args_lvars Γ) Σ with
    | Some e => Some e
    | None   =>
        option.map (fun '(x , σ , τ) => lvar_types_differ x σ τ) (args_clash Γ)
    end.

  (* The notations below prove this with [check_contract]. *)
  Definition NoLVarError (e : option LVarError) : Prop :=
    match e with
    | None   => True
    | Some _ => False
    end.

  (* Mismatches between the argument list (and result type) of a contract and
     the signature of its function or lemma. These are type errors anyway, but
     [check_contract] reports them with a clearer message. *)
  Inductive SignatureMismatch : Type :=
  (* The argument list has no argument for the parameter [y]. *)
  | mismatch_missing (y : PVar)
  (* The argument list has more arguments than the signature has parameters. *)
  | mismatch_extra
  (* A plain argument [given :: _] for the parameter [expected]. *)
  | mismatch_name (expected given : PVar)
  (* An argument of type [given] for the parameter [x] of type [expected]. *)
  | mismatch_type (x : PVar) (expected given : Ty)
  (* A result type [given] for a function with result type [expected]. *)
  | mismatch_result (expected given : Ty).

  (* Compares arguments and parameters pairwise, for lists of equal length. *)
  Fixpoint args_mismatch_pairwise (Γ : ArgCtx) (Δ : PCtx) :
    option SignatureMismatch :=
    match Γ , Δ with
    | Γ ▻ a , Δ ▻ y∷τ =>
        match args_mismatch_pairwise Γ Δ with
        | Some m => Some m
        | None   =>
            match a with
            | arg_var x σ =>
                if eq_dec x y
                then if eq_dec σ τ then None else Some (mismatch_type y τ σ)
                else Some (mismatch_name y x)
            | arg_pat σ _ _ =>
                if eq_dec σ τ then None else Some (mismatch_type y τ σ)
            end
        end
    | _     , _       => None
    end.

  (* The parameter of [Δ] at position [k], counting from the last one, which is
     at position 0. *)
  Fixpoint param_from_end (k : nat) (Δ : PCtx) : option PVar :=
    match k , Δ with
    | 0   , _ ▻ y∷_ => Some y
    | S k , Δ ▻ _   => param_from_end k Δ
    | _   , ε       => None
    end.

  Definition args_mismatch (Γ : ArgCtx) (Δ : PCtx) : option SignatureMismatch :=
    let n := ctx.length Γ in
    let m := ctx.length Δ in
    if Nat.eqb n m then args_mismatch_pairwise Γ Δ
    else if Nat.ltb n m
    (* The first parameter without an argument is at position [n], counting
       from the first one, at position 0; so at position [m - n - 1] counting
       from the last one. *)
    then option.map mismatch_missing (param_from_end (m - n - 1) Δ)
    else Some mismatch_extra.

  Definition fun_mismatch (Γ : ArgCtx) (ret : Ty) (Δ : PCtx) (τ : Ty) :
    option SignatureMismatch :=
    match args_mismatch Γ Δ with
    | Some m => Some m
    | None   => if eq_dec ret τ then None else Some (mismatch_result τ ret)
    end.

  (* Fails with a message if [m] computes to a mismatch. Does nothing if it
     computes to [None], or if the computation gets stuck, e.g. on types that
     contain variables: the type of the contract is still checked then. *)
  Ltac report_mismatch m :=
    let m := eval compute in m in
    lazymatch m with
    | Some (mismatch_missing ?y) =>
        fail 0 "There is no argument for the parameter" y
    | Some mismatch_extra =>
        fail 0 "There are more arguments than parameters in the signature"
    | Some (mismatch_name ?y ?x) =>
        fail 0 "Argument" x "should be named" y "as in the signature"
    | Some (mismatch_type ?y ?τ ?σ) =>
        fail 0 "Argument" y "has type" σ "but the signature says" τ
    | Some (mismatch_result ?τ ?σ) =>
        fail 0 "The result type is" σ "but the signature says" τ
    | _ => idtac
    end.

  (* Proves [NoLVarError c] for the notations below, or fails with a message:
     when the argument list does not match the signature, or for an
     [LVarError]. The signature is read off the type [A]
     of the function or lemma symbol ([Fun Δ τ], [FunX Δ τ] or [Lem Δ]), since
     the [Δ] of [fn]/[lem] is still unresolved when this runs. *)
  Ltac check_contract :=
    lazymatch goal with
    | |- NoLVarError ?c =>
        lazymatch c with
        | context [@fn ?A _ _ _ ?args ?ret] =>
            lazymatch A with
            | _ ?Δ ?τ => report_mismatch (fun_mismatch args ret Δ τ)
            | _ => idtac
            end
        | context [@lem ?A _ _ _ ?args] =>
            lazymatch A with
            | _ ?Δ => report_mismatch (args_mismatch args Δ)
            | _ => idtac
            end
        | _ => idtac
        end;
        let c' := eval compute in c in
        lazymatch c' with
        | None => exact I
        | Some (lvar_types_differ ?x ?σ ?τ) =>
            fail 0 "Logic variable" x "is used with conflicting types" σ
              "and" τ
        | Some (lvar_with_bound ?x) =>
            fail 0 "Logic variable" x "is listed after [with], but the"
              "arguments already introduce it"
        | Some (lvar_with_twice ?x) =>
            fail 0 "Logic variable" x "is listed twice after [with]"
        (* Comparing types that contain variables can get stuck, e.g. when a
           name is repeated with type [σ] in a contract polymorphic in [σ]. *)
        | _ =>
            fail 0 "Could not decide whether some logic variable is used with"
              "different types, perhaps because a name is repeated with a type"
              "that contains a variable"
        end
    end.

  (* The tactic is wrapped in an abbreviation without arguments. *)
  Abbreviation contract_checked := (ltac:(check_contract)) (only parsing).

  Definition mk_contract {Δ} (f : FunSpec Δ) (Σ : LCtx)
    (pre : Assertion (contract_lvars (funspec_args f) Σ))
    (res : LVar)
    (post : Assertion (contract_lvars (funspec_args f) Σ ▻ res∷funspec_ret f))
    (_ : NoLVarError (lvar_error (funspec_args f) Σ)) :
    SepContract (args_pctx (funspec_args f) Δ) (funspec_ret f) :=
    MkSepContract _ _ (contract_lvars (funspec_args f) Σ)
      (contract_store (funspec_args f) Δ Σ) pre res post.

  Definition mk_lemma {Δ} (l : LemSpec Δ) (Σ : LCtx)
    (pre post : Assertion (contract_lvars (lemspec_args l) Σ))
    (_ : NoLVarError (lvar_error (lemspec_args l) Σ)) :
    Lemma (args_pctx (lemspec_args l) Δ) :=
    MkLemma _ (contract_lvars (lemspec_args l) Σ)
      (contract_store (lemspec_args l) Δ Σ) pre post.

  Notation "x '::' τ" := (arg_var x τ) : arg_scope.
  (* Argument lists need their own list notations. *)
  Notation "[ ]" := (ctx.nil) : arg_scope.
  Notation "[ctx]" := (ctx.nil) : arg_scope.
  Notation "[ x ]" := (ctx.snoc ctx.nil x%arg) : arg_scope.
  Notation "[ x ; y ; .. ; z ]" :=
    (ctx.snoc .. (ctx.snoc (ctx.snoc ctx.nil x%arg) y%arg) .. z%arg) : arg_scope.

  Notation "'{{' P '}}' f '{{' res ',' Q '}}' 'with' logvars" :=
    (mk_contract f logvars%ctx P res Q contract_checked)
      (at level 200, P at level 100, Q at level 100, res at level 100,
        f at level 100, logvars at level 100).
  Notation "'{{' P '}}' f '{{' res ',' Q '}}'" :=
    (mk_contract f ctx.nil P res Q contract_checked)
      (at level 200, P at level 100, Q at level 100, res at level 100,
        f at level 100).
  Notation "'{{' P '}}' l '{{' Q '}}' 'with' logvars" :=
    (mk_lemma l logvars%ctx P Q contract_checked)
      (at level 200, P at level 100, Q at level 100, l at level 100,
        logvars at level 100).
  Notation "'{{' P '}}' l '{{' Q '}}'" :=
    (mk_lemma l ctx.nil P Q contract_checked)
      (at level 200, P at level 100, Q at level 100, l at level 100).

End ContractNotations.

End ContractNotationsOn.
