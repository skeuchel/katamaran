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

(* Tests and examples for the contract notations of
   theories/Syntax/ContractNotations.v:

     {{ PRE }} fn f [arg₁; …; argₙ] τ {{ res, POST }} with [x₁ :: σ₁; …]
     {{ PRE }} lem l [arg₁; …; argₙ] {{ POST }} with [x₁ :: σ₁; …]

   Every signature built with [SignatureMixin] provides them in its
   [ContractNotations] module. This file defines a small program, writes its
   contracts with the notations, compares some of them with the contract
   records they stand for, and verifies the functions against them. *)

From Stdlib Require Import
     Strings.String
     ZArith.ZArith.
From Katamaran Require Import
     Defaults
     Program
     Semantics.Registers
     Signature
     Sep.Hoare
     Symbolic.Solver
     MicroSail.SymbolicExecutor.
From stdpp Require Import base.

Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

Import DefaultBase.

(* The program. *)
Module Import TestProgram <: Program DefaultBase.

  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
    | add      : Fun ["x" ∷ ty.int; "y" ∷ ty.int] ty.int
    | swap     : Fun ["p" ∷ ty.prod ty.int ty.int] (ty.prod ty.int ty.int)
    | fst_both : Fun ["p" ∷ ty.prod ty.int ty.int; "q" ∷ ty.prod ty.int ty.int] ty.int
    | call_fst : Fun ["z" ∷ ty.int] ty.int
    | call_fst_bad : Fun ["z" ∷ ty.int] ty.int
    | inc      : Fun ["x" ∷ ty.int] ty.int.

    (* A foreign function and a ghost lemma, to show that the notations also
       work for those. *)
    Inductive FunX : PCtx -> Ty -> Set :=
    | ext : FunX ["x" ∷ ty.int] ty.int.

    Inductive Lem : PCtx -> Set :=
    | pair_lemma : Lem ["p" ∷ ty.prod ty.int ty.int]
    | flag_pair_lemma : Lem ["b" ∷ ty.bool; "p" ∷ ty.prod ty.int ty.int].

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := FunX.
    Definition 𝑳  : PCtx -> Set := Lem.
  End FunDeclKit.

  Include FunDeclMixin DefaultBase.

  Section FunDefKit.
    Local Coercion stm_exp : Exp >-> Stm.
    Local Notation "'x'" := (exp_var "x") : exp_scope.
    Local Notation "'y'" := (exp_var "y") : exp_scope.
    Local Notation "'z'" := (exp_var "z") : exp_scope.
    Local Notation "'p'" := (exp_var "p") : exp_scope.
    Local Notation "'q'" := (exp_var "q") : exp_scope.
    Local Notation "'a'" := (exp_var "a") : exp_scope.
    Local Notation "'b'" := (exp_var "b") : exp_scope.

    Definition fun_add : Stm ["x" ∷ ty.int; "y" ∷ ty.int] ty.int :=
      x + y.

    Definition fun_swap : Stm ["p" ∷ ty.prod ty.int ty.int] (ty.prod ty.int ty.int) :=
      match: p in (ty.int , ty.int) with
      | ("a", "b") => exp_binop bop.pair b a
      end.

    (* Returns the first component of [q]. Its contract says that [p] and [q]
       have the same first component, so this also is the first component of
       [p]. *)
    Definition fun_fst_both :
      Stm ["p" ∷ ty.prod ty.int ty.int; "q" ∷ ty.prod ty.int ty.int] ty.int :=
      match: q in (ty.int , ty.int) with
      | ("a", "b") => a
      end.

    Definition fun_call_fst : Stm ["z" ∷ ty.int] ty.int :=
      call fst_both (exp_binop bop.pair z (exp_int 1))
                    (exp_binop bop.pair z (exp_int 2)).

    Definition fun_call_fst_bad : Stm ["z" ∷ ty.int] ty.int :=
      call fst_both (exp_binop bop.pair z (exp_int 1))
                    (exp_binop bop.pair (z + exp_int 1) (exp_int 2)).

    Definition fun_inc : Stm ["x" ∷ ty.int] ty.int :=
      x + exp_int 1.

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | add      => fun_add
      | swap     => fun_swap
      | fst_both => fun_fst_both
      | call_fst => fun_call_fst
      | call_fst_bad => fun_call_fst_bad
      | inc      => fun_inc
      end.
  End FunDefKit.

  Include DefaultRegStoreKit DefaultBase.

  (* The foreign function [ext] only shows that [fn] accepts [FunX] symbols.
     Its semantics only matters for relating contracts to the operational
     semantics (soundness), which this test does not do, so a trivial one will
     do: a call may have any outcome. *)
  Section ForeignKit.
    Definition Memory : Set := unit.
    Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs)
      (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop := True.
    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof. exists γ, μ, (inl ""). constructor. Qed.
  End ForeignKit.

  Include ProgramMixin DefaultBase.

  Import callgraph.

  Lemma fundef_bindfree (Δ : PCtx) (τ : Ty) (f : Fun Δ τ) :
    stm_bindfree (FunDef f).
  Proof. destruct f; now vm_compute. Qed.

  Definition 𝑭_call_graph := generic_call_graph.
  Lemma 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.
  Proof. apply generic_call_graph_wellformed, fundef_bindfree. Qed.

  (* Only needed for total correctness, which this test does not use. *)
  Definition 𝑭_accessible {Δ τ} (f : 𝑭 Δ τ) : option (Accessible 𝑭_call_graph f) :=
    None.

End TestProgram.

Module Import TestSig <: Signature DefaultBase.
  Include DefaultPredicateKit DefaultBase.
  Include PredicateMixin DefaultBase.
  Include WorldsMixin DefaultBase.
  Include DefaultSolverKit DefaultBase.
  Include SignatureMixin DefaultBase.
End TestSig.

Module Import TestProgramLogic :=
  MakeProgramLogic DefaultBase TestSig TestProgram.

Module Import TestSpecification.
  Import asn.notations.
  Import TestSig.ContractNotations.

  (****************************************************************************)
  (* Correct uses of the notations. The contracts are used by the program's   *)
  (* specification and verified at the end of this file.                      *)
  (****************************************************************************)

  (* Plain arguments: [x :: σ] is the parameter [x], and also the logic
     variable [x] in the pre- and postcondition. *)
  Definition sep_contract_add : SepContractFun add :=
    {{ ⊤ }}
      fn add ["x" :: ty.int; "y" :: ty.int] ty.int
    {{ "result", term_var "result" = term_var "x" + term_var "y" }}.

  (* The notation stands for this contract record. *)
  Goal sep_contract_add =
    {| sep_contract_logic_variables := ["x" ∷ ty.int; "y" ∷ ty.int];
       sep_contract_localstore      := [term_var "x"; term_var "y"];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         term_var "result" = term_var "x" + term_var "y";
    |}.
  Proof. reflexivity. Qed.

  (* Patterns. A case study can describe arguments by patterns: [arg_pat σ Σ t]
     is an argument of type [σ] that equals the term [t] over the logic
     variables [Σ]. Here, a pattern that destructures a pair into its
     components, with a notation for it in [arg_scope]. *)
  Definition pair_pat (l r : LVar) (σ τ : Ty) : ArgBinding :=
    arg_pat (ty.prod σ τ) [l ∷ σ; r ∷ τ]
      (term_binop bop.pair (term_var_in (ctx.in_succ ctx.in_zero))
         (term_var_in ctx.in_zero)).
  Notation "⦅ l , r ⦆ '::' σ '*' τ" := (pair_pat l r σ τ)
    (at level 60, σ at level 0, τ at level 0) : arg_scope.

  (* The parameter keeps its name ("p") from the signature of [swap]; its
     components are the logic variables "a" and "b". *)
  Definition sep_contract_swap : SepContractFun swap :=
    {{ ⊤ }}
      fn swap [⦅"a", "b"⦆ :: ty.int * ty.int] (ty.prod ty.int ty.int)
    {{ "result",
       term_var "result" = term_binop bop.pair (term_var "b") (term_var "a") }}.

  Goal sep_contract_swap =
    {| sep_contract_logic_variables := ["a" ∷ ty.int; "b" ∷ ty.int];
       sep_contract_localstore      :=
         [env].["p" ∷ ty.prod ty.int ty.int ↦
                  term_binop bop.pair (term_var "a") (term_var "b")];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         term_var "result" = term_binop bop.pair (term_var "b") (term_var "a");
    |}.
  Proof. reflexivity. Qed.

  (* Logic variables with the same name and type are the same variable: the
     contract only applies when [p] and [q] have the same first component. *)
  Definition sep_contract_fst_both : SepContractFun fst_both :=
    {{ ⊤ }}
      fn fst_both [⦅"a", "b"⦆ :: ty.int * ty.int; ⦅"a", "c"⦆ :: ty.int * ty.int]
        ty.int
    {{ "result", term_var "result" = term_var "a" }}.

  Goal sep_contract_fst_both =
    {| sep_contract_logic_variables := ["a" ∷ ty.int; "b" ∷ ty.int; "c" ∷ ty.int];
       sep_contract_localstore      :=
         [env].["p" ∷ ty.prod ty.int ty.int ↦
                  term_binop bop.pair (term_var "a") (term_var "b")]
              .["q" ∷ ty.prod ty.int ty.int ↦
                  term_binop bop.pair (term_var "a") (term_var "c")];
       sep_contract_precondition    := ⊤;
       sep_contract_result          := "result";
       sep_contract_postcondition   := term_var "result" = term_var "a";
    |}.
  Proof. reflexivity. Qed.

  Definition sep_contract_call_fst : SepContractFun call_fst :=
    {{ ⊤ }}
      fn call_fst ["z" :: ty.int] ty.int
    {{ "result", term_var "result" = term_var "z" }}.

  (* Extra logic variables are listed after [with]. They need new names. *)
  Definition sep_contract_inc : SepContractFun inc :=
    {{ term_var "x" = term_var "n" }}
      fn inc ["x" :: ty.int] ty.int
    {{ "result", term_var "result" = term_var "n" + term_val ty.int 1 }}
    with ["n" :: ty.int].

  Goal sep_contract_inc =
    {| sep_contract_logic_variables := ["x" ∷ ty.int; "n" ∷ ty.int];
       sep_contract_localstore      := [term_var "x"];
       sep_contract_precondition    := term_var "x" = term_var "n";
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         term_var "result" = term_var "n" + term_val ty.int 1;
    |}.
  Proof. reflexivity. Qed.

  (* Foreign functions use [fn] as well, and lemmas use [lem] and have no
     result. *)
  Definition sep_contract_ext : SepContractFunX ext :=
    {{ ⊤ }} fn ext ["x" :: ty.int] ty.int {{ "result", ⊤ }}.

  Definition lemma_pair_lemma : SepLemma pair_lemma :=
    {{ ⊤ }}
      lem pair_lemma [⦅"a", "b"⦆ :: ty.int * ty.int]
    {{ term_var "a" = term_var "a" }}.

  Definition lemma_flag_pair_lemma : SepLemma flag_pair_lemma :=
    {{ ⊤ }}
      lem flag_pair_lemma ["b" :: ty.bool; ⦅"x", "y"⦆ :: ty.int * ty.int]
    {{ ⊤ }}.

  (* Contracts can be polymorphic in a type [σ].

     Limitation: the notations check the argument list against the signature
     of the function, giving the error messages shown in [Errors] below. That
     check compares types, which gets stuck on [σ]: it cannot decide whether
     [ty.list σ] equals [ty.list σ]. The notations then skip it, and a wrong
     argument list would only show up as a plain type error, with no clear
     message. *)
  Section Polymorphic.
    Context (σ : Ty) (f : Fun ["xs" ∷ ty.list σ; "y" ∷ σ] ty.int).

    Definition sep_contract_poly : SepContract ["xs" ∷ ty.list σ; "y" ∷ σ] ty.int :=
      {{ ⊤ }}
        fn f ["xs" :: ty.list σ; "y" :: σ] ty.int
      {{ "result", ⊤ }}
      with ["z" :: σ].
  End Polymorphic.

  Definition contract_environment : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | add      => Some sep_contract_add
      | swap     => Some sep_contract_swap
      | fst_both => Some sep_contract_fst_both
      | call_fst => Some sep_contract_call_fst
      | call_fst_bad => Some sep_contract_call_fst
      | inc      => Some sep_contract_inc
      end.

  Definition contract_environment_foreign : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | ext => sep_contract_ext
      end.

  Definition lemma_environment : LemmaEnv :=
    fun Δ l =>
      match l with
      | pair_lemma      => lemma_pair_lemma
      | flag_pair_lemma => lemma_flag_pair_lemma
      end.

  #[export] Instance test_specification : Specification :=
    {| CEnv   := contract_environment;
       CEnvEx := contract_environment_foreign;
       LEnv   := lemma_environment;
       fail_rule_pre := true;
    |}.

End TestSpecification.

(******************************************************************************)
(* Incorrect uses of the notations. Each of these is rejected, which [Fail]   *)
(* checks; the comment above each case gives the error message.               *)
(******************************************************************************)
Module Errors.
  Import asn.notations.
  Import TestSig.ContractNotations.

  (* Errors in the logic variables. *)

  (* Logic variable "x" is listed after [with], but the arguments already
     introduce it *)
  Fail Definition with_bound : SepContractFun inc :=
    {{ ⊤ }} fn inc ["x" :: ty.int] ty.int {{ "result", ⊤ }}
    with ["x" :: ty.int].
  (* Logic variable "c" is listed after [with], but the arguments already
     introduce it *)
  Fail Definition with_bound_pattern : SepContractFun fst_both :=
    {{ ⊤ }}
      fn fst_both [⦅"a", "b"⦆ :: ty.int * ty.int; ⦅"a", "c"⦆ :: ty.int * ty.int]
        ty.int
    {{ "result", ⊤ }}
    with ["c" :: ty.bool].
  (* Logic variable "n" is listed twice after [with] *)
  Fail Definition with_twice : SepContractFun inc :=
    {{ ⊤ }} fn inc ["x" :: ty.int] ty.int {{ "result", ⊤ }}
    with ["n" :: ty.int; "n" :: ty.int].

  (* Logic variable "b" is used with conflicting types ty.bool and ty.int *)
  Fail Definition different_types : SepLemma flag_pair_lemma :=
    {{ ⊤ }}
      lem flag_pair_lemma ["b" :: ty.bool; ⦅"b", "y"⦆ :: ty.int * ty.int]
    {{ ⊤ }}.

  (* Mismatches with the signature: the argument list has to describe the
     parameters of the function or lemma, and the result type has to be the
     function's result type. *)

  (* Argument "z" should be named "y" as in the signature *)
  Fail Definition wrong_name : SepContractFun add :=
    {{ ⊤ }} fn add ["x" :: ty.int; "z" :: ty.int] ty.int {{ "result", ⊤ }}.
  (* Argument "y" has type ty.bool but the signature says ty.int *)
  Fail Definition wrong_type : SepContractFun add :=
    {{ ⊤ }} fn add ["x" :: ty.int; "y" :: ty.bool] ty.int {{ "result", ⊤ }}.
  (* Argument "q" has type (ty.prod ty.bool ty.int) but the signature says
     (ty.prod ty.int ty.int) *)
  Fail Definition wrong_pattern_type : SepContractFun fst_both :=
    {{ ⊤ }}
      fn fst_both [⦅"a", "b"⦆ :: ty.int * ty.int; ⦅"a", "c"⦆ :: ty.bool * ty.int]
        ty.int
    {{ "result", ⊤ }}.
  (* There is no argument for the parameter "y" *)
  Fail Definition missing_argument : SepContractFun add :=
    {{ ⊤ }} fn add ["x" :: ty.int] ty.int {{ "result", ⊤ }}.
  (* There are more arguments than parameters in the signature *)
  Fail Definition extra_argument : SepContractFun inc :=
    {{ ⊤ }} fn inc ["x" :: ty.int; "y" :: ty.int] ty.int {{ "result", ⊤ }}.
  (* The result type is ty.bool but the signature says ty.int *)
  Fail Definition wrong_result : SepContractFun add :=
    {{ ⊤ }} fn add ["x" :: ty.int; "y" :: ty.int] ty.bool {{ "result", ⊤ }}.
  (* Argument "q" should be named "p" as in the signature *)
  Fail Definition wrong_lemma : SepLemma pair_lemma :=
    {{ ⊤ }} lem pair_lemma ["q" :: ty.prod ty.int ty.int] {{ ⊤ }}.
End Errors.

(******************************************************************************)
(* Verification of the functions against the contracts written above.         *)
(******************************************************************************)
Module Import TestExecutor :=
  MakeExecutor DefaultBase TestSig TestProgram TestProgramLogic.

(* The functions satisfy their contracts. *)
Lemma valid_contract_add : Symbolic.ValidContractReflect sep_contract_add fun_add.
Proof. vm_reflexivity. Qed.

Lemma valid_contract_swap : Symbolic.ValidContractReflect sep_contract_swap fun_swap.
Proof. vm_reflexivity. Qed.

(* This needs [p] and [q] to share the logic variable "a". *)
Lemma valid_contract_fst_both :
  Symbolic.ValidContractReflect sep_contract_fst_both fun_fst_both.
Proof. vm_reflexivity. Qed.

(* Calling [fst_both] matches the arguments against its patterns; here the
   first components agree. *)
Lemma valid_contract_call_fst :
  Symbolic.ValidContractReflect sep_contract_call_fst fun_call_fst.
Proof. vm_reflexivity. Qed.

(* Here they do not, so the call cannot use the contract of [fst_both]. *)
Lemma invalid_contract_call_fst_bad :
  ~ Symbolic.ValidContractReflect sep_contract_call_fst fun_call_fst_bad.
Proof. now vm_compute. Qed.

Lemma valid_contract_inc : Symbolic.ValidContractReflect sep_contract_inc fun_inc.
Proof. vm_reflexivity. Qed.
