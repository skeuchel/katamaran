(******************************************************************************)
(* Copyright (c) 2022 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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

From Stdlib Require Import
     Bool.Bool
     Lists.List
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Defaults
     Program
     Semantics
     Semantics.Registers
     Sep.Hoare
     Signature
     Symbolic.Solver
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness.

From stdpp Require Import decidable finite.

Set Implicit Arguments.
Import ctx.notations.
Import env.notations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.
Import DefaultBase DefaultGlobalState.

Definition ty_X := ty.list ty.int.

(*** PROGRAM ***)

Module Import ReplayProgram <: Program DefaultGlobalState.

  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
    | main : Fun ["xs" :: ty_X] ty.unit
    | arith_example : Fun ["x" :: ty.int] ty.int
    | unit_example : Fun ε ty.unit.

    Inductive Lem : PCtx -> Set :=
    | open_list : Lem ε.

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := fun _ _ => Empty_set.
    Definition 𝑳 : PCtx -> Set := Lem.
  End FunDeclKit.

  Include FunDeclMixin DefaultGlobalState.

  Section FunDefKit.
    Import ctx.resolution.

    Local Coercion stm_exp : Exp >-> Stm.

    Definition fun_main : Stm ["xs" :: ty_X] ty.unit :=
      stm_lemma open_list [] ;;
      stm_val ty.unit tt.

    Definition fun_arith_example : Stm ["x" :: ty.int] ty.int :=
      (* Initialize local variables *)
      let: "y" := exp_val ty.int 0 in
      let: "z" := exp_val ty.int 0 in
      (if: exp_var "x" < exp_val ty.int 7
       then "y" <- (stm_val ty.int 1)
       else stm_fail _ "Error") ;;
       (* else "y" <- (stm_val ty.int 2)) ;; *)
      (if: exp_var "x" = exp_val ty.int 5
       then "z" <- (stm_val ty.int 3)
       else stm_fail _ "Error") ;;
      exp_var "x" + exp_var "y" + exp_var "z".

    Definition fun_unit_example : Stm ε ty.unit :=
      stm_val ty.unit tt.

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | main => fun_main
      | arith_example => fun_arith_example
      | unit_example => fun_unit_example
      end.
  End FunDefKit.

  Include DefaultRegStoreKit DefaultGlobalState.

  Section ForeignKit.
    Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs)
      (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop := False.
    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof. destruct f. Qed.
  End ForeignKit.

  Include ProgramMixin DefaultGlobalState.

  Import callgraph.

  Lemma fundef_bindfree (Δ : PCtx) (τ : Ty) (f : Fun Δ τ) :
    stm_bindfree (FunDef f).
  Proof. destruct f; now vm_compute. Qed.

  Definition 𝑭_call_graph := generic_call_graph.
  Lemma 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.
  Proof. apply generic_call_graph_wellformed, fundef_bindfree. Qed.

  Abbreviation AccessibleFun f := (Accessible 𝑭_call_graph f).

  Module Import WithAccessibleTactics.
    Import AccessibleTactics.

    Instance accessible_main : AccessibleFun main.
    Proof. accessible_proof. Qed.

    Instance accessible_arith_example : AccessibleFun arith_example.
    Proof. accessible_proof. Qed.

    Instance accessible_unit_example : AccessibleFun unit_example.
    Proof. accessible_proof. Qed.
  End WithAccessibleTactics.

  Definition 𝑭_accessible {Δ τ} (f : 𝑭 Δ τ) : option (AccessibleFun f) :=
    match f with
    | main => Some _
    | _ => Some _
    end.
End ReplayProgram.

Module Import ReplayPredicates.
  Import ListNotations.

  Inductive PurePredicate : Set :=
  (* PurePredicates for the arith example *)
  | Aₐ
  | Bₐ
  | Pₐ
  | Qₐ
  (* PurePredicates for the unit example *)
  | Aᵤ
  | Bᵤ
  | Cᵤ
  (* PurePredicates for the main example *)
  | Q.

  Definition interp_Qₐ (x : Val ty.int) : Prop :=
    False.

  Definition interp_Pₐ (x : Val ty.int) : Prop :=
    if x =? 5
    then interp_Qₐ 9
    else True.

  Definition interp_Aₐ (b : Val ty.bool) : Prop :=
    if b
    then interp_Qₐ 9
    else True.

  Definition interp_Bₐ (x : Val ty.int) (b : Val ty.bool) : Prop :=
    b = (x =? 5).

  Definition Q_aux (xs : Val ty_X) : bool :=
    match xs with
    | 0 :: xs => (1 =? 7)
    | _       => true
    end%list.

  Definition interp_Q (xs : Val ty_X) : Prop :=
    Q_aux xs = true.

  Axiom interp_Cᵤ : Prop.

  (* interp_Aᵤ only provided information for Cᵤ when b = true *)
  Definition interp_Aᵤ (b : Val ty.bool) : Prop :=
    if b
    then interp_Cᵤ
    else True.

  Definition interp_Bᵤ (b : Val ty.bool) : Prop :=
    b = true.

  Inductive Predicate : Set :=
  | P.

  Section TransparentObligations.
    Local Set Transparent Obligations.

    Derive NoConfusion for PurePredicate.
    Derive NoConfusion for Predicate.

  End TransparentObligations.

  Derive EqDec for PurePredicate.
  Derive EqDec for Predicate.
End ReplayPredicates.

Module Import ReplaySig <: Signature DefaultGlobalState.
  Section PredicateKit.
    Definition 𝑷 := PurePredicate.
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | Aₐ => [ty.bool]
      | Bₐ => [ty.int;ty.bool]
      | Aᵤ => [ty.bool]
      | Bᵤ => [ty.bool]
      | Cᵤ => []
      | Pₐ => [ty.int]
      | Qₐ => [ty.int]
      | Q => [ty_X]
      end.
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | Aₐ => interp_Aₐ
      | Bₐ => interp_Bₐ
      | Aᵤ => interp_Aᵤ
      | Bᵤ => interp_Bᵤ
      | Cᵤ => interp_Cᵤ
      | Pₐ => interp_Pₐ
      | Qₐ => interp_Qₐ
      | Q => interp_Q
      end.
    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | P => [ty_X]
      end.
    Global Instance 𝑯_is_dup : IsDuplicable 𝑯 := {
        is_duplicable p := false
      }.
    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

    Local Arguments Some {_} &.
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | P => Some (MkPrecise ε [ty_X] eq_refl)
      end.
  End PredicateKit.

  Include PredicateMixin DefaultGlobalState.
  Include WorldsMixin DefaultGlobalState.

  Section ReplaySolverKit.
    Import List.ListNotations.
    Import Entailment.

    Definition simplify_Pₐ {Σ} (x : Term Σ ty.int) : option (PathCondition Σ) :=
      let no_simplification := Some [formula_user Pₐ [x]] in
      match term_get_val x with
      | Some v =>
          if v =? 5
          then Some [formula_user Qₐ [term_val ty.int 9]]
          else no_simplification
      | _ => no_simplification
      end.

    Definition simplify_Q {Σ} (xs : Term Σ ty_X) : option (PathCondition Σ) :=
      let no_simplification := Some [formula_user Q [xs]] in
      match term_get_val xs with
      | Some ls => match ls with
                   | 0 :: _ => Some [formula_relop bop.eq (term_val ty.int 1%Z) (term_val ty.int 7%Z)]%ctx
                   | _      => no_simplification
                   end%list
      | _       => no_simplification
      end.

    Definition simplify_Aₐ {Σ} (b : Term Σ ty.bool) : option (PathCondition Σ) :=
      let no_simplification := Some [formula_user Aₐ [b]] in
      match term_get_val b with
      | Some b =>
          if b
          then Some [formula_user Qₐ [term_val ty.int 9]]
          else no_simplification
      | None => no_simplification
      end.

    Definition simplify_Bₐ {Σ} (x : Term Σ ty.int) (b : Term Σ ty.bool) : option (PathCondition Σ) :=
      let no_simplification := Some [formula_user Bₐ [x;b]] in
      match term_get_val x with
      | Some x =>
          if x =? 5
          then Some [formula_relop bop.eq b (term_val ty.bool true)]
          else Some [formula_relop bop.eq b (term_val ty.bool false)]
      | None => no_simplification
      end.

    Definition simplify_Aᵤ {Σ} (b : Term Σ ty.bool) : option (PathCondition Σ) :=
      let no_simplification := Some [formula_user Aᵤ [b]] in
      match term_get_val b with
      | Some b =>
          if b
          then Some [formula_user Cᵤ []]
          else no_simplification
      | None => no_simplification
      end.

    Definition simplify_Bᵤ {Σ} (b : Term Σ ty.bool) : option (PathCondition Σ) :=
      Some [formula_eq b (term_val ty.bool true)].

    Equations(noeqns) simplify_user [Σ] (p : 𝑷) : Env (Term Σ) (𝑷_Ty p) -> option (PathCondition Σ) :=
    | Aₐ | [env b]  => simplify_Aₐ b
    | Bₐ | [env x; b]  => simplify_Bₐ x b
    | Aᵤ | [env b] => simplify_Aᵤ b
    | Bᵤ | [env b] => simplify_Bᵤ b
    | Cᵤ | [env]   => Some [formula_user Cᵤ []]
    | Pₐ | [env x]  => simplify_Pₐ x
    | Qₐ | [env x]  => Some [formula_user Qₐ [x]]
    | Q | [env xs ] => simplify_Q xs.

    Local Ltac lsolve :=
      repeat
        lazymatch goal with
        | |- Some _             ⊣⊢ Some _             => apply @proper_some
        | |- ctx.snoc ctx.nil _ ⊣⊢ ctx.snoc ctx.nil _ => apply proper_snoc; [easy|]
        | |- None               ⊣⊢ Some _             => apply @unsatisfiable_none_some
        | |- [ctx]              ⊣⊢ _                  => apply nil_l_valid
        | |- Unsatisfiable (ctx.snoc ctx.nil _)       => apply unsatisfiable_snoc_r
        | |- match @term_get_val ?Σ ?σ ?v with _ => _ end ⊣⊢ _ =>
            destruct (@term_get_val_spec Σ σ v); subst; try progress cbn
        | |- match @term_get_list ?Σ ?σ ?v with _ =>_ end ⊣⊢ _ =>
            destruct (@term_get_list_spec Σ σ v) as [[] ?|]; subst; try progress cbn
        | |- match @term_get_pair ?Σ ?σ₁ ?σ₂ ?v with _ =>_ end ⊣⊢ _ =>
            destruct (@term_get_pair_spec Σ σ₁ σ₂ v); subst; try progress cbn
        | |- match @term_get_record ?r ?Σ ?v with _ =>_ end ⊣⊢ _ =>
            destruct (@term_get_record_spec Σ r v); subst; try progress cbn
        | H: ?fst * ?snd |- _ =>
            destruct H; subst; try progress cbn
        end; try easy; auto.

    Lemma simplify_user_spec : SolverUserOnlySpec simplify_user.
    Proof.
      intros Σ p ts.
      destruct p; cbv in ts; env.destroy ts; cbn; lsolve.
      - unfold simplify_Aₐ; lsolve.
        destruct a; lsolve.
      - unfold simplify_Bₐ; lsolve.
        destruct (a =? 5) eqn:Ea; lsolve.
        apply Z.eqb_eq in Ea. subst.
        intros ι. now cbn.
        intros ι. cbn. unfold interp_Bₐ. rewrite Ea. auto.
      - unfold simplify_Pₐ; lsolve.
        destruct (a =? 5) eqn:Ea; lsolve.
        apply Z.eqb_eq in Ea. subst.
        intros ι. now cbn.
      - unfold simplify_Aᵤ; lsolve.
        destruct a; lsolve.
      - unfold simplify_Q; lsolve.
        destruct a; lsolve.
        destruct v; lsolve.
    Qed.

    Definition solver : Solver :=
      solveruseronly_to_solver simplify_user.

    Lemma solver_spec : SolverSpec solver.
    Proof.
      apply solveruseronly_to_solver_spec, simplify_user_spec.
    Qed.
  End ReplaySolverKit.

  Include SignatureMixin DefaultGlobalState.

End ReplaySig.

Module Import ReplayProgramLogic :=
  MakeProgramLogic DefaultGlobalState ReplaySig ReplayProgram.
(* Compose the symbolic executor and symbolic verification condition generator. *)
Module Import ReplayExecutor :=
  MakeExecutor DefaultGlobalState ReplaySig ReplayProgram ReplayProgramLogic.
(* Also instantiate the shallow executor for the soundness proofs and the
   statistics. *)
Module Import ReplayShalExec :=
  MakeShallowExecutor DefaultGlobalState ReplaySig ReplayProgram ReplayProgramLogic.
(* Instantiate the operational semantics which is an input to the Iris model. *)
Module ReplaySemantics <: Semantics DefaultGlobalState ReplayProgram :=
  MakeSemantics DefaultGlobalState ReplayProgram.

(* The specification module contains the contracts for all μSail and foreign functions. *)
Module Import ReplaySpecification.
  Import ctx.resolution.
  Import List.ListNotations.

  Section ContractDefKit.

    Import asn.notations.
    Abbreviation asn_prop Σ P := (asn.formula (@formula_prop Σ Σ (sub_id Σ) P)).
    Abbreviation asn_P xs := (asn.chunk (chunk_user P [xs])).
    Abbreviation asn_Q xs := (asn.formula (formula_user Q [xs])).

    Definition sep_contract_main : SepContract ["xs" :: ty_X] ty.unit :=
      {| sep_contract_logic_variables := ["xs" :: ty_X];
         sep_contract_localstore      := [term_var "xs"];
         sep_contract_precondition    := asn_Q (term_var "xs") ∗ asn_P (term_var "xs");
         sep_contract_result          := "_";
         sep_contract_postcondition   := term_val ty.int 1%Z = term_val ty.int 7%Z;
      |}.

    Definition contract_environment : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | main => Some sep_contract_main
        | _    => None
        end.

    Definition contract_environment_foreign : SepContractEnvEx :=
      fun Δ τ f =>
        match f with end.

    Definition lemma_open_list : SepLemma open_list :=
      {| lemma_logic_variables := ["l" :: ty_X];
         lemma_patterns        := env.nil;
         lemma_precondition    := asn_P (term_var "l");
         lemma_postcondition   := term_var "l" = term_list [term_val ty.int 0%Z];
      |}.

    Definition lemma_environment : LemmaEnv :=
      fun Δ l =>
        match l with
        | open_list => lemma_open_list
        end.

  End ContractDefKit.

  #[export] Instance replay_specification : Specification :=
    {| CEnv   := contract_environment;
       CEnvEx := contract_environment_foreign;
       LEnv   := lemma_environment;
       fail_rule_pre := true;
    |}.

End ReplaySpecification.

Lemma shallow_valid_contract_main : Shallow.ValidContract sep_contract_main (FunDef main).
Proof.
  cbn.
  intros v HQ.
  compute.
  exists v.
  split; auto.
  intros ->.
  unfold interp_Q in HQ.
  now cbn in HQ.
Qed.

Lemma symbolic_no_replay_valid_contract_main :
  VerificationCondition
    (postprocess
       (postprocess (ReplayExecutor.vcgen default_config 1 sep_contract_main (FunDef main) wnil))).
Proof.
  compute. (* Output: replay would solve more than what we see here! Once we now the shape of the list, the Q predicate can be simplified in a way that makes the goal trivial to solve. *)
  constructor.
  compute.
  firstorder.
Qed.

Lemma symbolic_replay_valid_contract_main :
  VerificationCondition
    (postprocess
       (SPureSpec.replay (postprocess (ReplayExecutor.vcgen default_config 1 sep_contract_main (FunDef main) wnil)))).
Proof.
  compute. (* Output: with the replay functionality the residu VC is trivial. *)
  firstorder.
Qed.

(* IMPORTANT: Abort is being used in these lemmas to indicate that it could be
              solve easier with Replay. It doesn't mean the lemma doesn't hold
              and should only be considered to be indicative (doc for how/what
              Replay does). *)
Section ReplayExamples.
  Import Symbolic.
  Import ctx.resolution.
  Import asn.notations.

  #[local] Abbreviation P := (interp_Pₐ).
  #[local] Abbreviation Q := (interp_Qₐ).
  #[local] Notation "a <= b" := ((term_binop (bop.relop bop.le) a b = term_val ty.bool true)).

  Definition ValidContractWithoutReplay {Δ τ} (c : SepContract Δ τ)
    (s : Stm Δ τ) : Prop :=
    VerificationCondition
      (postprocess
         (postprocess (ReplayExecutor.vcgen default_config 1 c s wnil))).

  Section ArithExample.

    Definition arith_contract1 : SepContract ["x" :: ty.int] ty.int :=
      {|
        sep_contract_logic_variables := ["x"∷ty.int];
        sep_contract_localstore := [term_var "x"];
        sep_contract_precondition :=
          asn.formula (formula_user Pₐ [term_var "x"]);
        sep_contract_result := "r";
        sep_contract_postcondition :=
          asn.formula (formula_user Qₐ [term_var "r"])
      |}.

    Definition arith_contract2 : SepContract ["x" :: ty.int] ty.int :=
      {|
        sep_contract_logic_variables := ["x"∷ty.int;"b"∷ty.bool];
        sep_contract_localstore := [term_var "x"];
        sep_contract_precondition :=
          asn.formula (formula_user Aₐ [term_var "b"])
            ∗ asn.formula (formula_user Bₐ [term_var "x"; term_var "b"]);
        sep_contract_result := "r";
        sep_contract_postcondition :=
          asn.formula (formula_user Qₐ [term_var "r"])
      |}.

    Definition arith_contract_debug : SepContract ["x" :: ty.int] ty.int :=
      {|
        sep_contract_logic_variables := ["x"∷ty.int;"b"∷ty.bool];
        sep_contract_localstore := [term_var "x"];
        sep_contract_precondition :=
          asn.formula (formula_user Aₐ [term_var "b"])
            ∗ asn.formula (formula_user Bₐ [term_val ty.int 5; term_var "b"]);
        sep_contract_result := "r";
        sep_contract_postcondition :=
          asn.formula (formula_user Qₐ [term_var "r"])
      |}.

    Lemma valid_arith_contract1_no_replay : ValidContractWithoutReplay arith_contract1 (FunDef arith_example).
    Proof.
      compute.
      constructor.
      cbn.
    Abort.

    Definition test1 := Eval compute in ReplayExecutor.vcgen default_config 1 arith_contract1 (FunDef arith_example)wnil.
    Definition test2 := Eval compute in postprocess test1.
    Definition test3 := Eval compute in SPureSpec.replay (w := wnil) test2.
    Definition test4 := Eval compute in postprocess test3.
    
    Lemma valid_arith_contract1_with_replay : ValidContract arith_contract1 (FunDef arith_example).
    Proof.
      now compute.
    Qed.

    Lemma valid_arith_contract2_no_replay : ValidContractWithoutReplay arith_contract2 (FunDef arith_example).
    Proof.
      compute.
      constructor.
      cbn.
    Abort.

    Lemma valid_arith_contract2_with_replay : ValidContract arith_contract2 (FunDef arith_example).
    Proof.
      now compute.
    Qed.

    Lemma valid_arith_contract_debug_no_replay : ValidContractWithoutReplay arith_contract_debug (FunDef arith_example).
    Proof.
      compute. (* Here we see (Aₐ true) but not simplified (even though it *is* possible!) *)
      constructor.
      cbn - [interp_Aₐ].
      cbn [interp_Aₐ].
    Abort.

    Lemma valid_arith_contract_debug_with_replay : ValidContract arith_contract_debug (FunDef arith_example).
    Proof.
      compute. (* Here Aₐ is simplified to (Qₐ 9) (first assume node), thanks to Replay *)
      constructor.
      cbn.
      (* Replay should go over formula_user Aₐ again? *)
    Admitted.
  End ArithExample.

  Section UnitExample.

    Definition unit_contract1 : SepContract ε ty.unit :=
      {|
        sep_contract_logic_variables := ["b" :: ty.bool];
        sep_contract_localstore := []%env;
        sep_contract_precondition :=
          asn.formula (formula_user Aᵤ [term_var "b"])
          ∗ asn.formula (formula_user Bᵤ [term_var "b"]);
        sep_contract_result := "r";
        sep_contract_postcondition :=
          asn.formula (formula_user Cᵤ [])
      |}.

    Definition unit_contract2 : SepContract ε ty.unit :=
      {|
        sep_contract_logic_variables := ["b" :: ty.bool];
        sep_contract_localstore := []%env;
        sep_contract_precondition :=
          asn.formula (formula_user Bᵤ [term_var "b"])
          ∗ asn.formula (formula_user Aᵤ [term_var "b"]);
        sep_contract_result := "r";
        sep_contract_postcondition :=
          asn.formula (formula_user Cᵤ [])
      |}.

    (* This contract remove B and just assumes that b = true directly *)
    Definition unit_contract3 : SepContract ε ty.unit :=
      {|
        sep_contract_logic_variables := ["b" :: ty.bool];
        sep_contract_localstore := []%env;
        sep_contract_precondition :=
          asn.formula (formula_user Aᵤ [term_var "b"])
          ∗ term_var "b" = term_val ty.bool true;
        sep_contract_result := "r";
        sep_contract_postcondition :=
          asn.formula (formula_user Cᵤ [])
      |}.

    Definition unit_contract_int : SepContract ε ty.unit :=
      {|
        sep_contract_logic_variables := ["a" :: ty.int; "b" :: ty.int];
        sep_contract_localstore := []%env;
        sep_contract_precondition :=
          term_var "a" + term_var "b" = term_val ty.int 5
          ∗ term_var "b" = term_val ty.int 0;
        sep_contract_result := "_";
        sep_contract_postcondition :=
          (term_var "a") <= (term_val ty.int 5);
      |}.

    Lemma valid_unit_contract1_no_replay : ValidContractWithoutReplay unit_contract1 (FunDef unit_example).
    Proof.
      compute.
      constructor. (* No Replay, so we get "assume (Aᵤ true)", which is not simplified, as b = true happened "later". *)
    Abort.

    Lemma valid_unit_contract1_with_replay : ValidContract unit_contract1 (FunDef unit_example).
    Proof.
      now compute. (* Replay, we get a trivial VC *)
    Qed.

    Lemma valid_unit_contract2_no_replay : ValidContractWithoutReplay unit_contract2 (FunDef unit_example).
    Proof.
      compute.
      constructor. (* No replay, but the ordering of the conjuncts in the precondition ensures A will get simplified too (by putting B first!) *)
      now cbn.
    Qed.

    Lemma valid_unit_contract3_no_replay : ValidContractWithoutReplay unit_contract3 (FunDef unit_example).
    Proof.
      compute.
      constructor. (* Same issue as in valid_unit_contract1_no_replay *)
    Abort.

    Lemma valid_unit_contract3_with_replay : ValidContract unit_contract3 (FunDef unit_example).
    Proof.
      now compute. (* Replay, gives us a trivial VC *)
    Qed.

    Lemma valid_unit_contract_int_no_replay : ValidContractWithoutReplay unit_contract_int (FunDef unit_example).
    Proof.
      compute.
      (* No replay, we see that we have an assume: 5 = a + 0, which didn't get
         simplified, and we need to prove that: a = 5 *)
      constructor.
      cbn.
    Abort.

    Lemma valid_unit_contract_int_with_replay : ValidContract unit_contract_int (FunDef unit_example).
    Proof.
      now compute. (* Replay, gives us a trivial VC *)
    Qed.
  End UnitExample.
End ReplayExamples.

