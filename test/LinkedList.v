(******************************************************************************)
(* Copyright (c) 2021 Steven Keuchel                                          *)
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

(* This file contains a toy example verifying the correctness of simple
   functions operating on singly-linked lists. It is essentially based on the
   definitions of linked list first defined in

     John C. Reynolds. 2000.
     Intuitionistic reasoning about shared mutable data structure.

   We instantiate the framework to get a symbolic verification condition
   generator and also instantiate the Iris model with a suitable definition of
   memory.
  *)

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
     Iris.Instance
     Iris.Base
     Notations
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

From stdpp Require Import decidable finite list fin_maps infinite.
From iris.proofmode Require string_ident proofmode.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Local Open Scope string_scope.

(* We use this notation in every place an int represents a memory address.
   Unfortunately, this Notation is also used for integers that are not
   addreses. *)
Abbreviation ptr   := ty.int.
Abbreviation llist := (ty.option ptr).

Module Import ExampleBase <: Base.

  (* We use default instances because this example does not use any types other
     than the standard ones already available. *)
  #[export] Instance typedeclkit : TypeDeclKit := DefaultTypeDeclKit.
  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit := DefaultTypeDenoteKit.
  #[export] Instance typedefkit : TypeDefKit typedenotekit := DefaultTypeDefKit.
  #[export] Instance varkit : VarKit := DefaultVarKit.

  Include BaseMixin.
End ExampleBase.

Module Import ExampleGlobalState <: GlobalState.
  Module BASE := ExampleBase.

  Section MemoryModel.
    (* The type of memory we use for this example. A mapping from addresses
       represented as integers to pairs. *)
    Definition Memory : Set := gmap.gmap Z (Z * (Z + unit)).
  End MemoryModel.

  (* We don't make any use of registers (global variables). *)
  Include DefaultRegDeclKit BASE.

End ExampleGlobalState.


(* The [Program] module contains the declaration and definition of the functions
   that make up the program. *)
Module Import ExampleProgram <: Program ExampleGlobalState.

  Section FunDeclKit.
    (* We define the signatures of μSail functions. Their bodies are defined
       later.*)
    Inductive Fun : PCtx -> Ty -> Set :=
    | append      : Fun [ "p" ∷ llist; "q" ∷ llist ] llist
    | appendloop  : Fun [ "p" ∷ ptr; "q" ∷ llist ] ty.unit
    | length      : Fun [ "p" ∷ llist ] ty.int
    | copy        : Fun [ "p" ∷ llist ] llist
    | reverse     : Fun [ "p" ∷ llist ] llist
    | reverseloop : Fun [ "p" ∷ llist; "q" ∷ llist ] llist
    .

    (* These are foreign functions that will be implemented in Coq. They should
       be considered to be primitives provided by a runtime system. *)
    Inductive FunX : PCtx -> Ty -> Set :=
    | mkcons : FunX [ "x" ∷ ty.int; "xs" ∷ llist ] ptr
    | fst    : FunX [ "p" ∷ ptr ] ty.int
    | snd    : FunX [ "p" ∷ ptr ] llist
    | setfst : FunX [ "p" ∷ ptr; "x" ∷ ty.int ] ty.unit
    | setsnd : FunX [ "p" ∷ ptr; "xs" ∷ llist ] ty.unit
    .

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := FunX.

    (* The ghost lemmas for opening and closing the recursive linked list
       predicate ptstolist. This predicate is defined later in this file, but
       since the ghost lemmas are used in statements, their signatures are
       already defined here. *)
    Inductive Lem : PCtx -> Set :=
    | open_nil      : Lem [ ]
    | open_cons     : Lem [ "p" ∷ ptr ]
    | close_nil     : Lem [ "p" ∷ ty.unit ]
    | close_cons    : Lem [ "p" ∷ ptr ].

    Definition 𝑳 : PCtx -> Set := Lem.
  End FunDeclKit.

  (* A mixin provided by the library pulling in definitions of statements etc.
     which rely on the declared functions and ghost lemmas. *)
  Include FunDeclMixin ExampleGlobalState.

  Section FunDefKit.

    Local Coercion stm_exp : Exp >-> Stm.

    Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
    Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
    Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.

    Notation "'lemma' f args" := (stm_lemma f args%env) (at level 10, f at next level) : exp_scope.

    (* The append function, taking two linked lists [p],[q] and appending [q] to
       [p] by destructively updating the last heap-allocated pair. Both lists
       are allowed to be empty. *)
    Definition fun_append : Stm [ "p" ∷ llist; "q" ∷ llist ] llist :=
      match: exp_var "p" with
      | inl "x" =>
        call appendloop (exp_var "x") (exp_var "q") ;;
        exp_var "p"
      | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        exp_var "q"
      end.

    (* The loop that recurses to the last pair. The first argument needs to be a
       valid address pointing to a pair, i.e. it represents a non-empty linked
       list. *)
    Definition fun_appendloop : Stm [ "p" ∷ ptr; "q" ∷ llist ] ty.unit :=
      lemma open_cons [exp_var "p"] ;;
      let: "mbn" := foreign snd (exp_var "p") in
      match: (exp_var "mbn") with
      | inl "x" => call appendloop (exp_var "x") (exp_var "q")
      | inr "tt" =>
          lemma close_nil [exp_var "tt"] ;;
          (* Do the destructive update. *)
          foreign setsnd (exp_var "p") (exp_var "q")
      end;;
      lemma close_cons [exp_var "p"].

    (* An example with the first lemma call removed. The intention is to demonstrate
       the error reporting capabilities of the library. *)
    Definition fun_appendloop_broken : Stm [ "p" ∷ ptr; "q" ∷ llist ] ty.unit :=
      (* lemma open_cons [exp_var "p"] ;; *)
      let: "mbn" := foreign snd (exp_var "p") in
      match: (exp_var "mbn") with
      | inl "x" => call appendloop (exp_var "x") (exp_var "q")
      | inr "tt" =>
          lemma close_nil [exp_var "tt"] ;;
          foreign setsnd (exp_var "p") (exp_var "q")
      end;;
      lemma close_cons [exp_var "p"].

    (* A recursive function calculating the length of a heap-allocated list. *)
    Definition fun_length : Stm [ "p" ∷ llist ] ty.int :=
      match: exp_var "p" with
      | inl "x" =>
        lemma open_cons [exp_var "x"] ;;
        let: "t" := foreign snd (exp_var "x") in
        let: "r" := call length (exp_var "t") in
        lemma close_cons [exp_var "x"] ;;
        exp_binop bop.plus (exp_val ty.int 1%Z) (exp_var "r")
      | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        lemma open_nil [] ;;
        stm_val ty.int 0%Z
      end.

    (* Make a deep copy of a linked list, i.e. allocate new pairs that hold
       the same elements in the same order as the given list. *)
    Definition fun_copy : Stm [ "p" ∷ llist ] llist :=
      match: exp_var "p" with
      | inl "x" =>
        lemma open_cons [exp_var "x"] ;;
        let: "h"  := foreign fst (exp_var "x") in
        let: "t"  := foreign snd (exp_var "x") in
        let: "t'" := call copy (exp_var "t") in
        let: "x'" := foreign mkcons (exp_var "h") (exp_var "t'") in
        lemma close_cons [exp_var "x"] ;;
        lemma close_cons [exp_var "x'"] ;;
        exp_inl (exp_var "x'")
      | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        lemma open_nil [] ;;
        lemma open_nil [] ;;
        exp_val llist (inr tt)
      end.

    (* In-place reversing of a linked list. This changes the order of all
       pointers in the list, destructively updating the given list. *)
    Definition fun_reverse : Stm [ "p" ∷ llist ] llist :=
      lemma open_nil [] ;;
      call reverseloop (exp_var "p") (exp_val llist (inr tt)).

    (* The loop for the reversal with an accumulator [q]. This reverses [p]
       and appends [q] to that result. *)
    Definition fun_reverseloop : Stm [ "p" ∷ llist; "q" ∷ llist ] llist :=
      match: exp_var "p" with
      | inl "x" =>
        lemma open_cons [exp_var "x"] ;;
        let: "n"  := foreign snd (exp_var "x") in
        foreign setsnd (exp_var "x") (exp_var "q");;
        lemma close_cons [exp_var "x"] ;;
        call reverseloop (exp_var "n") (exp_inl (exp_var "x"))
      | inr "tt" =>
        lemma close_nil [exp_var "tt"] ;;
        exp_var "q"
      end.

    (* Combine all the separately-defined function bodies into a single map from
       function names to their bodies. *)
    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | append     => fun_append
      | appendloop => fun_appendloop
      | length     => fun_length
      | copy       => fun_copy
      | reverse     => fun_reverse
      | reverseloop => fun_reverseloop
      end.

  End FunDefKit.

  (* We pull in the default implementation of a store for registers. *)
  Include DefaultRegStoreKit ExampleGlobalState.

  (* In this section we define the foreign functions. *)
  Section ForeignKit.

    Import iris.proofmode.proofmode.

    (* This defines a "stepping relation" for the foreign functions. Since all
       these functions are deterministic, we write them in a functional instead
       of a relational style. *)
    Equations(noeqns) ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs)
      (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop :=
      (* mkcons allocates a new pair and initializes it with the given values
         [x] and [xs]*)
      ForeignCall mkcons (env.snoc (env.snoc env.nil _ x) _ xs) res γ γ' μ μ' :=
        (* Determinate the next free address. *)
        let next := infinite_fresh (elements (dom μ)) in
        γ' = γ /\
        (* Allocate the pair at [next]. *)
        μ' = (<[next := (x, xs)]> μ) /\
        res = inr next;
      ForeignCall fst (env.snoc env.nil _ z) res γ γ' μ μ' :=
        match μ !! z with
        | None          => res = inl "Invalid pointer"
        | Some (head,_) => γ' = γ /\ μ' = μ /\ res = inr head
        end;
      ForeignCall snd (env.snoc env.nil _ z) res γ γ' μ μ' :=
        match μ !! z with
        | None          => res = inl "Invalid pointer"
        | Some (_,next) => γ' = γ /\ μ' = μ /\ res = inr next
        end;
      ForeignCall setfst (env.snoc (env.snoc env.nil _ z) _ x) res γ γ' μ μ' :=
        match (μ !! z) with
        | None => res = inl "Invalid pointer"
        | Some (_, xs) => γ' = γ /\  μ' = <[z := (x, xs)]> μ /\ res = inr tt
        end;
      ForeignCall setsnd (env.snoc (env.snoc env.nil _ z) _ xs) res γ γ' μ μ' :=
        match (μ !! z) with
        | None => res = inl "Invalid pointer"
        | Some (elem, _) => γ' = γ /\  μ' = <[z := (elem, xs)]> μ /\ res = inr tt
        end.

    (* Show the progress of the foreign function stepping relation. *)
    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof.
      destruct f; env.destroy args; cbn;
        try match goal with
            | |- context[match ?disc with _ => _ end] =>
                lazymatch disc with
                (* Destruct the lookup first before creating the evars using eexists. *)
                | lookup _ _ => destruct disc as [[elem next]|] eqn:?
                end
            end;
        repeat
          lazymatch goal with
          | |- _ = _ => reflexivity
          | |- _ /\ _ => split
          | |- exists _, _ => eexists
          end; auto.
    Qed.

  End ForeignKit.

  Include ProgramMixin ExampleGlobalState.

  Import callgraph.

  Lemma fundef_bindfree (Δ : PCtx) (τ : Ty) (f : Fun Δ τ) :
    stm_bindfree (FunDef f).
  Proof. destruct f; now vm_compute. Qed.

  Definition 𝑭_call_graph := generic_call_graph.
  Lemma 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.
  Proof. apply generic_call_graph_wellformed, fundef_bindfree. Qed.

  Definition 𝑭_accessible {Δ τ} (f : 𝑭 Δ τ) : option (Accessible 𝑭_call_graph f) :=
    None.

End ExampleProgram.

(* These are user-defined pure predicates that we use to encode the functional
   correctness of some of the linked list functions that are otherwise not
   encodable in the assertion language. The assertion language has a primitive
   list append, but no operators for the other functions. *)
Inductive PurePredicate : Set :=
| plength
| preverse
| preverseappend
.

(* The following datatype defines the spatial predicates that are used in the
   example. *)
Inductive Predicate : Set :=
| ptstocons (* A points-to predicate for a single heap allocated pair. *)
| ptstolist (* A points-to predicate for a heap allocated linked list. *)
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

(* The program logic signature contains all the necessary definitions
   pertaining to user-defined pure and spatial predicates. These definitions
   are enough to instantiate the assertion language for pre- and
   postconditions used in function contracts. *)
Module Import ExampleSignature <: Signature ExampleGlobalState.
  Import ExampleBase.

  Definition 𝑷 := PurePredicate.
  (* Maps each pure predicate to a list of arguments with their types. *)
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | plength => [ty.list ty.int; ty.int]
    | preverse => [ty.list ty.int; ty.list ty.int]
    | preverseappend => [ty.list ty.int; ty.list ty.int; ty.list ty.int]
    end.
  (* Interprets a pure predicate name as a Coq proposition. *)
  Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
    match p with
    | plength => fun xs l => Z.of_nat (Datatypes.length xs) = l
    | preverse => fun xs ys => ys = rev xs
    | preverseappend => fun xs ys zs => zs = rev_append xs ys
    end.

  #[export] Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

  Section HeapPredicateDeclKit.

    Definition 𝑯 := Predicate.
  (* Maps each spatial predicate to a list of arguments with their types. *)
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | ptstocons => [ptr; ty.int; llist]
      | ptstolist => [llist; ty.list ty.int]
      end.
    #[export] Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

    (* None of the predicates is duplicable. *)
    #[export] Instance 𝑯_is_dup : IsDuplicable 𝑯 :=
      {| is_duplicable p := false |}.

    #[local] Arguments Some {_} &.
    (* Defines precieness for both predicates. The address forms the input
       in both cases and the pointed-to values are the outputs. *)
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | ptstocons => Some (MkPrecise [ptr] [ptr; llist] eq_refl)
      | ptstolist => Some (MkPrecise [llist] [ty.list ptr] eq_refl)
      end.

  End HeapPredicateDeclKit.

  (* A mixin that defines Formulas, Chunks and assertions to write contract and
     that defines Worlds and symbolic propositions for the executor. *)
  Include PredicateMixin ExampleGlobalState.
  Include WorldsMixin ExampleGlobalState.

  (* The SolverKit module is the user-defined part of the solver that is linked
     with a generic part in MakeSolver. Here we can automatically simplify or
     solve the user-defined predicate case of formulas. We also prove
     correctness by showing that all runs of the simplifier produce unsolved
     residual formulas (that are hopefully simpler) that are equivalent to the
     input. *)
  Section ExampleSolverKit.
    #[local] Arguments Some {_} _%_ctx.
    #[local] Unset Implicit Arguments.
    #[local] Set Equations Transparent.

    (* Simplification of the [plength] predicate with arguments [xs] and [n]. *)
    Equations simplify_plength {Σ} (xs : Term Σ (ty.list ty.int)) (n : Term Σ ty.int) : Option PathCondition Σ :=
    | term_binop bop.cons x xs       | term_binop bop.plus (term_val ?(ty.int) 1%Z) n => Some [formula_user plength [xs;n]]
    | term_binop bop.cons x xs       | term_binop bop.plus n (term_val ?(ty.int) 1%Z) => Some [formula_user plength [xs;n]]
    | term_val ?(ty.list ty.int) nil | term_val ?(ty.int) 0%Z                         => Some []
    | xs                             | n                                              => Some [formula_user plength [xs;n]].

    (* Simplification of the [preverseappend] predicate with arguments [xs], [ys],
     and [zs]. *)
    Equations simplify_preverseappend {Σ} (xs ys zs: Term Σ (ty.list ty.int)) : Option PathCondition Σ :=
    (* | term_binop binop_cons x xs | term_binop binop_plus (term_val ?(ty.int) 1%Z) n := *)
    (*   Some [formula_user plength (env.nil ► (_ ↦ xs) ► (ty.int ↦ n))]%list; *)
    | term_val ?(ty.list ty.int) nil | ys | zs => Some [formula_relop bop.eq ys zs]
    | xs | term_val ?(ty.list ty.int) nil | zs => Some [formula_user preverse [xs;zs]]
    | term_binop bop.cons x xs | ys       | zs => Some [formula_user preverseappend [xs; term_binop bop.cons x ys; zs]]
    | xs | ys | zs                             => Some [formula_user preverseappend [xs;ys;zs]].

    Import Entailment.

    Local Ltac lsolve := repeat Entailment.tactics.mixin; try easy; auto.

    (* Prove that the simplifier of [plength] is sound and complete. *)
    Goal True. idtac "Timing before: llist/simplify_plength_spec". Abort.
    Lemma simplify_plength_spec {Σ} (xs : Term Σ (ty.list ty.int)) (n : Term Σ ty.int) :
      simplify_plength xs n ⊣⊢ Some [formula_user plength [xs;n]].
    Proof.
      pattern (simplify_plength xs n).
      apply_funelim (simplify_plength xs n); intros *; lsolve;
        intro ι; cbn; lia.
    Qed.
    Goal True. idtac "Timing after: llist/simplify_plength_spec". Abort.

    (* Prove that the simplifier of [preverseappend] is sound and complete. *)
    Goal True. idtac "Timing before: llist/simplify_preverseappend_spec". Abort.
    Lemma simplify_preverseappend_spec {Σ} (xs ys zs : Term Σ (ty.list ty.int)) :
      simplify_preverseappend xs ys zs ⊣⊢ Some [formula_user preverseappend [xs;ys;zs]].
    Proof.
      pattern (simplify_preverseappend xs ys zs).
      apply_funelim (simplify_preverseappend xs ys zs); intros *; lsolve;
        intro ι; cbn; first [now rewrite rev_alt|now rewrite rev_append_rev ].
    Qed.
    Goal True. idtac "Timing after: llist/simplify_preverseappend_spec". Abort.

    (* Combined the solvers to a solver for the [formula_user] case. *)
    Definition solve_user : SolverUserOnly :=
      fun Σ p =>
        match p with
        | plength => fun ts =>
                       let (ts,n)  := env.view ts in
                       let (ts,xs) := env.view ts in
                       simplify_plength xs n
        | preverse => fun ts => Some [formula_user preverse ts]
        | preverseappend =>
            fun ts =>
              let (ts,zs) := env.view ts in
              let (ts,ys) := env.view ts in
              let (ts,xs) := env.view ts in
              simplify_preverseappend xs ys zs
        end.

    (* Combine the correctness proofs. *)
    Lemma solve_user_spec : SolverUserOnlySpec solve_user.
    Proof.
      intros Σ p ts.
      destruct p; cbv in ts; env.destroy ts.
      - apply simplify_plength_spec.
      - reflexivity.
      - apply simplify_preverseappend_spec.
    Qed.

    (* Lift the solver for the [formula_user] case to a solver over any set
       of formulas. *)
    Definition solver : Solver :=
      solveruseronly_to_solver solve_user.
    Lemma solver_spec : SolverSpec solver.
    Proof.
      apply solveruseronly_to_solver_spec, solve_user_spec.
    Qed.

  End ExampleSolverKit.

  Include SignatureMixin ExampleGlobalState.
End ExampleSignature.

Module Import ExampleProgramLogic :=
  MakeProgramLogic ExampleGlobalState ExampleSignature ExampleProgram.

(* The specification module contains the contracts for all μSail and foreign functions. *)
Module Import ExampleSpecification.

  Section ContractDefKit.

    Import ctx.resolution.
    Import asn.notations.

    (* We define notations for more convenience. *)
    Local Notation "p '↦l' xs" := (asn.chunk (chunk_user ptstolist (env.nil ► (llist ↦ p) ► (ty.list ty.int ↦ xs)))) (at level 70).
    Local Notation "p '↦p' ( x , xs )" := (asn.chunk (chunk_user ptstocons (env.nil ► (ptr ↦ p) ► (ty.int ↦ x) ► (llist ↦ xs)))) (at level 70).

    Arguments formula_prop [Σ] Σ' ζ _.

    Definition asn_append {Σ : LCtx} (xs ys zs : Term Σ (ty.list ty.int)) : Assertion Σ :=
      term_binop bop.append xs ys = zs.

    Definition sep_contract_append : SepContract [ "p" ∷ llist; "q" ∷ llist ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "q" ∷ llist; "xs" ∷ ty.list ty.int; "ys" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"; term_var "q"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs" ∗ term_var "q" ↦l term_var "ys";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn.exist "zs" (ty.list ty.int)
             (term_var "result" ↦l term_var "zs" ∗
              asn_append (term_var "xs") (term_var "ys") (term_var "zs"));
      |}.

    Definition sep_contract_appendloop : SepContract [ "p" ∷ ptr; "q" ∷ llist ] ty.unit :=
      {| sep_contract_logic_variables := ["p" ∷ ptr; "q" ∷ llist; "xs" ∷ ty.list ty.int; "ys" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"; term_var "q"];
         sep_contract_precondition    := term_inl (term_var "p") ↦l term_var "xs" ∗ term_var "q" ↦l term_var "ys";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           term_var "result" = term_val ty.unit tt ∗
           asn.exist "zs" (ty.list ty.int)
             (term_inl (term_var "p") ↦l term_var "zs" ∗
              asn_append (term_var "xs") (term_var "ys") (term_var "zs"));
      |}.

    Definition sep_contract_length : SepContract [ "p" ∷ llist ] ty.int :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "xs" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn.formula (formula_user plength [term_var "xs"; term_var "result"]) ∗
           term_var "p" ↦l term_var "xs"
      |}.

    Definition sep_contract_copy : SepContract [ "p" ∷ llist ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "xs" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           term_var "p" ↦l term_var "xs" ∗
           term_var "result" ↦l term_var "xs"
      |}.

    Definition sep_contract_reverse : SepContract [ "p" ∷ llist ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "xs" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs";
         sep_contract_result          := "r";
         sep_contract_postcondition   :=
           asn.exist "zs" (ty.list ty.int)
             (term_var "r" ↦l term_var "zs" ∗
              asn.formula (formula_user preverse [term_var "xs"; term_var "zs"]));
      |}.

    Definition sep_contract_reverseloop : SepContract [ "p" ∷ llist; "q" ∷ llist ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ llist; "q" ∷ llist; "xs" ∷ ty.list ty.int; "ys" ∷ ty.list ty.int];
         sep_contract_localstore      := [term_var "p"; term_var "q"];
         sep_contract_precondition    := term_var "p" ↦l term_var "xs" ∗ term_var "q" ↦l term_var "ys";
         sep_contract_result          := "r";
         sep_contract_postcondition   :=
           asn.exist "zs" (ty.list ty.int)
             (term_var "r" ↦l term_var "zs" ∗
              asn.formula (formula_user preverseappend [term_var "xs"; term_var "ys"; term_var "zs"]));
      |}.

    Definition sep_contract_mkcons : SepContract [ "x" ∷ ty.int; "xs" ∷ llist ] ptr :=
      {| sep_contract_logic_variables := ["x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "x"; term_var "xs"];
         sep_contract_precondition    := ⊤;
         sep_contract_result          := "p";
         sep_contract_postcondition   := term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_fst : SepContract [ "p" ∷ ptr ] ty.int :=
      {| sep_contract_logic_variables := ["p" ∷ ty.int; "x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦p ( term_var "x" , term_var "xs" );
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           term_var "result" = term_var "x" ∗
           term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_snd : SepContract [ "p" ∷ ptr ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ ty.int; "x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p"];
         sep_contract_precondition    := term_var "p" ↦p ( term_var "x" , term_var "xs" );
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           term_var "result" = term_var "xs" ∗
           term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_setfst : SepContract [ "p" ∷ ptr; "x" ∷ ty.int ] ty.unit :=
      {| sep_contract_logic_variables := ["p" ∷ ty.int; "x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p"; term_var "x"];
         sep_contract_precondition    := asn.exist "y" ty.int (term_var "p" ↦p ( term_var "y" , term_var "xs"));
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
         term_var "result" = term_val ty.unit tt ∗
         term_var "p" ↦p ( term_var "x" , term_var "xs");
      |}.

    Definition sep_contract_setsnd : SepContract [ "p" ∷ ptr; "xs" ∷ llist ] ty.unit :=
      {| sep_contract_logic_variables := ["p" ∷ ty.int; "x" ∷ ty.int; "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p"; term_var "xs"];
         sep_contract_precondition    := asn.exist "ys" llist (term_var "p" ↦p ( term_var "x" , term_var "ys"));
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
         term_var "result" = term_val ty.unit tt ∗
         term_var "p" ↦p ( term_var "x" , term_var "xs");
      |}.

    Definition sep_lemma_open_nil : Lemma [ ] :=
      {| lemma_logic_variables := [];
         lemma_patterns        := [];
         lemma_precondition    := ⊤;
         lemma_postcondition   := term_val llist (inr tt) ↦l term_val (ty.list ty.int) nil;
      |}.

    Definition sep_lemma_open_cons : Lemma [ "p" ∷ ptr ] :=
      {| lemma_logic_variables := ["p" ∷ ty.int; "xs" ∷ ty.list ty.int];
         lemma_patterns        := [term_var "p"];
         lemma_precondition    := term_inl (term_var "p") ↦l term_var "xs";
         lemma_postcondition   :=
           asn.match_list (term_var "xs")
             ⊥
             "y" "ys"
             (asn.exist "n" llist
                (term_var "p" ↦p (term_var "y", term_var "n") ∗
                term_var "n" ↦l term_var "ys"))
      |}.

    Definition sep_lemma_close_cons : Lemma [ "p" ∷ ptr ] :=
      {| lemma_logic_variables := ["p" ∷ ptr; "x" ∷ ty.int; "xs" ∷ ty.list ty.int; "n" ∷ llist ];
         lemma_patterns        := [term_var "p"];
         lemma_precondition    := term_var "p" ↦p (term_var "x" , term_var "n") ∗
                                  term_var "n" ↦l term_var "xs";
         lemma_postcondition   := term_inl (term_var "p") ↦l term_binop bop.cons (term_var "x") (term_var "xs")
      |}.

    Definition sep_lemma_close_nil : Lemma [ "p" ∷ ty.unit ] :=
      {| lemma_logic_variables := ["p" ∷ ty.unit; "xs" ∷ ty.list ty.int ];
         lemma_patterns        := [term_var "p"];
         lemma_precondition    := term_inr (term_var "p") ↦l term_var "xs";
         lemma_postcondition   :=
           term_var "p"  = term_val ty.unit tt ∗
           term_var "xs" = term_val (ty.list ty.int) nil
      |}.



    (* The following maps μSail function names to their contracts. *)
    Definition contract_environment : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | append     => Some (sep_contract_append)
        | appendloop => Some (sep_contract_appendloop)
        | length     => Some (sep_contract_length)
        | copy       => Some (sep_contract_copy)
        | reverse    => Some (sep_contract_reverse)
        | reverseloop => Some (sep_contract_reverseloop)
        end.

    (* And this definition maps foreign functions to their contracts. *)
    Definition contract_environment_foreign : SepContractEnvEx :=
      fun Δ τ f =>
        match f with
        | mkcons => sep_contract_mkcons
        | fst => sep_contract_fst
        | snd => sep_contract_snd
        | setfst => sep_contract_setfst
        | setsnd => sep_contract_setsnd
        end.

    (* And finally a mapping from ghost lemmas to the entailments they encode. *)
    Definition lemma_environment : LemmaEnv :=
      fun Δ l =>
        match l with
        | open_nil => sep_lemma_open_nil
        | open_cons => sep_lemma_open_cons
        | close_cons => sep_lemma_close_cons
        | close_nil => sep_lemma_close_nil
        end.

  End ContractDefKit.

  #[export] Instance example_specification : Specification :=
    {| CEnv   := contract_environment;
       CEnvEx := contract_environment_foreign;
       LEnv   := lemma_environment;
       fail_rule_pre := true;
    |}.

End ExampleSpecification.


(* Use the specification and the solver module to compose the symbolic executor
   and symbolic verification condition generator. *)
Module Import ExampleExecutor :=
  MakeExecutor ExampleGlobalState ExampleSignature ExampleProgram ExampleProgramLogic.

Section DebugExample.
  Import SymProp.notations.
  Notation "x '∷' σ . P" := (@amsg.there _ (x ∷ σ) P)
    (at level 49, P at level 200, right associativity, only printing,
       format "x '∷' σ .  '/' P").
  Notation "'error' x" := (SymProp.error x) (at level 200, only printing, format "'error'  x").
  Notation "P" := (amsg.mk P) (only printing).
  Import ListNotations.

  Lemma debug_appendloop_broken : Symbolic.ValidContract sep_contract_appendloop fun_appendloop_broken.
  Proof.
    compute.
    idtac "Verification condition with failure:".
    match goal with |- VerificationCondition ?x => idtac x end.
  Abort.

End DebugExample.

(* In this section we use the symbolic VCG to verify the contracts of all the
   μSail functions. In this case, the automation provided by the user-defined
   and generic solvers, and the explicit ghost lemma invocations in the function
   definition provide enough instructions to solve the verification conditions
   fully automatically. We therefore use the reflective version of the VCGs
   [ValidContractReflect] and prove each VC by reflexivity. *)
Section ContractVerification.

  Goal True. idtac "Timing before: llist/valid_contract_append". Abort.
  Lemma valid_contract_append : Symbolic.ValidContractReflect sep_contract_append fun_append.
  Proof. now vm_compute. Qed.
  Goal True. idtac "Timing after: llist/valid_contract_append". Abort.

  Goal True. idtac "Timing before: llist/valid_contract_appendloop". Abort.
  Lemma valid_contract_appendloop : Symbolic.ValidContractReflect sep_contract_appendloop fun_appendloop.
  Proof. now vm_compute. Qed.
  Goal True. idtac "Timing after: llist/valid_contract_appendloop". Abort.

  Goal True. idtac "Timing before: llist/valid_contract_length". Abort.
  Lemma valid_contract_length : Symbolic.ValidContractReflect sep_contract_length fun_length.
  Proof. now vm_compute. Qed.
  Goal True. idtac "Timing after: llist/valid_contract_length". Abort.

  Goal True. idtac "Timing before: llist/valid_contract_copy". Abort.
  Lemma valid_contract_copy : Symbolic.ValidContractReflect sep_contract_copy fun_copy.
  Proof. now vm_compute. Qed.
  Goal True. idtac "Timing after: llist/valid_contract_copy". Abort.

  Goal True. idtac "Timing before: llist/valid_contract_reverse". Abort.
  Lemma valid_contract_reverse : Symbolic.ValidContractReflect sep_contract_reverse fun_reverse.
  Proof. now vm_compute. Qed.
  Goal True. idtac "Timing after: llist/valid_contract_reverse". Abort.

  Goal True. idtac "Timing before: llist/valid_contract_reverseloop". Abort.
  Lemma valid_contract_reverseloop : Symbolic.ValidContractReflect sep_contract_reverseloop fun_reverseloop.
  Proof. now vm_compute. Qed.
  Goal True. idtac "Timing after: llist/valid_contract_reverseloop". Abort.

End ContractVerification.

(* Also instantiate the shallow executor for the soundness proofs and the
   statistics. *)
Module Import ExampleShalExec :=
  MakeShallowExecutor ExampleGlobalState ExampleSignature ExampleProgram ExampleProgramLogic.

(* Instantiate the operational semantics which is an input to the Iris model. *)
Module ExampleSemantics <: Semantics ExampleGlobalState ExampleProgram :=
  MakeSemantics ExampleGlobalState ExampleProgram.

(* This module contains the instantiation of the Iris model. It contains the
   definition of several user-defined modules that are inputs to the generic
   module functors defined in the library. *)
Module ExampleModel.

  Import ExampleProgram.
  Import ExampleSpecification.

  (* The construction of the model is split up into several steps. First, the
     [IrisBase] defines the operational model that only depends on the program
     and the operational semantics, but not the signature or defined function
     contracts. *)
  (* Instantiates with the step relation and sets up the ghost state for
     registers. *)
  Module Import ExampleIrisPrelims <: IrisPrelims ExampleGlobalState ExampleProgram ExampleSemantics.
    Include IrisPrelims ExampleGlobalState ExampleProgram ExampleSemantics.
  End ExampleIrisPrelims.

  Module Import ExampleIrisBase <: IrisBase ExampleGlobalState ExampleProgram ExampleSemantics ExampleIrisPrelims.

    (* The [IrisParameters] define the ghost state for memory which is provided
       by the user. This is then combined with the ghost state for registers in
       the [IrisResources] mixin below. *)
    Section ExampleIrisParameters.
      Import iris.bi.interface.
      Import iris.bi.big_op.
      Import iris.base_logic.lib.iprop.
      Import iris.base_logic.lib.gen_heap.
      Import iris.proofmode.proofmode.

      Class mcMemGS Σ :=
        McMemGS {
            (* ghost variable for tracking the memory state. *)
            mc_ghGS : gen_heapGS Z (Z * (Z + unit)) Σ;
            mc_invNs : namespace
          }.
      #[export] Existing Instance mc_ghGS.

      Definition memGS : gFunctors -> Set := mcMemGS.

      Lemma fst_pair_id2 : forall {A} {B},
          (λ (x : A) (y : B), (Datatypes.fst ∘ pair x) y) = (λ (x : A) (y : B), x).
      Proof.
        intros; now vm_compute.
      Qed.

      Lemma imap_pair_fst_seq {A} (l : list A) :
        (imap pair l).*1 = seq 0 (length l).
      Proof.
        rewrite fmap_imap.
        rewrite fst_pair_id2.
        rewrite imap_seq_0.
        rewrite list_fmap_id; now vm_compute.
      Qed.

      Definition mem_state_interp : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} hG μ => (gen_heap_interp (hG := mc_ghGS (mcMemGS := hG)) μ)%I.
    End ExampleIrisParameters.

    Include IrisResources ExampleGlobalState ExampleProgram ExampleSemantics ExampleIrisPrelims.
    Include IrisWeakestPre ExampleGlobalState ExampleProgram ExampleSemantics ExampleIrisPrelims.
    Include IrisTotalWeakestPre ExampleGlobalState ExampleProgram ExampleSemantics ExampleIrisPrelims.
    Include IrisTotalPartialWeakestPre ExampleGlobalState ExampleProgram ExampleSemantics ExampleIrisPrelims.

  End ExampleIrisBase.

  Module ExampleIrisAdeqParams <: IrisAdeqParameters ExampleGlobalState ExampleIrisBase.
    Import iris.base_logic.lib.gen_heap.
    Import iris.proofmode.proofmode.

    Definition memGpreS : gFunctors -> Set := fun Σ => gen_heapGpreS Z (Z * (Z + unit)) Σ.
    Definition memΣ : gFunctors := gen_heapΣ Z (Z * (Z + unit)).

    Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
      fun {Σ} => subG_gen_heapGpreS (Σ := Σ) (L := Z) (V := (Z * (Z + unit))).

    Definition mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ => ([∗ map] l↦v ∈ μ, pointsto (hG := mc_ghGS (mcMemGS := hG)) l (DfracOwn 1) v)%I.

    Lemma mem_init `{! gen_heapGpreS Z (Z * (Z + unit)) Σ} (μ : Memory) :
      ⊢ |==> ∃ mG : memGS Σ, (mem_state_interp mG μ ∗ mem_res mG μ)%I.
    Proof.
      iMod (gen_heap_init (L := Z) (V := (Z * (Z + unit))) empty) as (gH) "[inv _]".

      iMod (gen_heap_alloc_big empty μ (map_disjoint_empty_r μ) with "inv") as "(inv & res & _)".
      iModIntro.
      rewrite (right_id empty union μ).

      iExists (McMemGS gH (nroot .@ "mem_state_interp")).
      iFrame.
    Qed.
  End ExampleIrisAdeqParams.

  (* After instantiating [IrisBase] we have access to the Iris base logic
     with the given ghost state and can interpret the user-defined predicates in
     this logic. This is then provided to the library as part of the
     [IrisInstance] module. *)
  Module Import ExampleIrisInstance <:
    IrisInstance ExampleGlobalState ExampleSignature ExampleProgram ExampleSemantics
      ExampleProgramLogic ExampleIrisPrelims ExampleIrisBase.

    Import iris.base_logic.lib.gen_heap.
    Import iris.base_logic.lib.iprop.
    Import iris.bi.big_op.
    Import iris.bi.interface.
    Import iris.proofmode.proofmode.

    (* This is the interpretation of the points to pair predicate in Iris. *)
    Definition ptstocons_interp `{mG : mcMemGS Σ} (p : Z) (v : Z) (n : Z + unit) : iProp Σ :=
      (pointsto p (DfracOwn 1) (pair v n))%I.

    (* This is the recursive definition of the points to list predicate in Iris. *)
    Fixpoint ptstolist_interp `{mG : mcMemGS Σ} (p : Z + unit) (vs : list Z) : iProp Σ :=
      match vs with
      | nil => ⌜p = inr tt⌝
      | v :: vs => (∃ p' pn, ⌜p = inl p'⌝ ∗ ptstocons_interp p' v pn ∗ ptstolist_interp pn vs)%I
      end.

    (* We don't need additional ghost state beyond what we already have for the WP.*)
    Definition resGS := trivGS.

    (* Pattern match on the generic representation of abstract predicates map them
       to their Iris definition. *)
    Definition luser_inst `{sRG : sailRegGS Σ} `{fancy_updates.invGS Σ} {mG : mcMemGS Σ} {_ : trivGS Σ} (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
      (match p return Env Val (𝑯_Ty p) -> iProp Σ with
      | ptstocons => fun ts => ptstocons_interp (env.head (env.tail (env.tail ts))) (env.head (env.tail ts)) (env.head ts)
      | ptstolist => fun ts => ptstolist_interp (env.head (env.tail ts)) (env.head ts)
       end) ts.

    (* This definition verifies the soundness if duplicability. However, this
       example does not contain any predicates marked as duplicable and therefore
       the proof is trivial *)
    Definition lduplicate_inst `{sRG : sailRegGS Σ} `{fancy_updates.invGS Σ} {mG : mcMemGS Σ} {_ : trivGS Σ} :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true -> luser_inst p ts ⊢ luser_inst p ts ∗ luser_inst p ts.
    Proof.
      destruct p; now cbn.
    Qed.

    (* At this point we have enough information to instantiate the program logic
       rules of Iris that do not refer to specific contracts. *)
    Include IrisSignatureRules ExampleGlobalState ExampleSignature ExampleProgram ExampleSemantics ExampleProgramLogic ExampleIrisPrelims ExampleIrisBase.
    Include IrisAdequacy ExampleGlobalState ExampleSignature ExampleProgram ExampleSemantics ExampleProgramLogic ExampleIrisPrelims ExampleIrisBase ExampleIrisAdeqParams.

  End ExampleIrisInstance.

  (* The [IrisInstanceWithContracts] implements the program logic rules that can
     refer to the [Specification] module, which contains the contracts for
     functions. These rules therefore include function call rules and the rule
     for a ghost lemma statement. We split up the construction of the model in
     this way to allow combinations of multiple different set of contracts for a
     single program. *)
  Module ExampleIrisInstanceWithContracts.
    (* Include our axiomatic program logic. Note that the program logic is
       parameterized over a given set of contracts so it is included here
       instead of [IrisInstance].  *)
    Include IrisInstanceWithContracts ExampleGlobalState ExampleSignature
      ExampleProgram ExampleSemantics ExampleProgramLogic ExampleIrisPrelims
      ExampleIrisBase ExampleIrisInstance.

    (* Import the soundness proofs for the shallow and symbolic executors. *)
    Include MicroSail.ShallowSoundness.Soundness ExampleGlobalState ExampleSignature
      ExampleProgram ExampleProgramLogic ExampleShalExec.
    Include MicroSail.RefineExecutor.RefineExecOn ExampleGlobalState ExampleSignature
      ExampleProgram ExampleProgramLogic ExampleShalExec ExampleExecutor.

    (* In this section we verify the contracts of the foreign functions defined in
       Coq and the entailments encoded in ghost lemmas using Iris Proof Mode. *)
    Section WithIrisNotations.
      Import iris.bi.interface.
      Import iris.bi.big_op.
      Import iris.base_logic.lib.iprop.
      Import iris.program_logic.weakestpre.
      Import iris.base_logic.lib.gen_heap.
      Import iris.proofmode.string_ident.
      Import iris.proofmode.proofmode.

      Ltac destruct_syminstance ι :=
        repeat
          match type of ι with
          | Env _ (ctx.snoc _ (MkB ?s _)) =>
              string_to_ident_cps s
                ltac:(fun id =>
                        let fr := fresh id in
                        destruct (env.view ι) as [ι fr];
                        destruct_syminstance ι)
          | Env _ ctx.nil => destruct (env.view ι)
          | _ => idtac
          end.

      Lemma mkcons_sound `{sailGS Σ} :
        ValidContractForeign sep_contract_mkcons mkcons.
      Proof.
        intros Γ es δ ι Heq.
        destruct (env.view ι) as [ι xs].
        destruct (env.view ι) as [ι x].
        destruct (env.view ι). cbn.
        iIntros "_".
        iApply semWP_foreign.
        iIntros (γ1 μ1) "[Hregs Hmem]".
        unfold mem_state_interp.
        iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
        iModIntro. iIntros (? ? ? f1).
        rewrite Heq in f1. cbn in f1.
        destruct_conjs; subst.
        do 3 iModIntro.
        iMod "Hclose2" as "_".
        iMod (gen_heap_alloc μ1 (infinite_fresh (A := Z) (elements (dom μ1))) (x, xs) with "Hmem") as "[Hmem [Hres _]]".
        { rewrite <-not_elem_of_dom, <-elem_of_elements.
          now eapply infinite_is_fresh.
        }
        iModIntro.
        iFrame.
        iApply wp_value.
        now iFrame.
      Qed.

      Lemma fst_sound `{sailGS Σ} :
        ValidContractForeign sep_contract_fst fst.
      Proof.
        intros Γ es δ ι Heq.
        destruct (env.view ι) as [ι vxs].
        destruct (env.view ι) as [ι vx].
        destruct (env.view ι) as [ι vp].
        destruct (env.view ι). cbn.
        iIntros "Hres".
        iApply semWP_foreign.
        iIntros (γ1 μ1) "[Hregs Hmem]".
        iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
        iModIntro. iIntros (? ? ? f1).
        rewrite Heq in f1. cbn in f1.
        unfold mem_state_interp.
        do 3 iModIntro.
        iMod "Hclose2" as "_".
        iPoseProof (gen_heap_valid μ1 vp (DfracOwn 1) (vx,vxs) with "Hmem Hres") as "%eq".
        rewrite eq in f1.
        destruct_conjs; subst.
        iModIntro.
        iFrame.
        iApply wp_value.
        now iFrame.
      Qed.

      Lemma snd_sound `{sailGS Σ} :
        ValidContractForeign sep_contract_snd snd.
      Proof.
        intros Γ es δ ι Heq.
        destruct (env.view ι) as [ι vxs].
        destruct (env.view ι) as [ι vx].
        destruct (env.view ι) as [ι vp].
        destruct (env.view ι). cbn.
        iIntros "Hres".
        iApply semWP_foreign.
        iIntros (γ1 μ1) "[Hregs Hmem]".
        iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
        iModIntro. iIntros (? ? ? f1).
        rewrite Heq in f1. cbn in f1.
        unfold mem_state_interp.
        do 3 iModIntro.
        iMod "Hclose2" as "_".
        iPoseProof (gen_heap_valid μ1 vp (DfracOwn 1) (vx,vxs) with "Hmem Hres") as "%".
        rewrite H0 in f1.
        destruct_conjs; subst.
        iModIntro.
        iFrame.
        iApply wp_value.
        now iFrame.
      Qed.

      Lemma setfst_sound `{sailGS Σ} :
        ValidContractForeign sep_contract_setfst setfst.
      Proof.
        intros Γ es δ ι Heq.
        destruct (env.view ι) as [ι vxs].
        destruct (env.view ι) as [ι vx].
        destruct (env.view ι) as [ι vp].
        destruct (env.view ι). cbn.
        iIntros "Hres".
        iDestruct "Hres" as (vx__old) "Hres".
        iApply semWP_foreign.
        iIntros (γ1 μ1) "[Hregs Hmem]".
        iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
        iModIntro.
        iIntros (res ? ? Hf).
        iPoseProof (gen_heap_valid μ1 vp (DfracOwn 1) (vx__old,vxs) with "Hmem Hres") as "%".
        iIntros "!> !> !>". iMod "Hclose2" as "_".
        iPoseProof (gen_heap_valid μ1 vp (DfracOwn 1) (vx__old,vxs) with "Hmem Hres") as "%".
        rewrite Heq in Hf. cbn in Hf. rewrite H0 in Hf.
        destruct_conjs; subst.
        iMod (gen_heap_update μ1 vp (vx__old,vxs) (vx,vxs) with "Hmem Hres") as "[Hmem Hres]".
        iModIntro.
        iFrame.
        iApply semWP_val.
        now iFrame.
      Qed.

      Lemma setsnd_sound `{sailGS Σ} :
        ValidContractForeign sep_contract_setsnd setsnd.
      Proof.
        intros Γ es δ ι Heq.
        destruct (env.view ι) as [ι vxs].
        destruct (env.view ι) as [ι vx].
        destruct (env.view ι) as [ι vp].
        destruct (env.view ι). cbn.
        iIntros "Hres".
        iDestruct "Hres" as (vxs__old) "Hres".
        iApply semWP_foreign.
        iIntros (γ1 μ1) "[Hregs Hmem]".
        iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
        iModIntro. iIntros (res ? ? Hf).
        rewrite Heq in Hf. cbn in Hf.
        unfold mem_state_interp.
        do 3 iModIntro.
        iMod "Hclose2" as "_".
        iPoseProof (gen_heap_valid μ1 vp (DfracOwn 1) (vx,vxs__old) with "Hmem Hres") as "%".
        rewrite H0 in Hf.
        destruct_conjs; subst.
        iMod (gen_heap_update μ1 vp (vx,vxs__old) (vx,vxs) with "Hmem Hres") as "[Hmem Hres]".
        iModIntro.
        iFrame.
        iApply wp_value.
        now iFrame.
      Qed.

      Lemma foreignSem `{sailGS Σ} : ForeignSem.
      Proof.
        intros τ Δ f; destruct f;
          eauto using mkcons_sound, fst_sound, snd_sound, setfst_sound, setsnd_sound.
      Qed.

      Goal True. idtac "Timing before: llist/lemmas". Abort.
      Lemma lemSem `{sailGS Σ} : LemmaSem.
      Proof.
        intros Γ l.
        destruct l; cbn; intros ι; destruct_syminstance ι; cbn.
        - auto.
        - iIntros "Hres".
          destruct xs; cbn.
          { iDestruct "Hres" as "%". inversion H0. }
          iDestruct "Hres" as (p' pn) "[% [Hp' Hpn]]".
          inversion H0; subst.
          iExists pn.
          iFrame.
        - iIntros "Hres".
          destruct xs; cbn.
          + now destruct p.
          + iDestruct "Hres" as (p' pn) "[% _]".
            inversion H0.
        - iIntros "[Hp Hn]".
          iExists p.
          iExists n.
          now iFrame.
      Qed.
      Goal True. idtac "Timing after: llist/lemmas". Abort.

      (* Show that all the contracts are sound in the Iris model. *)
      Lemma linked_list_sound `{sailGS Σ} : ⊢ ValidContractEnvSem CEnv.
      Proof.
        apply (sound foreignSem lemSem).
        intros Γ τ f c.
        destruct f; inversion 1; subst;
          apply shallow_vcgen_soundness;
          apply symbolic_vcgen_soundness;
          apply Symbolic.validcontract_reflect_sound.
        apply valid_contract_append.
        apply valid_contract_appendloop.
        apply valid_contract_length.
        apply valid_contract_copy.
        apply valid_contract_reverse.
        apply valid_contract_reverseloop.
      Qed.

      Goal True. idtac "Assumptions linked_list_sound:". Abort.
      Print Assumptions linked_list_sound.

    End WithIrisNotations.

  End ExampleIrisInstanceWithContracts.

End ExampleModel.

Section Statistics.

  Variable undefined : forall A, A.

  #[global] Instance stats_forall {A} {B : A -> Prop} {SP : forall a, CStatistics.ShallowStats (B a)} :
    CStatistics.ShallowStats (forall a : A, B a) := SP (undefined A).
  #[global] Instance stats_exists {A} {B : A -> Prop} {SP : forall a, CStatistics.ShallowStats (B a)} :
    CStatistics.ShallowStats (exists a : A, B a) := SP (undefined A).

  (* This tactic calculates the number of different execution branches explored by
     the shallow and symbolic executor for the body of the function [fn]. *)
  Ltac calcstats fn :=
    let smb := eval compute in (Symbolic.Statistics.calc fn) in
    let shl := Shallow.Statistics.calc fn in
    let row := constr:(pair fn (pair shl smb)) in
    idtac row.

  (* We print the statistics for every μSail function defined in the program. *)
  Goal forall {Δ τ} (f : Fun Δ τ), f = f.
    idtac "Branching statistics:".
    destruct f;
      match goal with
      |- ?g = _ => calcstats g
      end.
  Abort.

End Statistics.
