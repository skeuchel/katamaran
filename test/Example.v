(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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
     Signature
     Bitvector
     Sep.Hoare
     Semantics.Registers
     MicroSail.SymbolicExecutor
     Symbolic.Solver
     Program.

From stdpp Require Import decidable finite.

Set Implicit Arguments.
Import ctx.notations.
Import env.notations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** TYPES ***)

(** Enums **)
Inductive Enums : Set :=
| ordering.

Inductive Ordering : Set :=
| LT
| EQ
| GT.

(** Unions **)
Inductive Unions : Set :=
| either.

Inductive EitherConstructor : Set :=
| Left
| Right.

(** Records **)
Inductive Records : Set :=.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Enums.
  Derive NoConfusion for Ordering.
  Derive NoConfusion for Unions.
  Derive NoConfusion for EitherConstructor.
  Derive NoConfusion for Records.

End TransparentObligations.

Derive EqDec for Enums.
Derive EqDec for Ordering.
Derive EqDec for Unions.
Derive EqDec for EitherConstructor.
Derive EqDec for Records.

Section Finite.

  Import stdpp.finite.
  Import ListNotations.

  Local Obligation Tactic :=
    finite_from_eqdec.

  Global Program Instance Ordering_finite : Finite Ordering :=
    {| enum := [LT;EQ;GT] |}.
  Global Program Instance EitherConstructor_finite : Finite EitherConstructor :=
    {| enum := [Left;Right] |}.

End Finite.

Module Import ExampleBase <: Base.
  Import stdpp.finite.

  #[export] Instance typedeclkit : TypeDeclKit :=
    {| enumi := Enums;
       unioni := Unions;
       recordi := Records;
    |}.

  Definition enum_denote (E : Enums) : Set :=
    match E with
    | ordering => Ordering
    end.

  Definition union_denote (U : Unions) : Set :=
    match U with
    | either => (string + Z)%type
    end.

  Definition record_denote (R : Records) : Set :=
    match R with end.

  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit :=
    {| enumt := enum_denote;
       uniont := union_denote;
       recordt := record_denote;
    |}.

  Definition union_constructors (U : Unions) : Set :=
    match U with
    | either => EitherConstructor
    end.

  Definition union_constructor_type (U : Unions) : union_constructors U -> Ty :=
    match U with
    | either => fun K => match K with
                         | Left => ty.string
                         | Right => ty.int
                         end
    end.

  Definition union_unfold (U : unioni) : uniont U -> { K & Val (union_constructor_type U K) } :=
    match U with
    | either => fun Kv =>
                  match Kv with
                  | inl v => existT Left v
                  | inr v => existT Right v
                  end
    end.

  Definition union_fold (U : unioni) : { K & Val (union_constructor_type U K) } -> uniont U :=
    match U with
    | either => fun Kv =>
                  match Kv with
                  | existT Left v  => inl v
                  | existT Right v => inr v
                  end
    end.

  Definition record_field_type (R : recordi) : NCtx Empty_set Ty :=
    match R with end.

  Definition record_fold (R : recordi) : NamedEnv Val (record_field_type R) -> recordt R :=
    match R with end.
  Definition record_unfold (R : recordi) : recordt R -> NamedEnv Val (record_field_type R) :=
    match R with end.

  #[export] Instance eqdec_enum_denote E : EqDec (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance finite_enum_denote E : finite.Finite (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance eqdec_union_denote U : EqDec (union_denote U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_union_constructors U : EqDec (union_constructors U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance finite_union_constructors U : finite.Finite (union_constructors U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_record_denote R : EqDec (record_denote R) :=
    ltac:(destruct R; auto with typeclass_instances).

  #[export,refine] Instance typedefkit : TypeDefKit typedenotekit :=
    {| unionk         := union_constructors;
       unionk_ty      := union_constructor_type;
       unionv_fold    := union_fold;
       unionv_unfold  := union_unfold;
       recordf        := Empty_set;
       recordf_ty     := record_field_type;
       recordv_fold   := record_fold;
       recordv_unfold := record_unfold;
    |}.
  Proof.
    - abstract (now intros [] []).
    - abstract (now intros [] [[]]).
    - abstract (intros []).
    - abstract (intros []).
  Defined.

  #[export] Instance varkit : VarKit := DefaultVarKit.

  Include BaseMixin.

End ExampleBase.

Module Import ExampleGlobalState <: GlobalState.
  Module BASE := ExampleBase.

  Include DefaultRegDeclKit BASE.

  Definition Memory : Set := unit.

End ExampleGlobalState.

(*** PROGRAM ***)

Module Import ExampleProgram <: Program ExampleGlobalState.

  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
    | abs        : Fun [ "x" ∷ ty.int ] ty.int
    | cmp        : Fun [ "x" ∷ ty.int; "y" ∷ ty.int ] (ty.enum ordering)
    | gcd        : Fun [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int
    | gcdloop    : Fun [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int
    | msum       : Fun [ "x" ∷ ty.union either; "y" ∷ ty.union either] (ty.union either)
    | length {σ} : Fun [ "xs" ∷ ty.list σ ] ty.int
    | fpthree16  : Fun [ "sign" ∷ ty.bvec 1 ] (ty.bvec 16)
    | fpthree32  : Fun [ "sign" ∷ ty.bvec 1 ] (ty.bvec 32)
    | fpthree64  : Fun [ "sign" ∷ ty.bvec 1 ] (ty.bvec 64)
    | bvtest     : Fun [ "sign" ∷ ty.bvec 42 ] (ty.bvec 42)
    | bvtest2    : Fun [ "sign" ∷ ty.bvec 42 ] (ty.bvec 42)
    | bvtest3    : Fun [ "sign" ∷ ty.bvec 42 ] ty.int
    | pevaltest1 : Fun [ "sign" ∷ ty.bvec 42; "y" ∷ ty.int ] ty.int
    .

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := fun _ _ => Empty_set.
    Definition 𝑳 : PCtx -> Set := fun _ => Empty_set.
  End FunDeclKit.

  Include FunDeclMixin ExampleGlobalState.

  Section FunDefKit.
    Import ctx.resolution.

    Local Coercion stm_exp : Exp >-> Stm.

    Local Notation "'`LT'" := (@exp_val _ (ty.enum ordering) LT).
    Local Notation "'`GT'" := (@exp_val _ (ty.enum ordering) GT).
    Local Notation "'`EQ'" := (@exp_val _ (ty.enum ordering) EQ).
    Local Notation "'`Left' e" := (exp_union either Left e) (at level 10, e at level 9).
    Local Notation "'`Right' e" := (exp_union either Right e) (at level 10, e at level 9).
    Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
    Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
    Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.

    Definition fun_msum : Stm ["x" ∷ ty.union either; "y" ∷ ty.union either] (ty.union either) :=
      stm_match_union_alt either x
       (fun K =>
          match K with
          | Left  => MkAlt (pat_var "z") (`Left z)
          | Right => MkAlt (pat_var "z") (y)%exp
          end).

    Definition fun_fpthree' (e f : nat) : Stm [ "sign" ∷ ty.bvec 1 ] (ty.bvec (1 + e + f)) :=
      let: "exp" ∷ ty.bvec e := stm_val (ty.bvec e) bv.one in
      let: "frac" ∷ ty.bvec f := stm_val (ty.bvec f) bv.one in
      exp_binop
        (@bop.bvapp _ 1 (e + f))
        (exp_var "sign")
        (exp_binop
           (@bop.bvapp _ e f)
           (exp_var "exp")
           (exp_var "frac")).

    Definition fun_fpthree16 : Stm [ "sign" ∷ ty.bvec 1 ] (ty.bvec 16) :=
      (let n := 16 in
       let e := 5 in
       let f := (n - (e + 1)) in
       fun_fpthree' e f)%nat.

    Definition fun_fpthree32 : Stm [ "sign" ∷ ty.bvec 1 ] (ty.bvec 32) :=
      (let n := 32 in
       let e := 8 in
       let f := (n - (e + 1)) in
       fun_fpthree' e f)%nat.

    Definition fun_fpthree64 : Stm [ "sign" ∷ ty.bvec 1 ] (ty.bvec 64) :=
      (let n := 64 in
       let e := 11 in
       let f := (n - (e + 1)) in
       fun_fpthree' e f)%nat.

    Definition fun_bvtest : Stm [ "sign" ∷ ty.bvec 42 ] (ty.bvec 42) :=
      let: "one" ∷ ty.bvec 42 := stm_val (ty.bvec 42) bv.one in
      let: "zero" ∷ ty.bvec 42 := stm_val (ty.bvec 42) bv.zero in
      exp_binop
        bop.bvadd
        (exp_binop bop.bvsub (exp_var "sign") (exp_var "one"))
        (exp_binop
           bop.bvadd
           (exp_var "one")
           (exp_var "zero"))
    .

    (* This is a test for the ring solver quoter in the partial evaluator, to see if it
       properly identifies different occurrences of the same opaque term
     *)
    Definition fun_bvtest2 : Stm [ "sign" ∷ ty.bvec 42 ] (ty.bvec 42) :=
      let: "one" ∷ ty.bvec 42 := stm_val (ty.bvec 42) bv.one in
      let: "zero" ∷ ty.bvec 42 := stm_val (ty.bvec 42) bv.zero in
      exp_binop
        bop.bvadd
        (exp_binop bop.bvsub (exp_var "sign") (exp_var "one"))
        (exp_binop
           bop.bvadd
           (exp_var "sign")
           (exp_binop bop.bvsub (exp_var "one") (exp_var "sign")))
    .

    Definition fun_bvtest3 : Stm [ "sign" ∷ ty.bvec 42 ] ty.int :=
      let: "one" ∷ ty.bvec 42 := stm_val (ty.bvec 42) bv.one in
      let: "zero" ∷ ty.bvec 42 := stm_val (ty.bvec 42) bv.zero in
      exp_unop uop.unsigned
        (exp_binop bop.bvadd
           (exp_binop bop.bvsub (exp_var "sign") (exp_var "one"))
           (exp_binop
              bop.bvadd
              (exp_val (ty.bvec _) bv.zero)
              (exp_binop bop.bvsub (exp_var "one") (exp_var "sign"))))
    .

    Definition fun_pevaltest1 : Stm [ "sign" ∷ ty.bvec 42; "y" ∷ ty.int ] ty.int :=
      exp_var "y" + exp_unop uop.unsigned (exp_var "sign" -ᵇ exp_var "sign") - exp_var "y"
    .

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      Eval compute in
      match f in Fun Δ τ return Stm Δ τ with
      | abs => if: exp_int 0 <= x then x else - x
      | cmp => if: x < y then `LT else
               if: x = y then `EQ else
               if: x > y then `GT else
               fail "cmp failed"
      | gcd => "x" <- call abs x ;;
               "y" <- call abs y ;;
               call gcdloop x y
      | gcdloop =>
               let: "z" := call cmp x y in
               match: z in ordering with
               | LT => call gcdloop x (y - x)
               | EQ => x
               | GT => call gcdloop (x - y) y
               end
      | msum => fun_msum
      | length => stm_match_list
                    (exp_var "xs")
                    (stm_val ty.int 0)
                    "y" "ys" (let: "n" := call length (exp_var "ys") in exp_int 1 + exp_var "n")
      | fpthree16 => fun_fpthree16
      | fpthree32 => fun_fpthree32
      | fpthree64 => fun_fpthree64
      | bvtest => fun_bvtest
      | bvtest2 => fun_bvtest2
      | bvtest3 => fun_bvtest3
      | pevaltest1 => fun_pevaltest1
      end.
  End FunDefKit.

  Include DefaultRegStoreKit ExampleGlobalState.

  Section ForeignKit.
    Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs)
      (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop := False.
    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof. destruct f. Qed.
  End ForeignKit.

  Include ProgramMixin ExampleGlobalState.

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

    Instance accessible_abs : AccessibleFun abs.
    Proof. accessible_proof. Qed.
    Instance accessible_cmp : AccessibleFun cmp.
    Proof. accessible_proof. Qed.
    Instance accessible_msum : AccessibleFun msum.
    Proof. accessible_proof. Qed.
    Instance accessible_fpthree16 : AccessibleFun fpthree16.
    Proof. accessible_proof. Qed.
    Instance accessible_fpthree32 : AccessibleFun fpthree32.
    Proof. accessible_proof. Qed.
    Instance accessible_fpthree64 : AccessibleFun fpthree64.
    Proof. accessible_proof. Qed.
    Instance accessible_bvtest : AccessibleFun bvtest.
    Proof. accessible_proof. Qed.
    Instance accessible_bvtest2 : AccessibleFun bvtest2.
    Proof. accessible_proof. Qed.
    Instance accessible_bvtest3 : AccessibleFun bvtest3.
    Proof. accessible_proof. Qed.
    Instance accessible_pevaltest1 : AccessibleFun pevaltest1.
    Proof. accessible_proof. Qed.

  End WithAccessibleTactics.

  Definition 𝑭_accessible {Δ τ} (f : 𝑭 Δ τ) : option (AccessibleFun f) :=
    match f with
    | gcd     => None
    | gcdloop => None
    | length  => None
    | _       => Some _
    end.

End ExampleProgram.

Module Import ExampleSig <: Signature ExampleGlobalState.
  Include DefaultPredicateKit ExampleGlobalState.
  Include PredicateMixin ExampleGlobalState.
  Include WorldsMixin ExampleGlobalState.
  Include DefaultSolverKit ExampleGlobalState.
  Include SignatureMixin ExampleGlobalState.
End ExampleSig.

Module Import ExampleProgramLogic :=
  MakeProgramLogic ExampleGlobalState ExampleSig ExampleProgram.

Module Import ExampleSpecification.

  Import ctx.resolution.

  Section ContractDefKit.

    Import asn.notations.
    Abbreviation asn_prop Σ P := (asn.formula (@formula_prop Σ Σ (sub_id Σ) P)).

    Definition sep_contract_abs : SepContract [ "x" ∷ ty.int ] ty.int :=
      {| sep_contract_logic_variables := ["x" ∷ ty.int];
         sep_contract_localstore      := [term_var "x"];
         sep_contract_precondition    := ⊤;
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_prop
             ["x" ∷ ty.int; "result" ∷ ty.int]
             (fun x result => result = Z.abs x)%type
      |}.

    Definition sep_contract_cmp : SepContract ["x" ∷ ty.int; "y" ∷ ty.int] (ty.enum ordering)  :=
       {| sep_contract_logic_variables := ["x" ∷ ty.int; "y" ∷ ty.int];
          sep_contract_localstore      := [term_var "x"; term_var "y"];
          sep_contract_precondition    := ⊤;
          sep_contract_result          := "result";
          sep_contract_postcondition   :=
            asn.match_enum
              ordering (term_var "result")
              (fun result =>
                 match result with
                 | LT => term_var "x" < term_var "y"
                 | EQ => term_var "x" = term_var "y"
                 | GT => term_var "x" > term_var "y"
                 end)
       |}.

    Definition sep_contract_gcd : SepContract [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int :=
      {| sep_contract_logic_variables := ["x" ∷ ty.int; "y" ∷ ty.int];
         sep_contract_localstore      := [term_var "x"; term_var "y"];
         sep_contract_precondition    := ⊤;
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_prop
             ["x" ∷ ty.int; "y" ∷ ty.int; "result" ∷ ty.int]
             (fun x y result => result = Z.gcd x y)%type
      |}.

    Definition sep_contract_gcdloop : SepContract [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int :=
      {| sep_contract_logic_variables := ["x" ∷ ty.int; "y" ∷ ty.int];
         sep_contract_localstore      := [term_var "x"; term_var "y"];
         sep_contract_precondition    :=
           term_val ty.int 0 <= term_var "x" ∗
           term_val ty.int 0 <= term_var "y";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_prop
             ["x" ∷ ty.int; "y" ∷ ty.int; "result" ∷ ty.int]
             (fun x y result => result = Z.gcd x y)%type
      |}.

    Definition length_post {σ} (xs : list (Val σ)) (result : Val ty.int) :=
      (result = Z.of_nat (@Datatypes.length (Val σ) xs))%type.
    Definition sep_contract_length {σ} : SepContract [ "xs" ∷ ty.list σ ] ty.int :=
      {| sep_contract_logic_variables := ["xs" ∷ ty.list σ ];
         sep_contract_localstore      := [term_var "xs"];
         sep_contract_precondition    := ⊤;
         sep_contract_result          := "result";
         sep_contract_postcondition   := asn_prop ["xs"∷ty.list σ; "result"∷ty.int] length_post
      |}.

    Definition sep_contract_bvtest : SepContract [ "sign" ∷ ty.bvec 42 ] (ty.bvec 42) :=
      {| sep_contract_logic_variables := ["sign" ∷ ty.bvec 42 ];
         sep_contract_localstore      := [term_var "sign"];
         sep_contract_precondition    := ⊤;
         sep_contract_result          := "result";
         sep_contract_postcondition   := asn.formula (formula_relop bop.eq (term_var "result") (term_var "sign"))
      |}.

    Definition sep_contract_bvtest2 : SepContract [ "sign" ∷ ty.bvec 42 ] (ty.bvec 42) :=
      {| sep_contract_logic_variables := ["sign" ∷ ty.bvec 42 ];
        sep_contract_localstore      := [term_var "sign"];
        sep_contract_precondition    := ⊤;
        sep_contract_result          := "result";
        sep_contract_postcondition   := asn.formula (formula_relop bop.eq (term_var "result") (term_var "sign"))
      |}.

    Definition sep_contract_bvtest3 : SepContract [ "sign" ∷ ty.bvec 42 ] ty.int :=
      {| sep_contract_logic_variables := ["sign" ∷ ty.bvec 42 ];
        sep_contract_localstore      := [term_var "sign"];
        sep_contract_precondition    := ⊤;
        sep_contract_result          := "result";
        sep_contract_postcondition   := asn.formula (formula_relop bop.eq (term_var "result") (term_val ty.int 0%Z))
      |}.

    Definition sep_contract_pevaltest1 : SepContract [ "sign" ∷ ty.bvec 42 ; "y" ∷ ty.int ] ty.int :=
      {| sep_contract_logic_variables := ["sign" ∷ ty.bvec 42 ; "y" ∷ ty.int ];
        sep_contract_localstore      := [term_var "sign"; term_var "y" ];
        sep_contract_precondition    := ⊤;
        sep_contract_result          := "result";
        sep_contract_postcondition   := term_var "result" = term_val ty.int 0%Z
      |}.

    Definition contract_environment : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | abs        => Some sep_contract_abs
        | cmp        => Some sep_contract_cmp
        | gcd        => Some sep_contract_gcd
        | gcdloop    => Some sep_contract_gcdloop
        | msum       => None
        | length     => Some sep_contract_length
        | fpthree16  => None
        | fpthree32  => None
        | fpthree64  => None
        | bvtest     => Some sep_contract_bvtest
        | bvtest2    => Some sep_contract_bvtest2
        | bvtest3    => Some sep_contract_bvtest3
        | pevaltest1 => Some sep_contract_pevaltest1
        end.

    Definition contract_environment_foreign : SepContractEnvEx :=
      fun Δ τ f =>
        match f with end.

    Definition lemma_environment : LemmaEnv :=
      fun Δ l =>
        match l with end.

  End ContractDefKit.

  #[export] Instance example_specification : Specification :=
    {| CEnv   := contract_environment;
       CEnvEx := contract_environment_foreign;
       LEnv   := lemma_environment;
       fail_rule_pre := true;
    |}.

End ExampleSpecification.

Module Import ExampleExecutor :=
  MakeExecutor ExampleGlobalState ExampleSig ExampleProgram ExampleProgramLogic.

Local Ltac solve :=
  repeat
    (compute
     - [Z.of_nat Pos.of_succ_nat List.length Pos.succ Val Z.add
                 Z.succ
        Z.compare Z.eqb Z.ge Z.geb Z.gt Z.gtb Z.le Z.leb Z.lt
        Z.ltb Z.mul Z.of_nat Z.opp Z.pos_sub Z.succ is_true negb
       ] in *;
      repeat
       match goal with
       | H: NamedEnv _ _ |- _ => unfold NamedEnv in H
       | H: _ /\ _ |- _ => destruct H
       | H: Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
       | H: Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
       | H : pair _ _ = pair _ _ |- _ => inversion H; subst; clear H
       | |- forall _, _ => intro
       | |- exists _, _ => eexists
       | |- Debug _ _ => constructor
       | |- _ /\ _ => constructor
       | |- VerificationCondition _ => constructor; cbn
       | |- Obligation _ _ _ => constructor; cbn
       | |- _ \/ False => left
       | |- False \/ _ => right
       end;
     cbn [List.length Z.add];
     subst; try congruence;
     auto
    ).

Arguments inst {_ _ _ _} !_ _ /.
Arguments inst_term {_} [_] !_ _ /.
Arguments instprop {_ _ _} !_ _ /.
Arguments instprop_formula [_] !_ _ /.

Goal True. idtac "Timing before: example/length". Abort.
Lemma valid_contract_length {σ} : Symbolic.ValidContract (@sep_contract_length σ) (FunDef length).
Proof.
  compute - [length_post Val].
  constructor; simpl; solve; lia.
Qed.
Goal True. idtac "Timing after: example/length". Abort.

Goal True. idtac "Timing before: example/cmp". Abort.
Lemma valid_contract_cmp : Symbolic.ValidContractReflect sep_contract_cmp (FunDef cmp).
Proof. now vm_compute. Qed.
Goal True. idtac "Timing after: example/cmp". Abort.
Lemma valid_contract_bvtest : Symbolic.ValidContractWithErasure sep_contract_bvtest (FunDef bvtest).
Proof.
  now cbv.
Qed.

Lemma valid_contract_bvtest2 : Symbolic.ValidContractWithErasure sep_contract_bvtest2 (FunDef bvtest2).
Proof.
  now cbv.
Qed.

Lemma valid_contract_bvtest3 : Symbolic.ValidContractWithErasure sep_contract_bvtest3 (FunDef bvtest3).
Proof.
  now cbv.
Qed.

Lemma valid_contract_pevaltest1 : Symbolic.ValidContractWithErasure sep_contract_pevaltest1 (FunDef pevaltest1).
Proof.
  now cbv.
Qed.
