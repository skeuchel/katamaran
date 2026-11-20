(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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


From Katamaran Require Import
     Prelude
     Signature
     Verifier
     Hoare.
From Katamaran Require Export
     MicroSail.SymbolicExecutor.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type SymbolicVCGenOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG)
  (Import V : Verifier B SIG)
  (Import EXEC : SymbolicExecOn B SIG PROG PLOG).

  Import ModalNotations.
  Import SymProp.
  Import Postprocessing.
  Local Open Scope modal.

  Definition vcgen {SPEC : Specification} (cfg : Config) (inline_fuel : nat) {Δ τ}
    (c : SepContract Δ τ) (s : Stm Δ τ) : ⊢ 𝕊 :=
    fun w => SHeapSpec.run (exec_contract (M := SHeapSpec) (sexec cfg inline_fuel) c s w).

  Definition replay : ⊢ 𝕊 -> 𝕊 :=
    fun w P => SHeapSpec.run (SReplay.replay_aux (M := SHeapSpec) P (sub_id w)).

  Module Symbolic.

    Definition ValidContractWithFuel {SPEC : Specification} {Δ τ} (fuel : nat)
      (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationCondition
        (postprocess (replay (postprocess (vcgen default_config fuel c body wnil)))).

    Definition ValidContract {SPEC : Specification} {Δ τ} (c : SepContract Δ τ)
      (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

    Definition verification_failed_with_error (msg : amsg.EAMessage) : bool := false.
    Opaque verification_failed_with_error.

    Fixpoint ok' {Σ} (p : 𝕊 Σ) : bool :=
      match p with
      | SymProp.block => true
      | SymProp.debug _ p => ok' p
      | SymProp.error msg => verification_failed_with_error (amsg.erase_amessage _ msg)
      | _           => false
      end.
    Definition ok {Σ} (p : 𝕊 Σ) : bool := ok' (prune p).

    Lemma ok_sound {Σ} (p : 𝕊 Σ) (ι : Valuation Σ) :
      is_true (ok p) -> safe p ι.
    Proof.
      rewrite <- prune_sound. unfold ok.
      generalize (prune p) as q. clear. intros q.
      induction q; try discriminate; cbn; intuition.
    Qed.

    Definition ValidContractReflectWithFuel {SPEC : Specification} {Δ τ}
      (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      is_true (ok (postprocess (replay (postprocess (vcgen default_config fuel c body wnil))))).

    Definition ValidContractReflect {SPEC : Specification} {Δ τ}
      (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      ValidContractReflectWithFuel 1 c body.

    Lemma validcontract_reflect_fuel_sound {SPEC : Specification} {Δ τ}
      (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractReflectWithFuel fuel c body ->
      ValidContractWithFuel fuel c body.
    Proof.
      unfold ValidContractReflectWithFuel, ValidContractWithFuel. intros Hok.
      apply (ok_sound _ env.nil) in Hok. now constructor.
    Qed.

    Lemma validcontract_reflect_sound {SPEC : Specification} {Δ τ}
      (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractReflect c body ->
      ValidContract c body.
    Proof.
      unfold ValidContract, ValidContractReflect.
      now apply validcontract_reflect_fuel_sound.
    Qed.

    Definition VcGenErasureFuel {SPEC : Specification} {Δ τ} (fuel : nat)
      (c : SepContract Δ τ) (body : Stm Δ τ) : Erasure.ESymProp :=
      Erasure.erase_symprop (postprocess (replay (postprocess (vcgen default_config fuel c body wnil)))).

    Definition ValidContractWithErasureAndFuel {SPEC : Specification} {Δ τ}
      (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationConditionWithErasure (VcGenErasureFuel fuel c body).

    Definition VcGenErasure {SPEC : Specification} {Δ τ} (c : SepContract Δ τ)
      (body : Stm Δ τ) : Erasure.ESymProp :=
      VcGenErasureFuel 1 c body.

    Definition ValidContractWithErasure {SPEC : Specification} {Δ τ}
      (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      VerificationConditionWithErasure (VcGenErasure c body).

    Lemma verification_condition_with_erasure_sound (p : 𝕊 ctx.nil) :
      VerificationConditionWithErasure (Erasure.erase_symprop p) ->
      VerificationCondition p.
    Proof. intros [H]. constructor. now rewrite <- Erasure.erase_safe. Qed.

    Lemma validcontract_with_erasure_sound {SPEC : Specification} {Δ τ}
      (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractWithErasure c body ->
      ValidContract c body.
    Proof. apply verification_condition_with_erasure_sound. Qed.

    Lemma validcontract_with_erasure_and_fuel_sound {SPEC : Specification} {Δ τ}
      {fuel} (c : SepContract Δ τ) (body : Stm Δ τ) :
      ValidContractWithErasureAndFuel fuel c body ->
      ValidContractWithFuel fuel c body.
    Proof. apply verification_condition_with_erasure_sound. Qed.

    Module Statistics.

      Import SymProp.Statistics.

      Definition extend_postcond_with_debug {Δ τ} (c : SepContract Δ τ) : SepContract Δ τ :=
        match c with
        | {| sep_contract_logic_variables := lvars;
             sep_contract_localstore      := store;
             sep_contract_precondition    := pre;
             sep_contract_result          := res;
             sep_contract_postcondition   := post;
          |} => {| sep_contract_logic_variables := lvars;
                   sep_contract_localstore      := store;
                   sep_contract_precondition    := pre;
                   sep_contract_result          := res;
                   sep_contract_postcondition   := asn.sep post asn.debug;
                |}
        end.

      Definition calc {SPEC : Specification} {Δ τ} (f : 𝑭 Δ τ) : option (Stats) :=
        match CEnv f with
        | Some contract =>
            let contract' := extend_postcond_with_debug contract in
            let body      := FunDef f in
            let vc        := vcgen default_config 1 contract' body wnil in
            Some (count_to_stats (count_nodes vc empty))
        | None   => None
        end.

      (* VC sizes before and after each postprocessing step of [ValidContractWithFuel]. *)
      Record VCStats : Set :=
        { vc_raw         : VCCount  (* output of the executor *)
        ; vc_postprocess : VCCount  (* after postprocess *)
        ; vc_replay      : VCCount  (* after postprocess; replay; postprocess *)
        }.

      Definition vc_stats {SPEC : Specification} {Δ τ} (fuel : nat) (f : 𝑭 Δ τ) :
        option VCStats :=
        match CEnv f with
        | Some c =>
            let vc := vcgen default_config fuel c (FunDef f) wnil in
            Some {| vc_raw         := vc_count vc vc_count_empty;
                    vc_postprocess := vc_count (postprocess vc) vc_count_empty;
                    vc_replay      := vc_count (postprocess (replay (postprocess vc)))
                                        vc_count_empty |}
        | None => None
        end.

      (* [raw; postprocess; replay], each as [vc_count_to_list]. *)
      Definition vc_stats_to_list (o : option VCStats) : list (list N) :=
        match o with
        | Some s => vc_count_to_list (vc_raw s) :: vc_count_to_list (vc_postprocess s) ::
                      vc_count_to_list (vc_replay s) :: nil
        | None => nil
        end.

    End Statistics.

  End Symbolic.

End SymbolicVCGenOn.

Module Type SymbolicVCGen (B : Base) (SIG : Signature B) (PROG : Program B)
  (PLOG : ProgramLogic B SIG PROG) (V : Verifier B SIG) :=
  SymbolicExecOn B SIG PROG PLOG <+ SymbolicVCGenOn B SIG PROG PLOG V.

Module MakeExecutor
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG)
  (Import V    : Verifier B SIG).

  Include SymbolicVCGen B SIG PROG PLOG V.

End MakeExecutor.
