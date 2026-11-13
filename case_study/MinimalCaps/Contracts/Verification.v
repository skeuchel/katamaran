(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
     Program.Tactics
     Strings.String
     ZArith.ZArith
     Classes.EquivDec
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Base
     MinimalCaps.Logic
     MinimalCaps.Machine
     MinimalCaps.Sig
     MinimalCaps.Contracts.Definitions
     Sep.Hoare
     MicroSail.ShallowExecutor
     MicroSail.SymbolicExecutor
     Symbolic.Solver.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Import MinCapsProgramLogic.
Import MinCapsSpecification.

(*** MinCapsValidContracts ***)
(* In this module we prove that all specified contracts are valid. *)
Module MinCapsValidContracts.
  Import MinCapsExecutor.
  Import MinCapsSignature.

  Local Ltac solve :=
    repeat
      (repeat
         match goal with
         | H: _ /\ _ |- _ => destruct H
         | H: Empty_set |- _ => destruct H
         | |- forall _, _ => cbn [Val snd]; intro
         | |- False \/ _ =>  right
         | |- _ \/ False =>  left
         | |- _ \/ exists _, _ =>  left (* avoid existentials, bit fishy but fine for now *)
         | |- _ /\ _ => constructor
         | |- VerificationCondition _ =>
             constructor;
             cbv [SymProp.safe nenv.remove nenv.lookup bop.eval is_true
                               inst inst_term instprop_formula env.Env_rect nenv.NamedEnv_rect];
             cbn
         | |- Obligation _ _ _ => constructor; cbn
         | |- Debug _ _ => constructor
         | |- Debug _ True \/ _ => left
         | |- (_ \/ _) \/ _ => rewrite or_assoc
         | |- context[Z.leb ?x ?y] =>
             destruct (Z.leb_spec x y)
         end;
       cbn [List.length andb is_true Val snd];
       subst; try congruence; try lia;
       auto
      ).

  Import MinCapsContractNotations.

  Definition ValidContractReflect {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractReflect c (FunDef f)
    | None => True
    end.

  Definition ValidContractWithErasure {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractWithErasure c (FunDef f)
    | None => True
    end.

  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContract c (FunDef f)
    | None => True
    end.

  Ltac symbolic_simpl :=
    apply Symbolic.validcontract_with_erasure_sound;
    compute;
    constructor;
    cbn.

  Lemma valid_contract_read_reg : ValidContractReflect read_reg.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_read_reg_cap : ValidContractReflect read_reg_cap.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_read_reg_num : ValidContractReflect read_reg_num.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_write_reg : ValidContractReflect write_reg.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_next_pc : ValidContractReflect next_pc.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_update_pc : ValidContractReflect update_pc.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_update_pc_perm : ValidContractReflect update_pc_perm.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_is_correct_pc : ValidContractReflect is_correct_pc.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_is_perm : ValidContractReflect MinCapsProgram.is_perm.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_add_pc : ValidContractReflect add_pc.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_read_mem : ValidContractReflect read_mem.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_write_mem : ValidContractReflect write_mem.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_read_allowed : ValidContractReflect read_allowed.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_write_allowed : ValidContractReflect write_allowed.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_within_bounds : ValidContractReflect within_bounds.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_perm_to_bits : ValidContractReflect perm_to_bits.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_perm_from_bits : ValidContractReflect perm_from_bits.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_and_perm : ValidContractReflect and_perm.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_is_sub_perm : ValidContractReflect is_sub_perm.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_is_within_range : ValidContractReflect is_within_range.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_abs : ValidContractReflect abs.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_is_not_zero : ValidContractReflect is_not_zero.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_can_incr_cursor : ValidContractReflect can_incr_cursor.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_jalr_cap : ValidContractReflect exec_jalr_cap.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cjalr : ValidContractReflect exec_cjalr.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cjal : ValidContractReflect exec_cjal.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_bne : ValidContractReflect exec_bne.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cmove : ValidContractReflect exec_cmove.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_ld : ValidContractReflect exec_ld.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_sd : ValidContractReflect exec_sd.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cincoffset : ValidContractReflect exec_cincoffset.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_candperm : ValidContractReflect exec_candperm.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_csetbounds : ValidContractReflect exec_csetbounds.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_csetboundsimm : ValidContractReflect exec_csetboundsimm.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cgettag : ValidContractReflect exec_cgettag.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_addi : ValidContractReflect exec_addi.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_add : ValidContractReflect exec_add.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_sub : ValidContractReflect exec_sub.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_slt : ValidContractReflect exec_slt.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_slti : ValidContractReflect exec_slti.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_sltu : ValidContractReflect exec_sltu.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_sltiu : ValidContractReflect exec_sltiu.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cgetperm : ValidContractReflect exec_cgetperm.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cgetbase : ValidContractReflect exec_cgetbase.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cgetlen : ValidContractReflect exec_cgetlen.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_cgetaddr : ValidContractReflect exec_cgetaddr.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_fail : ValidContractReflect exec_fail.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_ret : ValidContractReflect exec_ret.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec_instr : ValidContractReflect exec_instr.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exec : ValidContractReflect exec.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_step : ValidContractReflect step.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_reflect : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractReflect f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractReflect in Hvc.
    rewrite Hcenv in Hvc.
    apply Symbolic.validcontract_reflect_sound.
    apply Hvc.
  Qed.

  Lemma valid_contract : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContract f ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContract in Hvc.
    rewrite Hcenv in Hvc.
    apply Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      Symbolic.ValidContract c (FunDef f).
  Proof.
    intros; destruct f.
    - refine (valid_contract_reflect _ H valid_contract_read_reg).
    - refine (valid_contract_reflect _ H valid_contract_read_reg_cap).
    - refine (valid_contract_reflect _ H valid_contract_read_reg_num).
    - refine (valid_contract_reflect _ H valid_contract_write_reg).
    - refine (valid_contract_reflect _ H valid_contract_next_pc).
    - refine (valid_contract_reflect _ H valid_contract_update_pc).
    - refine (valid_contract_reflect _ H valid_contract_update_pc_perm).
    - refine (valid_contract_reflect _ H valid_contract_is_correct_pc).
    - refine (valid_contract_reflect _ H valid_contract_is_perm).
    - refine (valid_contract_reflect _ H valid_contract_add_pc).
    - refine (valid_contract_reflect _ H valid_contract_read_mem).
    - refine (valid_contract_reflect _ H valid_contract_write_mem).
    - refine (valid_contract_reflect _ H valid_contract_read_allowed).
    - refine (valid_contract_reflect _ H valid_contract_write_allowed).
    - refine (valid_contract_reflect _ H valid_contract_within_bounds).
    - refine (valid_contract_reflect _ H valid_contract_perm_to_bits).
    - refine (valid_contract_reflect _ H valid_contract_perm_from_bits).
    - refine (valid_contract_reflect _ H valid_contract_and_perm).
    - refine (valid_contract_reflect _ H valid_contract_is_sub_perm).
    - refine (valid_contract_reflect _ H valid_contract_is_within_range).
    - refine (valid_contract_reflect _ H valid_contract_abs).
    - refine (valid_contract_reflect _ H valid_contract_is_not_zero).
    - refine (valid_contract_reflect _ H valid_contract_can_incr_cursor).
    - refine (valid_contract_reflect _ H valid_contract_exec_jalr_cap).
    - refine (valid_contract_reflect _ H valid_contract_exec_cjalr).
    - refine (valid_contract_reflect _ H valid_contract_exec_cjal).
    - refine (valid_contract_reflect _ H valid_contract_exec_bne).
    - refine (valid_contract_reflect _ H valid_contract_exec_ld).
    - refine (valid_contract_reflect _ H valid_contract_exec_sd).
    - refine (valid_contract_reflect _ H valid_contract_exec_addi).
    - refine (valid_contract_reflect _ H valid_contract_exec_add).
    - refine (valid_contract_reflect _ H valid_contract_exec_sub).
    - refine (valid_contract_reflect _ H valid_contract_exec_slt).
    - refine (valid_contract_reflect _ H valid_contract_exec_slti).
    - refine (valid_contract_reflect _ H valid_contract_exec_sltu).
    - refine (valid_contract_reflect _ H valid_contract_exec_sltiu).
    - refine (valid_contract_reflect _ H valid_contract_exec_cmove).
    - refine (valid_contract_reflect _ H valid_contract_exec_cincoffset).
    - refine (valid_contract_reflect _ H valid_contract_exec_candperm).
    - refine (valid_contract_reflect _ H valid_contract_exec_csetbounds).
    - refine (valid_contract_reflect _ H valid_contract_exec_csetboundsimm).
    - refine (valid_contract_reflect _ H valid_contract_exec_cgettag).
    - refine (valid_contract_reflect _ H valid_contract_exec_cgetperm).
    - refine (valid_contract_reflect _ H valid_contract_exec_cgetbase).
    - refine (valid_contract_reflect _ H valid_contract_exec_cgetlen).
    - refine (valid_contract_reflect _ H valid_contract_exec_cgetaddr).
    - refine (valid_contract_reflect _ H valid_contract_exec_fail).
    - refine (valid_contract_reflect _ H valid_contract_exec_ret).
    - refine (valid_contract_reflect _ H valid_contract_exec_instr).
    - refine (valid_contract_reflect _ H valid_contract_exec).
    - refine (valid_contract_reflect _ H valid_contract_step).
    - cbn in H; inversion H.
  Qed.

  Goal True. idtac "Timing before: minimalcaps". Abort.
  Lemma valid_contracts : forall {Δ τ} (f : Fun Δ τ),
      ValidContractReflect f.
  Proof.
    destruct f; now vm_compute.
  Qed.
  Goal True. idtac "Timing after: minimalcaps". Abort.

  Goal True. idtac "Assumptions for minimalcaps contracts:". Abort.
  Print Assumptions ValidContracts.
End MinCapsValidContracts.
