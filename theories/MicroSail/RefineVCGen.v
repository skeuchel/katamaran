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
     Signature
     Verifier
     Program
     Hoare
     MicroSail.ShallowVCGen
     MicroSail.SymbolicVCGen.
From Katamaran Require Export
     MicroSail.RefineExecutor.

Import ctx.notations.
Import env.notations.

Module RefineVCGenOn
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG)
  (Import V    : Verifier B SIG)
  (Import SHAL : ShallowVCGen B SIG PROG PLOG V)
  (Import SYMB : SymbolicVCGen B SIG PROG PLOG V).

  Include RefineExecOn B SIG PROG PLOG SHAL SYMB.

  Import ModalNotations.
  Import SymProp.
  Import logicalrelation logicalrelation.notations.
  Import LogicalSoundness.
  Import proofmode.
  Import iris.proofmode.environments.
  Import iris.proofmode.proofmode.

  Section WithSpec.

    Import HeapSpec.

    Context {SPEC : Specification}.

    #[export] Instance refine_vcgen (cfg : Config) (fuel : nat) {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) w :
      Related (RProp) (SHAL.vcgen cfg fuel c body) w (SYMB.vcgen cfg fuel c body w).
    Proof.
      unfold SHAL.vcgen, SYMB.vcgen. solve_related.
    Qed.

  End WithSpec.

  Lemma refine_replay (s : 𝕊 wnil) :
    ⊢ ℛ⟦RProp⟧ (SHAL.replay s [env]) (SYMB.replay s).
  Proof.
    unfold SHAL.replay, SYMB.replay.
    iApply HeapSpec.refine_run.
    iApply (RReplay.refine_replay_aux (RM := @RHeapSpec) s).
    now iApply (refine_lift (AT := Sub [ctx])).
  Qed.

  Lemma replay_sound (s : 𝕊 wnil) :
    safe (SYMB.replay s) [env] -> safe s [env].
  Proof.
    intros H.
    apply SHAL.replay_sound.
    exact (RProp_safe (refine_replay s) H).
  Qed.

  Lemma symbolic_vcgen_fuel_soundness {SPEC : Specification} {Γ τ} (fuel : nat)
    (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContractWithFuel fuel c body ->
    Shallow.ValidContractWithFuel fuel c body.
  Proof.
    unfold Symbolic.ValidContractWithFuel, Shallow.ValidContractWithFuel.
    intros [Hwp%postprocess_sound].
    apply replay_sound in Hwp.
    apply postprocess_sound in Hwp.
    exact (RProp_safe (refine_vcgen _ _ _ _ _) Hwp).
  Qed.

  Lemma symbolic_vcgen_soundness {SPEC : Specification} {Γ τ}
    (c : SepContract Γ τ) (body : Stm Γ τ) :
    Symbolic.ValidContract c body ->
    Shallow.ValidContract c body.
  Proof.
    unfold Symbolic.ValidContract, Shallow.ValidContract.
    apply symbolic_vcgen_fuel_soundness.
  Qed.

  (* Print Assumptions symbolic_vcgen_soundness. *)

End RefineVCGenOn.
