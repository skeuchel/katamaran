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

From Katamaran Require Import
     Bitvector
     Environment
     Iris.Base
     RiscvPmp.Machine
     RiscvPmp.GVT.trace.
From iris Require Import
     base_logic.lib.gen_heap
     proofmode.proofmode.

Set Implicit Arguments.

Import RiscvPmpProgram.

(* Instantiate the Iris framework solely using the operational semantics. At
   this point we do not commit to a set of contracts nor to a set of
   user-defined predicates. *)
(* Pull in the definition of the LanguageMixin and register ghost state. *)
Module RiscvPmpIrisPrelims <: IrisPrelims RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics.
  Include IrisPrelims RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics.
End RiscvPmpIrisPrelims.

Module RiscvPmpIrisBase <: IrisBase RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RiscvPmpIrisPrelims.
  Import RiscvPmpIrisPrelims.

  Section RiscvPmpIrisParams.
    (* Defines the memory ghost state. *)
    Definition MemVal : Set := Byte.

    (* NOTE: no resource present for current `State`, since we do not wish to reason about it for now *)
    Class mcMemGS Σ :=
      McMemGS {
          (* ghost variable for tracking state of heap *)
          mc_ghGS : gen_heapGS Addr MemVal Σ;
          (* tracking traces: we want a ghost variable for tracking the current trace *)
          mc_gtGS : traceG Trace Σ;

        }.
    #[export] Existing Instance mc_ghGS.
    #[export] Existing Instance mc_gtGS.

    Definition memGS : gFunctors -> Set := mcMemGS.

    Definition mem_state_interp : forall {Σ}, mcMemGS Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp memmap
           ∗ ⌜ map_Forall (fun a v => memory_ram μ a = v) memmap ⌝
           ∗ tr_auth1 (memory_trace μ)
        )%I.

  End RiscvPmpIrisParams.

  Include IrisResources RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RiscvPmpIrisPrelims.
  Include IrisWeakestPre RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RiscvPmpIrisPrelims.
  Include IrisTotalWeakestPre RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RiscvPmpIrisPrelims.
  Include IrisTotalPartialWeakestPre RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RiscvPmpIrisPrelims.

  Import iris.program_logic.weakestpre.

  Definition WP_loop `{sg : sailGS Σ} : iProp Σ :=
    semWP env.nil (FunDef loop) (fun _ _ => True%I).
  Definition TWP_loop `{sg : sailGS Σ} : iProp Σ :=
    semTWP env.nil (FunDef loop) (fun _ _ => True%I).

  Section PoweredLoop.
  Import Katamaran.Syntax.TypeDecl.
  Import Katamaran.Context.ctx.notations.
  Import Katamaran.Environment.env.notations.

  (* One iteration of the main loop: first the power status is checked. If the
     machine is powered on, it performs a step and continues, otherwise the
     loop ends. *)
  Lemma semWP_fun_loop `{sg : sailGS Σ} (Q : Post [ctx] ty.unit) :
    ((∀ Γ (δ : CStore Γ), semWP δ (call RiscvPmpProgram.step ;; call RiscvPmpProgram.loop) (λ v _, Q v [env])) ∧
     Q (inl tt) [env])
    ⊢ semWP env.nil (FunDef loop) Q.
  Proof.
    iIntros "H". cbn [FunDef]. unfold fun_loop.
    iApply semWP_let. iApply semWP_foreign.
    iIntros (γ μ) "Hstate".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (res γ' μ' Hf). cbn in Hf. inversion Hf; subst.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "Hstate".
    rewrite semWP_val. iModIntro. cbn.
    iApply semWP_pattern_match. iApply semWP_exp. cbn.
    destruct (fun_powered_on μ).
    - iDestruct "H" as "[H _]". iApply (semWP_mono with "[H]"); first iApply "H".
      iIntros (v δ') "HQ". destruct (env.view δ') as [δ'' ?]. by destruct (env.view δ'').
    - iDestruct "H" as "[_ H]". rewrite semWP_val. by iModIntro.
  Qed.
  End PoweredLoop.

  (* Useful instance for some of the Iris proofs *)
  #[export] Instance state_inhabited : Inhabited State.
  Proof. repeat constructor.
          - intros ty reg. apply val_inhabited.
          - intro. apply bv.bv_inhabited.
          - apply state_inhabited.
  Qed.

End RiscvPmpIrisBase.
