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
     RiscvPmp.trace.
From stdpp Require Import namespaces.
Module ns := stdpp.namespaces.
From iris Require Import
  algebra.auth
     base_logic.lib.gen_heap
     base_logic.lib.invariants
     proofmode.proofmode.

Set Implicit Arguments.

Import RiscvPmpProgram.
Import bv.notations.

Module Type RiscvPmpIrisBaseCommon <: IrisPrelims RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics.
  Include IrisPrelims RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics.

  (* Defines the memory ghost state. *)
  Definition MemVal : Set := Byte.

  Definition initMemMap μ := (list_to_map (map (fun a => (a , memory_ram μ a)) liveAddrs) : gmap Addr MemVal).

  Inductive WritePendingState :=
  | NothingPending : WritePendingState
  | Written : Event -> WritePendingState.

  Definition writePendingΣ := #[GFunctor (authR (optionUR (excl.exclR (leibnizO WritePendingState))))].

  Class writePending_preG Σ := WritePending_preG {
                                   writePending_pre_inG :: inG Σ (auth.authR (optionUR (excl.exclR (leibnizO WritePendingState))));
                                 }.

  Class writePendingG Σ := WritePendingG {
                               writePending_inG :: inG Σ (auth.authR (optionUR (excl.exclR (leibnizO WritePendingState))));
                               writePendingG_gname : gname
                             }.

  #[export] Instance writePendingΣ_preG `{writePendingG Σ} : writePending_preG Σ.
  Proof. constructor. typeclasses eauto. Defined.

  #[export] Instance subG_writePendingPreΣ {Σ}:
    subG writePendingΣ Σ →
    writePending_preG Σ.
  Proof. solve_inG. Qed.

  Definition nothingPending_auth `{writePendingG Σ} : iProp Σ :=
    own writePendingG_gname (● (Some (excl.Excl NothingPending) : optionUR (excl.exclR (leibnizO WritePendingState)))).
  Definition nothingPending `{writePendingG Σ} : iProp Σ :=
    own writePendingG_gname (◯ (Some (excl.Excl NothingPending) : optionUR (excl.exclR (leibnizO WritePendingState)))).
  Definition written_auth `{writePendingG Σ} e : iProp Σ :=
    own writePendingG_gname (● (Some (excl.Excl (Written e)) : optionUR (excl.exclR (leibnizO WritePendingState)))).
  Definition written `{writePendingG Σ} e : iProp Σ :=
    own writePendingG_gname (◯ (Some (excl.Excl (Written e)) : optionUR (excl.exclR (leibnizO WritePendingState)))).

  Lemma writePending_alloc `{!writePending_preG Σ} :
    ⊢ |==> ∃ tG : writePendingG Σ,
        nothingPending_auth ∗ nothingPending.
  Proof.
    iMod (own_alloc (● (Some (excl.Excl NothingPending): optionUR (excl.exclR (leibnizO WritePendingState))) ⋅ ◯ (Some (excl.Excl NothingPending) : optionUR (excl.exclR (leibnizO WritePendingState))))) as (γ) "[? ?]".
    { apply auth_both_valid_2; done. }
    iModIntro. iExists (WritePendingG _ γ). now iFrame.
  Qed.

  Lemma nothingPending_written `{writePendingG Σ} e :
    nothingPending_auth ∗ nothingPending ==∗
    written_auth e ∗ written e.
  Proof.
    rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply @option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  Lemma written_nothingPending `{writePendingG Σ} e :
    written_auth e ∗ written e ==∗
    nothingPending_auth ∗ nothingPending.
  Proof.
    rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply @option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  Lemma writePending_agree `{writePendingG Σ} (s s' : WritePendingState) :
    own writePendingG_gname (● (Some (excl.Excl s) : optionUR (excl.exclR (leibnizO WritePendingState)))) -∗
    own writePendingG_gname (◯ (Some (excl.Excl s') : optionUR (excl.exclR (leibnizO WritePendingState)))) -∗
    ⌜s = s'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi _]%auth_both_valid_discrete.
    rewrite excl.Excl_included in Hi. apply leibniz_equiv in Hi. by subst.
  Qed.

  Lemma written_auth_nothingPending `{writePendingG Σ} e :
    written_auth e -∗ nothingPending -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (writePending_agree with "H1 H2") as %?.
  Qed.

  Lemma nothingPending_auth_written `{writePendingG Σ} e :
    nothingPending_auth -∗ written e -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (writePending_agree with "H1 H2") as %?.
  Qed.

  Lemma written_auth_written `{writePendingG Σ} e e' :
    written_auth e -∗ written e' -∗ ⌜e = e'⌝.
  Proof.
    iIntros "H1 H2".
    by iDestruct (writePending_agree with "H1 H2") as %[= ->].
  Qed.

  #[export] Instance nothingPending_auth_Timeless `{writePendingG Σ} :
    Timeless nothingPending_auth.
  Proof. unfold nothingPending_auth. apply _. Qed.

  #[export] Instance written_auth_Timeless `{writePendingG Σ} e :
    Timeless (written_auth e).
  Proof. unfold written_auth. apply _. Qed.


  (* Ghost state tracking whether an execution is still powered on. The
     authoritative part lives in the memory state interpretation, where it
     reflects the memory; the fragment `powered b` is owned by the program. *)
  Definition poweredΣ := #[GFunctor (authR (optionUR (excl.exclR (leibnizO bool))))].

  Class powered_preG Σ := Powered_preG {
                              powered_pre_inG :: inG Σ (auth.authR (optionUR (excl.exclR (leibnizO bool))));
                            }.

  Class poweredG Σ := PoweredG {
                          powered_inG :: inG Σ (auth.authR (optionUR (excl.exclR (leibnizO bool))));
                          poweredG_gname : gname
                        }.

  #[export] Instance poweredΣ_preG `{poweredG Σ} : powered_preG Σ.
  Proof. constructor. typeclasses eauto. Defined.

  #[export] Instance subG_poweredPreΣ {Σ}:
    subG poweredΣ Σ →
    powered_preG Σ.
  Proof. solve_inG. Qed.

  Definition powered_auth `{poweredG Σ} (b : bool) : iProp Σ :=
    own poweredG_gname (● (Some (excl.Excl b) : optionUR (excl.exclR (leibnizO bool)))).
  Definition powered `{poweredG Σ} (b : bool) : iProp Σ :=
    own poweredG_gname (◯ (Some (excl.Excl b) : optionUR (excl.exclR (leibnizO bool)))).

  Lemma powered_alloc `{!powered_preG Σ} (b : bool) :
    ⊢ |==> ∃ pG : poweredG Σ, powered_auth b ∗ powered b.
  Proof.
    iMod (own_alloc (● (Some (excl.Excl b): optionUR (excl.exclR (leibnizO bool))) ⋅ ◯ (Some (excl.Excl b) : optionUR (excl.exclR (leibnizO bool))))) as (γ) "[? ?]".
    { apply auth_both_valid_2; done. }
    iModIntro. iExists (PoweredG _ γ). now iFrame.
  Qed.

  Lemma powered_agree `{poweredG Σ} (b b' : bool) :
    powered_auth b -∗ powered b' -∗ ⌜b = b'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi _]%auth_both_valid_discrete.
    rewrite excl.Excl_included in Hi. by apply leibniz_equiv in Hi.
  Qed.

  Lemma powered_update `{poweredG Σ} (b b' : bool) :
    powered_auth b ∗ powered b ==∗ powered_auth b' ∗ powered b'.
  Proof.
    rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply @option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  #[export] Instance powered_auth_Timeless `{poweredG Σ} b :
    Timeless (powered_auth b).
  Proof. unfold powered_auth. apply _. Qed.

  (* NOTE: no resource present for current `State`, since we do not wish to reason about it for now *)
  Class mcMemGS Σ :=
    McMemGS {
        (* ghost variable for tracking state of heap *)
        mc_ghGS :: gen_heapGS Addr MemVal Σ;
        (* tracking traces *)
        mc_gtGS :: traceG Trace Σ;
        (* tracking mmio write events *)
        mc_wpGS :: writePendingG Σ;
        (* tracking the power status *)
        mc_pwGS :: poweredG Σ
      }.

  Class mcMemGS2 Σ :=
    McMemGS2 {
        (* two copies of the unary ghost variables *)
        mc_ghGS2_left : mcMemGS Σ
      ; mc_ghGS2_right : mcMemGS Σ
      }.

  Class mcMemPreGS Σ := {
      mc_ghPreGS :: gen_heapGpreS Addr MemVal Σ;
      mc_gtPreGS :: trace_preG Trace Σ;
      mc_wpPreGS :: writePending_preG Σ;
      mc_pwPreGS :: powered_preG Σ;
      }.
  #[export] Existing Instance mc_ghPreGS.
  #[export] Existing Instance mc_gtPreGS.
  #[export] Existing Instance mc_wpPreGS.
  #[export] Existing Instance mc_pwPreGS.

  Definition memGpreS : gFunctors -> Set := mcMemPreGS.
  Definition memΣ : gFunctors := #[gen_heapΣ Addr MemVal ; tracePreΣ Trace; writePendingΣ; poweredΣ ].

  Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ.
  Proof. intros. solve_inG. Defined.

  Section SharedBinaryInvariant.
    Context {Σ : gFunctors} {mG : mcMemGS2 Σ}.

    Definition femto_inv_mmio_ns : ns.namespace := (ns.ndot ns.nroot "inv_mmio").

    (* The state of a single execution w.r.t. the adversary-observable trace
       `t` that both executions agree on. Either the observable part of this
       execution's trace is exactly `t`, or this execution is ahead by exactly
       one (observable) event `e`, which is recorded in the `written` ghost
       state until both executions are resynchronized. In addition, the full
       (unfiltered) trace of each execution satisfies `mmio_pred`, which
       gives the integrity of MMIO. *)
    Definition side_inv (width : nat) (mGs : mcMemGS Σ) (t : Trace) : iProp Σ :=
      ∃ ts, @tr_frag _ _ (@mc_gtGS _ mGs) ts ∗ ⌜mmio_pred width ts⌝ ∗
              ((⌜filter_adv_observable ts = t⌝ ∗ @nothingPending_auth _ (@mc_wpGS _ mGs))
               ∨ ∃ e, ⌜filter_adv_observable ts = e :: t⌝ ∗ @written_auth _ (@mc_wpGS _ mGs) e).

    #[export] Instance side_inv_Timeless width mGs t : Timeless (side_inv width mGs t).
    Proof. unfold side_inv. apply _. Qed.

    Definition interp_inv_mmio `{invGS Σ} (width : nat) : iProp Σ :=
      inv femto_inv_mmio_ns (∃ t, side_inv width mc_ghGS2_left t ∗ side_inv width mc_ghGS2_right t).

    (* If both executions have performed the same observable write, they can
       be resynchronized: the common observable trace is extended with that
       write and both executions return to the `nothingPending` state. *)
    Lemma written_nothingPending2 `{invGS Σ} (width : nat) (e : Event) E :
      ↑femto_inv_mmio_ns ⊆ E →
      interp_inv_mmio width -∗
      @written _ (@mc_wpGS _ mc_ghGS2_left) e -∗
      @written _ (@mc_wpGS _ mc_ghGS2_right) e ={E}=∗
      @nothingPending _ (@mc_wpGS _ mc_ghGS2_left) ∗
      @nothingPending _ (@mc_wpGS _ mc_ghGS2_right).
    Proof.
      iIntros (HE) "#Hinv Hl Hr".
      iInv "Hinv" as ">(%t & (%t1 & Hf1 & %Hp1 & H1) & (%t2 & Hf2 & %Hp2 & H2))" "Hclose".
      iDestruct "H1" as "[[_ Ha1] | (%e1 & %Ht1 & Ha1)]".
      { iDestruct (nothingPending_auth_written with "Ha1 Hl") as "[]". }
      iDestruct "H2" as "[[_ Ha2] | (%e2 & %Ht2 & Ha2)]".
      { iDestruct (nothingPending_auth_written with "Ha2 Hr") as "[]". }
      iDestruct (written_auth_written with "Ha1 Hl") as %->.
      iDestruct (written_auth_written with "Ha2 Hr") as %->.
      iMod (written_nothingPending with "[$Ha1 $Hl]") as "[Ha1 $]".
      iMod (written_nothingPending with "[$Ha2 $Hr]") as "[Ha2 $]".
      iApply "Hclose". iExists (e :: t).
      iSplitL "Hf1 Ha1"; iExists _; iFrame "∗ %"; by iLeft; iFrame.
    Qed.
  End SharedBinaryInvariant.

  Section WithMemory.
    Context {Σ : gFunctors} {mG : mcMemGS Σ}.

    (* TODO: change back to words instead of bytes... might be an easier first version
             and most likely still convenient in the future *)
    Definition interp_ptsto (addr : Addr) (b : Byte) : iProp Σ :=
      pointsto addr (DfracOwn 1) b ∗ ⌜¬ withinMMIO addr 1⌝.
    Definition ptstoSth : Addr -> iProp Σ := fun a => (∃ w, interp_ptsto a w)%I.
    Definition ptstoSthL : list Addr -> iProp Σ :=
      fun addrs => ([∗ list] k↦a ∈ addrs, ptstoSth a)%I.

    Definition interp_ptstomem' {width : nat} (addr : Addr) (bytes : bv (width * byte)) : iProp Σ :=
      [∗ list] offset ∈ seq 0 width,
        interp_ptsto (addr + bv.of_nat offset) (get_byte offset bytes).
    Fixpoint interp_ptstomem {width : nat} (addr : Addr) : bv (width * byte) -> iProp Σ :=
      match width with
      | O   => fun _ => True
      | S w =>
          fun bytes =>
            let (byte, bytes) := bv.appView byte (w * byte) bytes in
            interp_ptsto addr byte ∗ interp_ptstomem (bv.one + addr) bytes
      end%I.

    (* TODO: introduce constant for nr of word bytes (replace 4) *)
    Definition interp_ptsto_instr (addr : Addr) (instr : AST) : iProp Σ :=
      (∃ v, @interp_ptstomem 4 addr v ∗ ⌜ pure_decode v = inr instr ⌝)%I.

    Fixpoint ptsto_instrs (a : Val ty_xlenbits) (instrs : list AST) : iProp Σ :=
      match instrs with
      | cons inst insts => (interp_ptsto_instr a inst ∗ ptsto_instrs (bv.add a bv_instrsize) insts)%I
      | nil => True%I
      end.
    (* Arguments ptsto_instrs {Σ H} a%_Z_scope instrs%_list_scope : simpl never. *)

    Lemma ptsto_instrs_app {a : Val ty_xlenbits} {instrs1 instrs2 : list AST} :
      ptsto_instrs a (instrs1 ++ instrs2)
        ⊣⊢ ptsto_instrs a instrs1 ∗ ptsto_instrs (bv.add a (bv.of_nat (length instrs1 * bytes_per_instr))) instrs2.
    Proof.
      iRevert (a).
      iInduction instrs1 as [|i1 instrs1]; iIntros (a); cbn; iSplit.
      - rewrite <- bv.add_of_nat_0_r. now iIntros "$".
      - rewrite <- bv.add_of_nat_0_r. now iIntros "(_ & $)".
      - iIntros "($ & H)".
        iDestruct ("IHinstrs1" with "H") as "($ & H)".
        rewrite <- bv.add_assoc.
        now rewrite bv.of_nat_add.
      - iIntros "(($ & Hinstrs1) & Hinstrs2)".
        iSpecialize ("IHinstrs1" with "[$Hinstrs1 Hinstrs2]").
        { rewrite <- bv.add_assoc. now rewrite bv.of_nat_add. }
        done.
    Qed.

  End WithMemory.

End RiscvPmpIrisBaseCommon.

Module Type LeftOrRight.

  Parameter leftOrRight : bool.
End LeftOrRight.

Module LeftOrRightLeft <: LeftOrRight.
  Definition leftOrRight := true.
End LeftOrRightLeft.

Module LeftOrRightRight <: LeftOrRight.
  Definition leftOrRight := false.
End LeftOrRightRight.

(* Instantiate the Iris framework solely using the operational semantics. At
   this point we do not commit to a set of contracts nor to a set of
   user-defined predicates. *)
Module Type RiscvPmpIrisBase (Import leftOrRight : LeftOrRight)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  <: IrisBase RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RVPCOM.
  (* Pull in the definition of the LanguageMixin and register ghost state. *)

  Section RiscvPmpIrisParams.
    Definition memGS : gFunctors -> Set := mcMemGS2.

    Definition leftOrRightInstance `{mcMemGS2 Σ} : mcMemGS Σ :=
      if leftOrRight then mc_ghGS2_left else mc_ghGS2_right.
    #[export] Existing Instance leftOrRightInstance.

    (* The ghost state of the other execution. *)
    Definition otherInstance `{mcMemGS2 Σ} : mcMemGS Σ :=
      if leftOrRight then mc_ghGS2_right else mc_ghGS2_left.

    (* View the body of the shared invariant from the perspective of this execution. *)
    Lemma inv_mmio_body_own_other `{mcMemGS2 Σ} width t :
      side_inv width mc_ghGS2_left t ∗ side_inv width mc_ghGS2_right t ⊣⊢
      side_inv width leftOrRightInstance t ∗ side_inv width otherInstance t.
    Proof.
      unfold leftOrRightInstance, otherInstance.
      destruct leftOrRight; [done | apply bi.sep_comm].
    Qed.

    Definition mem_state_interp : forall {Σ}, mcMemGS2 Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp memmap
                     ∗ ⌜ map_Forall (fun a v => memory_ram μ a = v) memmap ⌝
                     ∗ tr_auth (memory_trace μ)
                     ∗ powered_auth (fun_powered_on μ)
        )%I.

  End RiscvPmpIrisParams.

  Include IrisResources RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RVPCOM.
  Include IrisWeakestPre RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RVPCOM.
  Include IrisTotalWeakestPre RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RVPCOM.
  Include IrisTotalPartialWeakestPre RiscvPmpGlobalState RiscvPmpProgram RiscvPmpSemantics RVPCOM.

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

  (* The power status of this execution, as seen by the program. *)
  Definition powered_tok `{sg : sailGS Σ} (b : bool) : iProp Σ :=
    @powered _ (@mc_pwGS _ (@leftOrRightInstance _ sailGS_memGS)) b.

  (* The power status in the memory agrees with the power token. *)
  Lemma powered_on_agree `{sg : sailGS Σ} (μ : Memory) (b : bool) :
    mem_state_interp sailGS_memGS μ -∗ powered_tok b -∗
    ⌜fun_powered_on μ = b⌝ ∗ mem_state_interp sailGS_memGS μ ∗ powered_tok b.
  Proof.
    iIntros "(%memmap & Hgh & %Hlink & Htr & Hpw) Hp".
    iDestruct (powered_agree with "Hpw Hp") as %Hb.
    iFrame "Hp". iSplitR; first done.
    iExists memmap. iFrame "∗ %".
  Qed.

  (* One iteration of the main loop, for a machine that is powered on. *)
  Lemma semWP_fun_loop_on `{sg : sailGS Σ} (Q : Post [ctx] ty.unit) :
    powered_tok true -∗
    (powered_tok true -∗ ∀ Γ (δ : CStore Γ),
         semWP δ (call RiscvPmpProgram.step ;; call RiscvPmpProgram.loop) (λ v _, Q v [env])) -∗
    semWP env.nil (FunDef loop) Q.
  Proof.
    iIntros "Hp H". cbn [FunDef]. unfold fun_loop.
    iApply semWP_let. iApply semWP_foreign.
    iIntros (γ μ) "[Hregs Hmem]".
    iDestruct (powered_on_agree with "Hmem Hp") as "(%Hb & Hmem & Hp)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (res γ' μ' Hf). cbn in Hf. inversion Hf; subst.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "Hregs Hmem".
    rewrite semWP_val. iModIntro. cbn.
    iApply semWP_pattern_match. iApply semWP_exp. cbn. rewrite Hb.
    iSpecialize ("H" with "Hp"). iApply (semWP_mono with "[H]"); first iApply "H".
    iIntros (v δ') "HQ". destruct (env.view δ') as [δ'' ?]. by destruct (env.view δ'').
  Qed.

  (* For a machine that is powered off, the main loop ends. *)
  Lemma semWP_fun_loop_off `{sg : sailGS Σ} (Q : Post [ctx] ty.unit) :
    powered_tok false -∗
    (powered_tok false -∗ Q (inl tt) [env]) -∗
    semWP env.nil (FunDef loop) Q.
  Proof.
    iIntros "Hp H". cbn [FunDef]. unfold fun_loop.
    iApply semWP_let. iApply semWP_foreign.
    iIntros (γ μ) "[Hregs Hmem]".
    iDestruct (powered_on_agree with "Hmem Hp") as "(%Hb & Hmem & Hp)".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (res γ' μ' Hf). cbn in Hf. inversion Hf; subst.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "Hregs Hmem".
    rewrite semWP_val. iModIntro. cbn.
    iApply semWP_pattern_match. iApply semWP_exp. cbn. rewrite Hb.
    rewrite semWP_val. iModIntro. by iApply "H".
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
