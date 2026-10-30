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
     Base
     Hoare
     Bitvector
     Iris.Instance
     Iris.Base
     Syntax.Predicates
     RiscvPmp.Base
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.IrisModel
     RiscvPmp.trace
     RiscvPmp.Sig.

From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From iris.proofmode Require Import proofmode.
From stdpp Require namespaces.
Module ns := stdpp.namespaces.

Set Implicit Arguments.
Import bv.notations.

(* Module RiscvPmpIrisAdeqParameters (LOR : LeftOrRight) <: *)
(*   IrisAdeqParameters RiscvPmpGlobalState. *)
(*   (* Pull in the definition of the LanguageMixin and register ghost state. *) *)
(*   Include RiscvPmpIrisBase LOR. *)
(*   (* Make Rocq automatically pick up the mcMemGS we want (left or right one, depending on LOR) *) *)
(*   Existing Instance leftOrRightInstance. *)

(*   Definition mem_res `{hG : mcMemGS Σ} : Memory -> iProp Σ := *)
(*     fun μ => (([∗ list] a' ∈ liveAddrs, pointsto a' (DfracOwn 1) (memory_ram μ a')) ∗ *)
(*              tr_frag1 (memory_trace μ) ∗ *)
(*              nothingPending *)
(*           )%I. *)

(*   Lemma initMemMap_works μ : map_Forall (λ (a : Addr) (v : MemVal), memory_ram μ a = v) (initMemMap μ). *)
(*   Proof. *)
(*     unfold initMemMap. *)
(*     rewrite map_Forall_to_list. *)
(*     rewrite Forall_forall. *)
(*     intros (a , v). *)
(*     rewrite elem_of_map_to_list. *)
(*     intros el. *)
(*     apply elem_of_list_to_map_2 in el. *)
(*     apply elem_of_list_In in el. *)
(*     apply in_map_iff in el. *)
(*     by destruct el as (a' & <- & _). *)
(*   Qed. *)

(*   Lemma big_sepM_list_to_map {Σ} {A B : Type} `{Countable A} {l : list A} {f : A -> B} (F : A -> B -> iProp Σ) : *)
(*     NoDup l -> *)
(*     ([∗ map] l↦v ∈ (list_to_map (map (λ a : A, (a, f a)) l)), F l v) *)
(*       ⊢ *)
(*       [∗ list] v ∈ l, F v (f v). *)
(*   Proof. *)
(*     intros ndl. *)
(*     induction ndl. *)
(*     - now iIntros "_". *)
(*     - cbn. *)
(*       rewrite big_sepM_insert. *)
(*       + iIntros "[$ Hrest]". *)
(*         now iApply IHndl. *)
(*       + apply not_elem_of_list_to_map_1. *)
(*         change (fmap fst ?l) with (map fst l). *)
(*         now rewrite map_map map_id. *)
(*   Qed. *)

(* End RiscvPmpIrisAdeqParameters. *)

Module Type RiscvPmpIrisInstancePredicates (LOR : LeftOrRight)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (Import RVPBASE : RiscvPmpIrisBase LOR RVPCOM).
  Import RiscvPmpProgram.

  Lemma difference_commute_gset {A} `{Countable A} (X Y Z : gset A) :
    (X ∖ Y) ∖ Z = (X ∖ Z) ∖ Y.
  Proof.
    apply set_eq.
    intros x.
    rewrite ?elem_of_difference.
    split.
    - intros ([HX HY] & HZ).
      repeat split; auto.
    - intros ([HX HZ] & HY).
      repeat split; auto.
  Qed.

  Lemma list_to_set_subseteq : ∀ {A : Type} {HEqDecision : EqDecision A}
                                 {HCountable : Countable A} (l1 l2 : list A),
      (list_to_set l1 : gset A) ⊆ list_to_set l2 <-> l1 ⊆ l2.
  Proof.
    intros ? ? ? l1 l2.
    rewrite ?elem_of_subseteq.
    split; intros Hl e He.
    - rewrite <- (@elem_of_list_to_set _ (gset _) _ _ _ _ _).
      rewrite <- (@elem_of_list_to_set _ (gset _) _ _ _ _ _) in He.
      now apply Hl.
    - apply elem_of_list_to_set.
      apply elem_of_list_to_set in He. auto.
  Qed.

  Lemma list_to_set_cons_subseteq {A : Type} `{Countable A} (y : A) (Y : list A) (X : gset A) :
    NoDup (y :: Y) ->
    list_to_set (y :: Y) ⊆ X -> list_to_set Y ⊆ (X ∖ {[y]}).
  Proof.
    intros Hdup Hsub.
    remember Hdup as HyY. clear HeqHyY.
    rewrite NoDup_cons in HyY.
    destruct HyY as [Hy HY].
    cbn in Hsub.
    rewrite union_subseteq in Hsub.
    destruct Hsub as [HyX Hsub].
    intros x Hx.
    apply elem_of_difference; split.
    - now apply Hsub.
    - intros Helem.
      apply elem_of_singleton in Helem; subst.
      rewrite elem_of_list_to_set in Hx.
      contradiction.
  Qed.

  Lemma big_sepS_delete_multi_list :
    ∀ {Σ} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → iProp Σ)
      (X : gset A) (Y : list A),
      NoDup Y ->
      list_to_set Y ⊆ X ->
      ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ list] y ∈ Y, Φ y) ∗ ([∗ set] x ∈ (X ∖ list_to_set Y), Φ x).
  Proof.
    intros ? ? ? ? Φ X Y.
    revert X.
    iInduction Y as [|y Y] "IH";
      iIntros (X Hdup Hsub).
    - cbn. rewrite difference_empty_L.
      iSplit.
      iIntros "$".
      iIntros "(_ & $)".
    - iSplit.
      + iIntros "H".
        remember Hsub as Hsub' eqn:Heq. clear Heq.
        cbn in Hsub.
        rewrite union_subseteq in Hsub.
        destruct Hsub as (Hy & Hsub).
        rewrite <- elem_of_subseteq_singleton in Hy.
        cbn.
        iPoseProof (big_sepS_delete _ _ y Hy with "H") as "($ & H)".
        rewrite <- difference_difference_l_L.
        apply list_to_set_cons_subseteq in Hsub'; auto.
        apply NoDup_cons in Hdup. destruct Hdup as [HyY Hdup].
        iSpecialize ("IH" $! (X ∖ {[ y ]}) Hdup Hsub').
        now iApply "IH".
      + iIntros "(HY & HX)".
        cbn. iDestruct "HY" as "(Hy & HY)".
        rewrite <- difference_difference_l_L.
        rewrite difference_commute_gset.
        iPoseProof (@big_sepS_delete_2 _ _ _ _ _ _ _ with "Hy HX") as "H".
        apply NoDup_cons in Hdup.
        destruct Hdup as [HyY Hdup].
        cbn in Hsub. rewrite union_subseteq in Hsub.
        destruct Hsub as [HyX Hsub].
        iApply ("IH" $! _ Hdup Hsub).
        iFrame "HY H".
  Qed.

  Lemma big_sepS_delete_multi :
    ∀ {Σ} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → iProp Σ)
      (X : gset A) (Y : gset A),
      Y ⊆ X ->
      ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ set] y ∈ Y, Φ y) ∗ ([∗ set] x ∈ (X ∖ Y), Φ x).
  Proof.
    intros ? ? ? ? Φ X Y Hsub.
    remember (elements Y) as l eqn:El.
    assert (Hdup: NoDup l) by (subst; apply NoDup_elements).
    assert (Hl: list_to_set l = Y) by (subst; apply list_to_set_elements_L).
    assert (Hsub': list_to_set l ⊆ X) by (now rewrite Hl).
    iSplit.
    - iIntros "H".
      iPoseProof (big_sepS_delete_multi_list _ Hdup Hsub' with "H") as "H".
      rewrite Hl. iDestruct "H" as "(H & $)".
      rewrite <- Hl.
      now iApply big_sepS_list_to_set.
    - iIntros "(HY & HX)".
      iApply (big_sepS_delete_multi_list _ Hdup Hsub').
      rewrite Hl. iFrame "HX".
      rewrite <- Hl.
      now iApply big_sepS_list_to_set.
  Qed.

  Lemma NoDup_reg_convert_to_idx (l : list (Reg ty_xlenbits)) :
    NoDup l ->
    NoDup (omap reg_convert_to_idx l).
  Proof.
    induction l as [|r l IH]; cbn; intros Hdup; try constructor.
    apply NoDup_cons in Hdup. destruct Hdup as [Hr Hdup].
    specialize (IH Hdup).
    destruct (reg_convert_to_idx r) as [rid|] eqn:E; auto.
    apply NoDup_cons. split; auto.
    intros Helem.
    apply list_elem_of_omap in Helem.
    destruct Helem as (? & Hin & Heq).
    pose proof (reg_convert_to_idx_Some_inj _ _ E Heq) as ?; subst.
    apply (Hr Hin).
  Qed.

  Section WithMemory.
    Context {Σ : gFunctors} {mG : mcMemGS Σ}.

    Definition femto_inv_mmio_ns : ns.namespace := (ns.ndot ns.nroot "inv_mmio").
    (* Definition interp_inv_mmio `{invGS Σ} (width : nat) : iProp Σ := *)
    (*   inv femto_inv_mmio_ns (∃ t, tr_frag1 t ∗ ⌜mmio_pred width t⌝). *)

    Definition femto_inv_ro_ns : ns.namespace := (ns.ndot ns.nroot "inv_ro").
    Definition interp_ptstomem_readonly `{invGS Σ} {width : nat} (addr : Addr) (b : bv (width * byte)) : iProp Σ :=
      inv femto_inv_ro_ns (interp_ptstomem addr b).

    (* NOTE: no read predicate yet, as we will not perform nor allow MMIO reads. *)
    (* NOTE: no local state yet, but this should be an iProp for the general case *)
    Definition interp_mmio_checked_write {width : nat} (addr : Addr) (bytes : bv (width * byte)) : iProp Σ :=
      ⌜addr = write_addr⌝ (* Allow arbitrary write values for M-mode only address *)
      ∨ ⌜addr = write_addr_adv ∧ bytes = (bv.of_N 42)⌝ (* When writing to an MMIO address that is observable by the adv, we only allow 42 to be written. *)
      ∨ ⌜addr = mmioShutdownAddr⌝. (* Powering off the machine, with an arbitrary exit value *)

    Section WithAddrs.
      Variable (live_addrs mmio_addrs : list Addr).

      (* Universal contract for single byte/`width` bytes after PMP checks *)
      Definition interp_addr_access_byte (a : Addr) : iProp Σ :=
        if decide (a ∈ mmio_addrs) then False%I (* Creates a proof obligation that the adversary cannot access MMIO. TODO: Change this to a trace filter to grant the adversary access to MMIO *)
        else if decide (a ∈ live_addrs) then ptstoSth a
             else True%I. (* Could be `False` as well *)
      Definition interp_addr_access (base : Addr) (width : nat): iProp Σ :=
        [∗ list] a ∈ bv.seq base (Z.of_nat width), interp_addr_access_byte a.

      Definition interp_pmp_addr_access (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
        [∗ list] a ∈ all_addrs,
          (⌜∃ p, Pmp_access a (bv.of_nat 1) entries m p⌝ -∗ interp_addr_access_byte a)%I.

      Lemma interp_pmp_addr_access_s_u_eq (entries : list PmpEntryCfg) :
        interp_pmp_addr_access entries User ⊣⊢ interp_pmp_addr_access entries Supervisor.
      Proof.
        iSplit; iApply big_sepL_mono; iIntros (k addr Hk) "H [%p %Hpmp]";
          iApply "H"; iExists p; iPureIntro; unfold Pmp_access, Gen_Pmp_access in *.
        - now rewrite pmp_check_aux_s_u_eq.
        - now rewrite pmp_check_aux_s_u_eq in Hpmp.
      Qed.

      Lemma interp_pmp_addr_access_not_machine (entries : list PmpEntryCfg) (m m' : Privilege) :
        m ≠ Machine -> m' ≠ Machine ->
        interp_pmp_addr_access entries m ⊢ interp_pmp_addr_access entries m'.
      Proof.
        intros Hm Hm'; destruct m, m'; try congruence;
          by rewrite ?interp_pmp_addr_access_s_u_eq.
      Qed.

      Definition interp_pmp_addr_access_without (addr : Addr) (width : nat)  (entries : list PmpEntryCfg) (m : Privilege) : iProp Σ :=
        (@interp_addr_access addr width -∗ interp_pmp_addr_access entries m)%I.
    End WithAddrs.
  End WithMemory.

  Section WithSailGS.
    Context `{sailRegGS Σ} `{invGS Σ}.

    Definition interp_gprs (exclude : gset (Reg ty_xlenbits)) : iProp Σ :=
      [∗ set] r ∈ GPRS ∖ exclude,
        (∃ v, reg_pointsTo r v)%I.

    Lemma list_to_set_list_difference : ∀ {A : Type} `{Countable A} (l1 l2 : list A),
      (list_to_set (list_difference l1 l2) : gset A) = list_to_set l1 ∖ list_to_set l2.
    Proof.
      intros ? ? ? l1 l2. apply set_eq. revert l2.
      induction l1 as [|e1 l1 IHl1];
        intros l2 e; simpl; split; intros He.
      - inversion He.
      - apply elem_of_difference in He.
        now destruct He as [He _].
      - case_match.
        + rewrite difference_union_distr_l_L.
          apply elem_of_union_r.
          now apply IHl1.
        + cbn in *.
          rewrite difference_union_distr_l_L.
          apply elem_of_union in He.
          destruct He as [He|He].
          * apply elem_of_union_l.
            apply elem_of_difference.
            split; auto.
            rewrite elem_of_list_to_set.
            apply elem_of_singleton in He.
            now subst.
          * apply elem_of_union_r.
            now apply IHl1.
      - rewrite elem_of_difference in He.
        destruct He as [Hl1 Hl2].
        case_match.
        + apply IHl1.
          apply elem_of_union in Hl1.
          destruct Hl1 as [He|He].
          * apply elem_of_singleton in He. subst.
            rewrite elem_of_list_to_set in Hl2. contradiction.
          * now apply elem_of_difference.
        + simpl. apply elem_of_union.
          apply elem_of_union in Hl1.
          destruct Hl1 as [He|He].
          * now left.
          * right. apply IHl1.
            now apply elem_of_difference.
    Qed.

    Lemma interp_gprs_with_excluded_gen `{sailGS Σ} (exclude1 exclude2 : gset (Reg ty_xlenbits)) :
      exclude2 ⊆ GPRS ∖ exclude1 ->
      ([∗ set] r ∈ exclude2, ∃ v, reg_pointsTo r v) ∗ interp_gprs (exclude1 ∪ exclude2) ⊣⊢ interp_gprs exclude1.
    Proof.
      intros Hsub1.
      unfold interp_gprs.
      iApply bi.wand_iff_sym.
      rewrite <- difference_difference_l_L.
      now iApply big_sepS_delete_multi.
    Qed.

    Lemma interp_gprs_with_excluded `{sailGS Σ} (exclude : gset (Reg ty_xlenbits)) :
      exclude ⊆ GPRS ->
      ([∗ set] r ∈ exclude, ∃ v, reg_pointsTo r v) ∗ interp_gprs exclude ⊣⊢ interp_gprs ∅.
    Proof.
      intros Hsub.
      rewrite <- union_empty_l_L at 2.
      now iApply interp_gprs_with_excluded_gen.
    Qed.

    Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits.

    Definition interp_pmp_entries (entries : list PmpEntryCfg) : iProp Σ :=
      match entries with
      | (cfg0, addr0) :: (cfg1, addr1) :: [] =>
          reg_pointsTo pmp0cfg cfg0 ∗
          reg_pointsTo pmpaddr0 addr0 ∗
          reg_pointsTo pmp1cfg cfg1 ∗
          reg_pointsTo pmpaddr1 addr1
      | _ => False
      end.
  End WithSailGS.
End RiscvPmpIrisInstancePredicates.

Module Type RiscvPmpIrisInstance (LOR : LeftOrRight)
  (Import RVPCOM : RiscvPmpIrisBaseCommon)
  (Import RVPBASE : RiscvPmpIrisBase LOR RVPCOM)
  (Import RVPPRED : RiscvPmpIrisInstancePredicates LOR RVPCOM RVPBASE)
<: IrisInstance RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram RiscvPmpSemantics RiscvPmpProgramLogic RVPCOM RVPBASE.

  Import RiscvPmpProgram.

  #[global] Notation "a '↦ₘ' t" := (interp_ptsto a t) (at level 70).

  Section RiscvPmpIrisPredicates.
    Context `{sr : sailRegGS Σ} `{igs : invGS Σ} `{mG2 : memGS Σ}.

    (* why is this not imported? *)
    Definition mG2Alias := (mG2 : mcMemGS2 Σ).
    Existing Instance mG2Alias.

    Import env.notations.

    (* We don't need additional ghost state beyond what we already have for the WP. *)
    Definition resGS := trivGS.

    Equations(noeqns) luser_inst {rG : trivGS Σ}
      (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | pmp_entries              | [ v ]                => interp_pmp_entries v
    | pmp_addr_access          | [ entries; m ]       => interp_pmp_addr_access liveAddrs mmioAddrs entries m
    | pmp_addr_access_without bytes | [ addr; entries; m ] => interp_pmp_addr_access_without liveAddrs mmioAddrs addr bytes entries m
    | gprs                     | _                    => interp_gprs ∅ (* For the Universal Contract verification we always need all GPRs, hence the empty exclude list *)
    | ptsto                    | [ addr; w ]          => interp_ptsto addr w
    | ptsto_one _              | [ addr; w ]          => False (* Unary instance has no support for different execution predicates *)
    | ptstomem_readonly _      | [ addr; w ]          => interp_ptstomem_readonly addr w
    | inv_mmio bytes           | _                    => @interp_inv_mmio _ mG2  _ bytes
    | mmio_checked_write _     | [ addr; w ]          => interp_mmio_checked_write addr w
    | encodes_instr            | [ code; instr ]      => ⌜ pure_decode code = inr instr ⌝%I
    | ptstomem _               | [ addr; bs]          => interp_ptstomem addr bs
    | ptstoinstr               | [ addr; instr ]      => interp_ptsto_instr addr instr
    | Sig.nothingPending           | _                => nothingPending
    | Sig.written width        | [ addr; val ]        => written (mkEvent IOWrite addr width val)
    | Sig.written_shutdown width | [ addr; val ]      => written (mkEvent IOShutdown addr width val)
    | Sig.powered              | [ b ]                => powered b
    .

    Ltac destruct_pmp_entries :=
      repeat match goal with
        | x : Val ty_pmpentry |- _ =>
            destruct x; auto
        | x : Val (ty.list ty_pmpentry) |- _ =>
            destruct x; auto
        | x : list (Val ty_pmpentry) |- _ =>
            destruct x; auto
        end.

    Definition lduplicate_inst {rG : trivGS Σ} :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst p ts) ⊢ (luser_inst p ts ∗ luser_inst p ts).
    Proof.
      destruct p; intros ts Heq; try discriminate Heq;
        clear Heq; cbn in *; env.destroy ts; cbn; destruct_pmp_entries; auto.
    Qed.

  End RiscvPmpIrisPredicates.

  Section RiscVPmpIrisInstanceProofs.
    Context `{sr : sailGS Σ}.

    Local Lemma to_nat_mono (a b : N) : (a < b)%N → N.to_nat a < N.to_nat b.
    Proof. lia. Qed.

    Lemma ptstoSthL_app {l1 l2} : (ptstoSthL (l1 ++ l2) ⊣⊢ ptstoSthL l1 ∗ ptstoSthL l2)%I.
    Proof. eapply big_sepL_app. Qed.

    Lemma ptstomem_bv_app :
      forall {n} (a : Addr) (b : bv byte) (bs : bv (n * byte)),
        @interp_ptstomem _ _ (S n)%nat a (bv.app b bs)
          ⊣⊢
          (interp_ptsto a b ∗ interp_ptstomem (bv.one + a) bs).
    Proof. intros; cbn [interp_ptstomem]; now rewrite bv.appView_app. Qed.

    Lemma pmp_entries_ptsto : ∀ (entries : list PmpEntryCfg),
        interp_pmp_entries entries ⊣⊢
          ∃ (cfg0 : Pmpcfg_ent) (addr0 : Addr) (cfg1 : Pmpcfg_ent) (addr1 : Addr),
            ⌜entries = [(cfg0, addr0); (cfg1, addr1)]⌝ ∗
                         reg_pointsTo pmp0cfg cfg0 ∗ reg_pointsTo pmpaddr0 addr0 ∗
                         reg_pointsTo pmp1cfg cfg1 ∗ reg_pointsTo pmpaddr1 addr1.
    Proof.
      intros entries; iSplit; iIntros  "H".
      - unfold interp_pmp_entries.
        destruct entries as [|[cfg0 addr0] [|[cfg1 addr1] [|]]] eqn:?; try done.
        repeat iExists _.
        now iFrame.
      -  iDestruct "H" as "(% & % & % & % & -> & ? & ? & ? & ?)"; iFrame.
    Qed.

    Lemma interp_ptstomem_exists_intro (bytes : nat) :
      ⊢ ∀ (paddr : Addr) (w : bv (bytes * byte)),
          interp_ptstomem paddr w -∗
                                     ∃ (w : bv (bytes * byte)), interp_ptstomem paddr w.
    Proof. auto. Qed.

    Lemma interp_ptstomem_big_sepS (bytes : nat) (paddr : Addr):
      (∃ (w : bv (bytes * byte)), interp_ptstomem paddr w) ⊣⊢
        ptstoSthL (bv.seq paddr (Z.of_nat bytes)).
    Proof.
      generalize dependent paddr.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr).
      - unfold ptstoSthL. unshelve auto. exact bv.zero.
      - rewrite Nat2Z.inj_succ bv.seq_succ; last lia.
        rewrite (app_comm_cons []) ptstoSthL_app.
        iDestruct ("IHbytes" $! (bv.one + paddr)) as "[IHL IHR]".
        iSplit.
        *  iIntros "[%w H]".
           destruct (bv.appView byte (bytes * byte) w) as [b bs].
           rewrite ptstomem_bv_app.
           iDestruct "H" as "[Hb Hbs]".
           iSplitL "Hb".
        + cbn. iSplit; [by iExists _ | auto].
        + iApply "IHL"; by iExists _.
          * iIntros "[[[%b Hhd] _] Htl]".
            iDestruct ("IHR" with "Htl") as "[%btl Htl]".
            iExists (bv.app b btl).
            rewrite ptstomem_bv_app. iFrame.
    Qed.

    Lemma fun_read_ram_works {bytes memmap μ paddr} {w : bv (bytes * byte)} :
      map_Forall (λ (a : Addr) (v : Base.Byte), memory_ram μ a = v) memmap ->
      interp_ptstomem paddr w ∗ gen_heap.gen_heap_interp memmap ⊢
        ⌜ fun_read_ram μ bytes paddr = w ⌝.
    Proof.
      revert paddr.
      iInduction bytes as [|bytes] "IHbytes";
        iIntros (paddr Hmap) "[Haddr Hmem]".
      - now destruct (bv.view w).
      - destruct (bv.appView byte (bytes * byte) w) as (w0 & w).
        rewrite ptstomem_bv_app.
        iDestruct "Haddr" as "([Haddr0 HnotM] & Haddr)".
        iPoseProof (gen_heap.gen_heap_valid with "Hmem Haddr0") as "%".
        iPoseProof ("IHbytes" $! w (bv.one + paddr) Hmap with "[$Haddr $Hmem]") as "%eq".
        iPureIntro.
        simpl.
        f_equal; auto.
    Qed.

    Lemma mem_state_interp_not_modified `{sailGS Σ} :
      ∀ (μ : Memory) (memmap : gmap Addr MemVal),
        ⊢ ⌜map_Forall (λ (a : Addr) (v : Byte), memory_ram μ a = v) memmap⌝ -∗
                                                                               gen_heap.gen_heap_interp memmap -∗
                                                                                                                  trace.tr_auth (memory_trace μ) -∗
                                                                                                                                                    powered_auth (fun_powered_on μ) -∗
                                                                                                                                                    mem_state_interp sailGS_memGS μ.
    Proof. iIntros (μ memmap) "Hmap Hmem Htr Hpw"; iExists memmap; now iFrame. Qed.

    Lemma map_Forall_update : ∀ (μ : Memory) (memmap : gmap Addr MemVal)
                                (paddr : Addr) (data : Byte),
        map_Forall (λ (a : Addr) (v : Byte), memory_ram μ a = v) memmap ->
        map_Forall (λ (a : Addr) (v : Byte), write_byte (memory_ram μ) paddr data a = v) (<[paddr:=data]> memmap).
    Proof.
      intros μ memmap paddr data Hmap.
      apply map_Forall_lookup.
      intros i x H0.
      unfold write_byte.
      destruct Classes.eq_dec.
      - subst paddr.
        now apply (lookup_insert_rev memmap i).
      - rewrite -> map_Forall_lookup in Hmap.
        rewrite (lookup_insert_ne _ _ _ _ n) in H0.
        now apply Hmap.
    Qed.

    Lemma fun_write_ram_works μ bytes paddr data memmap {w : bv (bytes * byte)} :
      map_Forall (λ (a : Addr) (v : Base.Byte), (memory_ram μ) a = v) memmap ->
      interp_ptstomem paddr w ∗ gen_heap.gen_heap_interp memmap ∗
        trace.tr_auth (memory_trace μ) ∗ powered_auth (fun_powered_on μ) ={⊤}=∗
      mem_state_interp sailGS_memGS (fun_write_ram μ bytes paddr data) ∗ interp_ptstomem paddr data.
    Proof.
      iRevert (data w paddr μ memmap).
      iInduction bytes as [|bytes] "IHbytes"; cbn [fun_write_ram interp_ptstomem];
        iIntros (data w paddr μ memmap Hmap) "(Haddr & Hmem & Htr & Hpw)".
      - iModIntro. iSplitL; last done.
        now iApply (mem_state_interp_not_modified $! Hmap with "Hmem Htr Hpw").
     -  change (bv.appView _ _ data) with (bv.appView byte (bytes * byte) data).
        destruct (bv.appView byte (bytes * byte) data) as [bd data].
        destruct (bv.appView byte (bytes * byte) w) as [bw w].
        iDestruct "Haddr" as "[[H $] Haddr]".
        iMod (gen_heap.gen_heap_update _ _ _ bd with "Hmem H") as "[Hmem $]".
        iApply ("IHbytes" $! data w
                       (bv.add bv.one paddr) (memory_update_ram μ (write_byte (memory_ram μ) paddr bd))
                    (insert paddr bd memmap) with "[%] [$Haddr $Hmem $Htr $Hpw]").
        by apply map_Forall_update.
    Qed.

    Lemma interp_addr_access_app base width width':
      interp_addr_access liveAddrs mmioAddrs base (width + width') ⊣⊢
        interp_addr_access liveAddrs mmioAddrs base width ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat width) width'.
    Proof.
      unfold interp_addr_access.
      rewrite Nat2Z.inj_add bv.seq_add ?bv.of_Z_nat ?big_sepL_app //; lia.
    Qed.

    Lemma interp_addr_access_cons base width:
      interp_addr_access liveAddrs mmioAddrs base (S width) ⊣⊢
        interp_addr_access_byte liveAddrs mmioAddrs base ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat 1) width.
    Proof. rewrite <-Nat.add_1_l.
           rewrite interp_addr_access_app.
           unfold interp_addr_access, interp_addr_access_byte.
           by rewrite bv.seq_one big_sepL_singleton.
    Qed.

    Lemma interp_addr_access_single base:
      interp_addr_access liveAddrs mmioAddrs base 1 ⊣⊢
        interp_addr_access_byte liveAddrs mmioAddrs base.
    Proof. rewrite interp_addr_access_cons.
           iSplit; iIntros "H"; [iDestruct "H" as "[H _]"|]; iFrame.
           unfold interp_addr_access. now cbn.
    Qed.

    (* Induction does not work here due to shape of `interp_pmp_addr_access_without`*)
    Lemma interp_pmp_addr_inj_extr {entries m p} base width :
      (bv.unsigned base + Z.of_nat width < 2 ^ Z.of_nat xlenbits)%Z →
      Pmp_access base (bv.of_nat width) entries m p →
      (interp_pmp_addr_access liveAddrs mmioAddrs entries m ⊣⊢
         (interp_addr_access liveAddrs mmioAddrs base width ∗ interp_pmp_addr_access_without liveAddrs mmioAddrs base width entries m))%I.
    Proof.
      intros Hrep Hpmp.
      (* Discharge easy direction *)
      iSplit ; last (iIntros "[H Hcont]"; by iApply "Hcont").
      unfold interp_pmp_addr_access_without, interp_pmp_addr_access.
      (* Hard direction: create `interp_addr_access` from scratch *)
      unfold interp_pmp_addr_access.
      pose proof (in_allAddrs_split base width Hrep) as [l1 [l2 Hall]]. rewrite Hall.
      rewrite !big_sepL_app.
      iIntros "(Hlow & Hia & Hhigh)".
      iSplitL "Hia".
      - iApply (big_sepL_mono with "Hia"). iIntros (? ? ?) "Hyp".
        iApply "Hyp". iPureIntro.
        eexists; eapply pmp_seq_restrict; eauto.
      - iIntros "Hia". iFrame.
        iDestruct (big_sepL_mono with "Hia") as "Hia"; last iFrame.
        now iIntros.
    Qed.

    Lemma interp_pmp_within_mmio_spec {entries m p} (paddr : Addr) bytes :
      (bv.unsigned paddr + Z.of_nat bytes < 2 ^ Z.of_nat xlenbits)%Z ->
      Pmp_access paddr (bv.of_nat bytes) entries m p →
      interp_pmp_addr_access liveAddrs mmioAddrs entries m -∗
                                                              ⌜bool_decide (withinMMIO paddr bytes) = false%nat⌝.
    Proof.
      iIntros (Hrep Hpmp) "Hint".
      destruct bytes as [|bytes]. (* No induction needed: disproving one location suffices. *)
      - rewrite bool_decide_eq_false. iPureIntro. intros [? _]. lia.
      - rewrite interp_pmp_addr_inj_extr; eauto.
        iDestruct "Hint" as "[Hint _]".
        iDestruct (interp_addr_access_cons with "Hint") as "[Hfirst _]".
        unfold interp_addr_access_byte.
        case_decide; auto.
        iPureIntro.
        rewrite bool_decide_eq_false. intros ?%withinMMIO_elem_of_base.
        congruence.
    Qed.

    (* Bidirectional version of the Iris lemma *)
    Lemma big_sepL_mono_iff {PROP : bi} {A : Type} (Φ Ψ : nat → A → PROP) (l : list A) :
      (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
      ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ [∗ list] k ↦ y ∈ l, Ψ k y.
    Proof.
      intros Hiff.
      iSplit; iApply big_sepL_mono; iIntros; iApply Hiff; auto.
    Qed.

    (* Use knowledge of RAM to extract byte *)
    Lemma interp_addr_access_byte_extr  base :
      base ∈ liveAddrs ->
      (interp_addr_access_byte liveAddrs mmioAddrs base ⊢
         ptstoSth base).
    Proof.
      intros (* Hpmp *) Hlive.
      unfold interp_addr_access_byte, ptstoSth, interp_ptsto.
      repeat case_decide; auto; iIntros; by exfalso.
    Qed.

    (* Inserting a byte is always possible *)
    Lemma interp_addr_access_byte_inj base :
      ptstoSth base -∗ interp_addr_access_byte liveAddrs mmioAddrs base.
    Proof.
      unfold interp_addr_access_byte, ptstoSth, interp_ptsto.
      iIntros "HFalse". iDestruct "HFalse" as (?) "[Hmapsto %HFalse]".
      case_decide.
      - by rewrite withinMMIO_one in HFalse.
      - case_decide; auto.
    Qed.

    (* Use knowledge of RAM to extract range *)
    Lemma interp_addr_access_extr base width :
      (Z.of_N minAddr ≤ bv.unsigned base)%Z →
      (bv.unsigned base + Z.of_nat width ≤ Z.of_N maxAddr)%Z →
      (bv.unsigned base + Z.of_nat width < 2 ^ Z.of_nat xlenbits)%Z →
      interp_addr_access liveAddrs mmioAddrs base width ⊢
        (∃ (w : bv (width * byte)), interp_ptstomem base w).
    Proof.
      intros HminOK HmaxOK Hrep.
      rewrite interp_ptstomem_big_sepS.
      unfold interp_addr_access, ptstoSthL.
      iApply big_sepL_mono.
      iIntros (? y Hseq) "//".
      iApply interp_addr_access_byte_extr.
      eapply bv.seq_subseteq, list_elem_of_lookup_2, Hseq; unfold maxAddr in *;
        change (bv.unsigned (bv.of_N minAddr)) with (Z.of_N minAddr); lia.
    Qed.

    (* Inserting a range is always possible *)
    Lemma interp_addr_access_inj base width:
      (∃ (w : bv (width * byte)), interp_ptstomem base w) ⊢
        interp_addr_access liveAddrs mmioAddrs base width.
    Proof.
      iIntros "Hint".
      rewrite interp_ptstomem_big_sepS.
      unfold interp_addr_access, ptstoSthL.
      iApply big_sepL_mono; last auto.
      iIntros (? y Hseq) "/=".
      iApply interp_addr_access_byte_inj.
    Qed.

    (* TODO: This lemma is not a special case of the above, because of strange semantics of `Pmp_access`*)
    Lemma interp_pmp_addr_access_without_0 {entries m} base :
      interp_pmp_addr_access liveAddrs mmioAddrs entries m ⊣⊢ interp_pmp_addr_access_without liveAddrs mmioAddrs base 0 entries m.
    Proof. unfold interp_pmp_addr_access_without, interp_addr_access.
           iSplit; iIntros "H".
           - now iIntros "_".
           - now iApply "H".
    Qed.

  End RiscVPmpIrisInstanceProofs.


  Include IrisSignatureRules RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram
    RiscvPmpSemantics RiscvPmpProgramLogic RVPCOM RVPBASE.
  (* Include IrisAdequacy RiscvPmpGlobalState RiscvPmpSignature RiscvPmpProgram *)
  (*   RiscvPmpSemantics RiscvPmpProgramLogic RiscvPmpIrisBase RiscvPmpIrisAdeqParameters. *)

  Lemma gprs_equiv `{sailGS Σ} : ∀ {Σ} (ι : Valuation Σ) (exclude : gset (Reg ty_xlenbits)),
      interp_gprs exclude ⊣⊢
        asn.interpret (asn_regs_ptsto exclude) ι.
  Proof.
    iIntros (? ι exclude).
    unfold interp_gprs, asn_regs_ptsto, asn_and_regs.
    remember (elements (GPRS ∖ exclude)) as l eqn:El.
    assert (Hdup: NoDup l) by (subst; apply NoDup_elements).
    assert (Hl: list_to_set l = GPRS ∖ exclude) by (subst; apply list_to_set_elements_L).
    rewrite <- Hl.
    rewrite big_sepS_list_to_set; last auto.
    clear El Hdup Hl.
    iInduction l as [|gpr gprs] "IH";
      iSplit; iIntros "H"; simpl; auto.
    - iDestruct "H" as "($ & H)".
      now iApply ("IH" with "H").
    - iDestruct "H" as "($ & H)".
      now iApply ("IH" with "H").
  Qed.

End RiscvPmpIrisInstance.

(* Module Type RiscvPmpIrisInstancesOwner. *)
(*   Module RiscvPmpIrisInstanceOwnerLeft := RiscvPmpIrisInstanceOwner LeftOrRightLeft. *)
(*   Module RiscvPmpIrisInstancePredicatesLeft := RiscvPmpIrisInstanceOwnerLeft.RiscvPmpIrisInstancePredicatesLOR. *)
(*   Module RiscvPmpIrisBaseLeft := RiscvPmpIrisInstanceOwnerLeft.RiscvPmpIrisBaseLOR. *)
(*   Module RiscvPmpIrisInstanceLeft := RiscvPmpIrisInstanceOwnerLeft.RiscvPmpIrisInstance. *)

(*   Module RiscvPmpIrisInstanceOwnerRight := RiscvPmpIrisInstanceOwner LeftOrRightRight. *)
(*   Module RiscvPmpIrisInstancePredicatesRight := RiscvPmpIrisInstanceOwnerRight.RiscvPmpIrisInstancePredicatesLOR. *)
(*   Module RiscvPmpIrisBaseRight := RiscvPmpIrisInstanceOwnerRight.RiscvPmpIrisBaseLOR. *)
(*   Module RiscvPmpIrisInstanceRight := RiscvPmpIrisInstanceOwnerRight.RiscvPmpIrisInstance. *)
(* End RiscvPmpIrisInstancesOwner. *)

