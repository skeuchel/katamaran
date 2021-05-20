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

From Coq Require Import
     Bool.Bool
     Program.Equality
     Program.Tactics
     ZArith.ZArith
     Strings.String
     Classes.Morphisms
     Classes.RelationClasses
     Classes.Morphisms_Prop
     Classes.Morphisms_Relations.
Require Import Basics.

From Coq Require Lists.List.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Sep.Logic
     Sep.Hoare
     Syntax
     Tactics
     Symbolic.Mutator.
From MicroSail Require Import
     SemiConcrete.Mutator
     SemiConcrete.Outcome
     SemiConcrete.Sound.

Set Implicit Arguments.

Import CtxNotations.
Import EnvNotations.

Module Soundness
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit)
       (Import contractkit : SymbolicContractKit termkit progkit assertkit).
  Module MUT := Mutators termkit progkit assertkit contractkit.
  Import MUT.
  Module LOG := ProgramLogic termkit progkit assertkit contractkit.
  Import LOG.
  Module SCMUT := SemiConcrete.Sound.Soundness termkit progkit assertkit contractkit.
  Import SCMUT.
  Import SCMUT.MUT.

  Import Path.

  (* Global Instance InstSMutResult {AT A} `{Inst AT A} {Γ} : Inst (SMutResult Γ AT) (CMutResult Γ A) := *)
  (*   {| inst Σ '(MkSMutResult a δ h) ι := MkCMutResult (inst a ι) (inst δ ι) (inst h ι); *)
  (*      lift Σ '(MkCMutResult a δ h) := MkSMutResult (lift a) (lift δ) (lift h); *)
  (*   |}. *)

  (* Global Instance InstLawsSMutResult {AT A} `{InstLaws AT A} {Γ} : InstLaws (SMutResult Γ AT) (CMutResult Γ A). *)
  (* Proof. *)
  (*   constructor. *)
  (*   - intros ? ? []; cbn; now rewrite ?inst_lift. *)
  (*   - intros ? ? ? ? []; cbn; now rewrite ?inst_subst. *)
  (* Qed. *)

  (* Definition smut_wp {AT A} `{Inst AT A} {Γ1 Γ2 w0} (d : SMut Γ1 Γ2 AT w0) *)
  (*   (P : A -> SCProp Γ2) *)
  (*   (δ0 : SStore Γ1 w0) (h0 : SHeap w0) *)
  (*   (ι0 : SymInstance w0)  : Prop := *)
  (*   Path.wp (d δ0 h0) (fun r => P (scmutres_value r) (scmutres_store r) (scmutres_heap r)) ι0. *)
  (* Global Arguments smut_wp : simpl never. *)

  Class Approx (AT : TYPE) (A : Type) : Type :=
    approx :
      forall (w : World) (ι : SymInstance w),
        AT w -> A -> Prop.
  Global Arguments approx {_ _ _ w} ι _ _.

  Global Instance ApproxInst {AT A} `{instA : Inst AT A} : Approx AT A :=
    fun w ι t v =>
      v = inst t ι.
  Global Arguments ApproxInst {_ _ _} w ι t v /.

  Global Instance ApproxPath {AT A} `{instA : Inst AT A} : Approx (SPath AT) (Outcome A) :=
    fun w ι ms mc =>
      forall (P Q : A -> Prop) (PQ : forall a, P a -> Q a),
        wp ms P ι ->
        outcome_satisfy mc Q.

  Global Instance ApproxBox {AT A} `{Approx AT A} : Approx (Box AT) A :=
    fun w0 ι0 a0 a =>
      forall (w1 : World) (ω01 : w0 ⊒ w1) (ι1 : SymInstance w1),
        ι0 = inst (wsub ω01) ι1 ->
        instpc (wco w1) ι1 ->
        approx ι1 (a0 w1 ω01) a.

  Global Instance ApproxImpl {AT A BT B} `{Approx AT A, Approx BT B} : Approx (Impl AT BT) (A -> B) :=
    fun w ι fs fc =>
      forall (ta : AT w) (a : A),
        approx ι ta a ->
        approx ι (fs ta) (fc a).

  Global Instance ApproxMutResult {AT A} `{Approx AT A} {Γ} : Approx (SMutResult Γ AT) (CMutResult Γ A).
  Proof.
    intros w0 ι0 [a0 δ0 h0] [a δ h].
    refine (approx ι0 a0 a /\ approx ι0 δ0 δ /\ approx ι0 h0 h).
  Defined.

  Global Instance ApproxMut {Γ1 Γ2 AT A} `{instA : Inst AT A} : Approx (SMut Γ1 Γ2 AT) (CMut Γ1 Γ2 A).
  Proof.
    unfold SMut, CMut. auto with typeclass_instances.
    eapply ApproxImpl.
    Unshelve.
    eapply ApproxImpl.
    Unshelve.
    eapply ApproxPath.
    unfold Approx.
    intros w ι.
    eapply approx.
    eapply ApproxImpl.
  Defined.
    (* fun w ι ms mc => *)
    (*   forall POST δt ht δc hc, *)
    (*     δc = inst δt ι -> *)
    (*     hc = inst ht ι -> *)
    (*     smut_wp ms POST δt ht ι -> *)
    (*     cmut_wp mc POST δc hc. *)

  Global Instance ApproxTermLit {σ} : Approx (STerm σ) (Lit σ) :=
    ApproxInst (AT := STerm σ).

  (* Global Instance ApproxChunk : Approx Chunk SCChunk := *)
  (*   fun w ι t v => *)
  (*     v = inst t ι. *)

  (* Global Instance ApproxUnit : Approx Unit unit := *)
  (*   fun w ι t v => *)
  (*     v = inst t ι. *)

  Hint Unfold SMut : core.
  Hint Unfold CMut : core.

  Hint Unfold SMut : typeclass_instances.
  Hint Unfold CMut : typeclass_instances.

  Lemma bapprox_block {AT A} `{InstLaws AT A} {Γ1 Γ2} {w : World} (ι : SymInstance w) :
    approx ι (@smut_block Γ1 Γ2 AT w) cmut_block.
  Proof.
    intros until Q. cbn. auto.
  Qed.

  Import ModalNotations.

  Lemma approx_angelic {AT A} `{Inst AT A} (x : option 𝑺) (σ : Ty)
    {Γ1 Γ2} {w0 : World} (ι0 : SymInstance w0)
    (Hpc0 : instpc (wco w0) ι0) :
    approx ι0 (smut_angelic x σ) (cmut_angelic (Γ1 := Γ1) (Γ2 := Γ2)).
  Proof.
    intros ms mc Hm δs δc -> hs hc -> P Q PQ. cbn.
    intros [v Hwp]; exists v; revert Hwp.
    apply Hm; wsimpl; auto. reflexivity.
    unfold approx, ApproxInst. cbn.
    now rewrite inst_subst, ?inst_sub_wk1.
    unfold approx, ApproxInst. cbn.
    now rewrite inst_subst, ?inst_sub_wk1.
  Qed.

  Lemma approx_demonic {AT A} `{Inst AT A} (x : option 𝑺) (σ : Ty)
    {Γ1 Γ2} {w0 : World} (ι0 : SymInstance w0)
    (Hpc0 : instpc (wco w0) ι0) :
    approx ι0 (smut_demonic x σ) (cmut_demonic (Γ1 := Γ1) (Γ2 := Γ2)).
  Proof.
    intros ms mc Hm δs δc -> hs hc -> P Q PQ. cbn.
    intros Hwp v; specialize (Hwp v); revert Hwp.
    apply Hm; wsimpl; auto. reflexivity.
    unfold approx, ApproxInst. cbn.
    now rewrite inst_subst, ?inst_sub_wk1.
    unfold approx, ApproxInst. cbn.
    now rewrite inst_subst, ?inst_sub_wk1.
  Qed.

  Lemma approx_produce_chunk {Γ} {w0 : World} (ι0 : SymInstance w0)
    (Hpc0 : instpc (wco w0) ι0) :
    approx ι0 (@smut_produce_chunk Γ w0) (cmut_produce_chunk).
  Proof.
    intros tc c -> w1 ω01 ι1 -> Hpc1 δs δc -> hs hc -> P Q PQ.
    cbn. rewrite inst_subst. apply PQ.
  Qed.

  Lemma approx_assume_formula {Γ} {w0 : World} {fml : Formula w0}
    {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0) :
    approx ι0 (@smut_assume_formula Γ w0 fml) (cmut_assume_formula ι0 fml).
  Proof.
    intros δs δc -> hs hc -> P Q PQ Hwp Hfml. cbn.
    unfold smut_assume_formula, assume_formulak in Hwp.
    destruct (solver_spec fml) as [[w1 [ζ fmls]] Hsolver|Hsolver].
    - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [Hν Hsolver].
      specialize (Hν Hfml). specialize (Hsolver (inst (sub_multishift ζ) ι0)).
      rewrite inst_multi in Hsolver; auto. specialize (Hsolver eq_refl).
      destruct Hsolver as [Hsolver _]. specialize (Hsolver Hfml).
      rewrite wp_assume_multisub, wp_assume_formulas_without_solver in Hwp.
      specialize (Hwp Hν Hsolver). revert Hwp.
      unfold four, smut_bpure, wtrans, persist, persist_subst; cbn.
      wsimpl. rewrite inst_multi; auto.
    - intuition.
  Qed.

  (* Forward entailment *)
  Lemma multishift_entails {w0 w1} (ν : MultiSub w0 w1) (ι0 : SymInstance w0) :
    inst_multisub ν ι0 ->
    instpc (wco w0) ι0 ->
    instpc (wco w1) (inst (sub_multishift ν) ι0).
  Proof.
    induction ν; cbn.
    - wsimpl; auto.
    - intros [Heqx Heq'] Hpc0. wsimpl.
      rewrite inst_sub_shift.
      apply IHν; wsimpl; auto.
  Qed.

  Lemma approx_assume_formulak {AT A} `{InstLaws AT A} {Γ1 Γ2} {w0 : World} {fml : Formula w0}
    {ι0 : SymInstance w0} (Hpc0 : instpc (wco w0) ι0) :
    approx ι0 (@smutk_assume_formula AT Γ1 Γ2 w0 fml) (@cmut_assume_formulak A Γ1 Γ2 _ ι0 fml).
  Proof.
    intros ms mc Hm δt δc Hδ hs hc Hh P Q PQ Hwp Hfml.
    unfold smutk_assume_formula, assume_formulak in Hwp.
    destruct (solver_spec fml) as [[w1 [ζ fmls]] Hsolver|Hsolver].
    - specialize (Hsolver ι0 Hpc0). destruct Hsolver as [Hν Hsolver].
      specialize (Hν Hfml). specialize (Hsolver (inst (sub_multishift ζ) ι0)).
      rewrite inst_multi in Hsolver; auto. specialize (Hsolver eq_refl).
      destruct Hsolver as [Hsolver _]. specialize (Hsolver Hfml).
      rewrite wp_assume_multisub, wp_assume_formulas_without_solver in Hwp.
      specialize (Hwp Hν Hsolver). revert Hwp.
      unfold four, smut_bpure, wtrans, persist, persist_subst, K; cbn.
      wsimpl. apply Hm; cbn; wsimpl; auto.
      + rewrite ?inst_multi; auto.
      + rewrite inst_pathcondition_app. split; auto.
        now apply multishift_entails.
      + unfold approx, ApproxInst. cbn.
        now rewrite inst_subst, inst_multi.
      + unfold approx, ApproxInst. cbn.
        now rewrite inst_subst, inst_multi.
    - intuition.
  Qed.

  Lemma approx_box_assume_formula {Γ} {w0 : World} (ι0 : SymInstance w0)
    (Hpc : instpc (wco w0) ι0) (fml : Formula w0) :
    approx ι0 (@smut_box_assume_formula Γ w0 fml) (cmut_assume_formula ι0 fml).
  Proof.
    intros w1 ω01 ι1 -> Hpc1 δs δc Hδ hs hc Hh P Q PQ Hwp.
    eapply approx_assume_formula in Hwp; eauto. revert Hwp.
    cbn. now rewrite ?inst_subst.
  Qed.

  Lemma approx_demonic_match_bool {AT A} `{InstLaws AT A} {Γ1 Γ2} {w : World} (ι : SymInstance w) :
    approx ι (@smut_demonic_match_bool AT Γ1 Γ2 w) (cmut_match_bool (A := A)).
  Proof.
    intros t v -> ms1 mc1 Hm1 ms2 mc2 Hm2 w1 ω01 ι1 -> Hpc1 δs δc Hδ hs hc Hh P Q PQ.
    unfold smut_demonic_match_bool, demonic_match_bool.
    destruct (term_get_lit_spec (subst t ω01)) as [[] Ht|].
    - specialize (Ht ι1). rewrite inst_subst in Ht. rewrite Ht.
      cbn. cbv [T four wtrans wrefl]. apply Hm1; cbn; wsimpl; auto.
    - specialize (Ht ι1). rewrite inst_subst in Ht. rewrite Ht.
      cbn. cbv [T four wtrans wrefl]. apply Hm2; cbn; wsimpl; auto.
    - cbn [wp]. intros [Hwp1 Hwp2].
      admit.
  Admitted.

  Lemma approx_produce {Γ Σ0 pc0} (asn : Assertion Σ0) :
    let w0 := @MkWorld Σ0 pc0 in
    forall
      (ι0 : SymInstance w0)
      (Hpc0 : instpc (wco w0) ι0),
        approx ι0 (@smut_produce Γ w0 asn) (cmut_produce ι0 asn).
  Proof.
    induction asn; intros w0 * Hpc; cbn.
    - now eapply (@approx_box_assume_formula Γ w0).
    - now apply approx_produce_chunk.
    - apply approx_demonic_match_bool; eauto.
      reflexivity.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - intros w1 ω01 ι1 -> Hpc1. apply approx_demonic; auto.
      intros w2 ω02 ι2 -> Hpc2. intros t v ->.
      apply IHasn; cbn - [inst subst sub_wk1]; wsimpl; auto.
    - admit.
  Admitted.

  Lemma approx_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B}
    {Γ1 Γ2 Γ3} {w0 : World} (ι0 : SymInstance w0) (Hpc0 : instpc (wco w0) ι0) :
    approx ι0 (@smut_bind Γ1 Γ2 Γ3 AT BT w0) (@cmut_bind Γ1 Γ2 Γ3 A B).
  Proof.
    intros ms mc Hm fs fc Hf δs δc Hδ hs hc Hh P Q PQ.
    unfold smut_bind, cmut_bind.
    rewrite outcome_satisfy_bind.
    rewrite wp_bind; auto.
    apply Hm; auto. intros [a δ' h']. unfold T. cbn.
    apply Hf; wsimpl; auto. admit. admit. admit.
  Admitted.



  (* Lemma spath_arrow_dcl_eta {AT A BT B} `{Subst AT, Subst BT, Inst AT A, Inst BT B} {Γ Σ1} (f : spath_arrow (SMutResult Γ AT) BT Σ1) : *)
  (*   spath_arrow_dcl *)
  (*     (AT := SMutResult Γ AT) *)
  (*     (fun Σ2 ζ12 pc2 r => *)
  (*        f Σ2 ζ12 pc2 {| dmutres_value := dmutres_result_value r; dmutres_result_state := dmutres_result_state r |}) -> *)
  (*   spath_arrow_dcl f. *)
  (* Proof. *)
  (*   intros HYP Σ2 Σ3 ζ12 ζ13 pc2 pc3 ζ23 r2 r3 F P Q PQ ι2 ι3; *)
  (*     specialize (HYP Σ2 Σ3 ζ12 ζ13 pc2 pc3 ζ23 r2 r3 F P Q PQ ι2 ι3); *)
  (*     destruct r2, r3; intuition. *)
  (* Qed. *)

  (* Lemma spath_arrow_dcl_pure {BT B} `{Subst ET, Subst BT, Inst BT B} {Γ3 Σ1} : *)
  (*     spath_arrow_dcl *)
  (*       (fun (Σ3 : LCtx) (_ : Sub Σ1 Σ3) (X : SMutResult Γ3 BT Σ3) (_ : PathCondition Σ3) => *)
  (*          match X with *)
  (*          | MkSMutResult b3 δ3 h3 => spath_pure (MkSMutResult b3 δ3 h3) *)
  (*          end). *)
  (* Proof. unfold spath_arrow_dcl. destruct a1, a2. cbn. intuition. Qed. *)

  Definition smut_wp {AT A} `{Inst AT A} {Γ1 Γ2 Σ0} (d : SMut Γ1 Γ2 AT Σ0)
    {Σ1} (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1)
    (ι1 : SymInstance Σ1) (P : A -> SCProp Γ2) : Prop :=
    Path.wp pc1 (d Σ1 ζ01 pc1 δ1 h1) (fun r => P (scmutres_value r) (scmutres_store r) (scmutres_heap r)) ι1.
  Global Arguments smut_wp : simpl never.

  Ltac fold_smut_wp :=
    match goal with
    | |- context[Path.wp ?pc (?d ?Σ ?ζ ?pc ?δ ?h) (fun r => ?P _ _ _) ?ι] =>
      change (Path.wp pc (d Σ ζ pc δ h) _ ι) with (smut_wp d ζ pc δ h ι P)
    end.

  Lemma smut_wp_monotonic {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d : SMut Γ1 Γ2 AT Σ0)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h -> Q a δ h) :
      smut_wp d ζ01 pc1 δ1 h1 ι1 P -> smut_wp d ζ01 pc1 δ1 h1 ι1 Q.
  Proof.
    unfold smut_wp. apply Path.wp_monotonic; intros []; apply PQ.
  Qed.

  Lemma smut_wp_equiv {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d : SMut Γ1 Γ2 AT Σ0)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h <-> Q a δ h) :
      smut_wp d ζ01 pc1 δ1 h1 ι1 P <-> smut_wp d ζ01 pc1 δ1 h1 ι1 Q.
  Proof.
    unfold smut_wp. split; apply Path.wp_monotonic; intros []; apply PQ.
  Qed.

  Lemma smut_wp_pure {AT A} `{InstLaws AT A} {Γ Σ0 Σ1} (a0 : AT Σ0)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ) :
    smut_wp (smut_pure (Γ := Γ) a0) ζ01 pc1 δ1 h1 ι1 P <-> P (inst a0 (inst ζ01 ι1)) (inst δ1 ι1) (inst h1 ι1).
  Proof. unfold smut_wp, smut_pure; cbn. now rewrite inst_subst. Qed.

  Lemma smut_wp_fail {AT A D} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0 Σ1} (func msg : string) (data : D) (ζ01 : Sub Σ0 Σ1)
        (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) :
    smut_wp (smut_error func msg data) ζ01 pc1 δ1 h1 ι1 P <-> False.
  Proof. split; intros []. Qed.

  Lemma smut_wp_sub {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0 Σ1 Σ2} (ζ01 : Sub Σ0 Σ1) (d : SMut Γ1 Γ2 AT Σ0)
    (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ζ12 : Sub Σ1 Σ2) (ι2 : SymInstance Σ2)
    (P : A -> SCProp Γ2) :
    smut_wp (smut_sub ζ01 d) ζ12 pc2 δ2 h2 ι2 P <->
    smut_wp d (subst ζ01 ζ12) pc2 δ2 h2 ι2 P.
  Proof. reflexivity. Qed.

  Lemma smut_wp_debug {AT A DT D} `{InstLaws AT A, Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2 Σ0 Σ1} d (k : SMut Γ1 Γ2 AT Σ0)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ2) :
    smut_wp (smut_debug d k) ζ01 pc1 δ1 h1 ι1 P <-> smut_wp k ζ01 pc1 δ1 h1 ι1 P.
  Proof.
    unfold smut_wp, smut_debug; cbn. split.
    - now intros [].
    - now constructor.
  Qed.

  Definition smut_geq {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT} (d1 d2 : SMut Γ1 Γ2 AT Σ0) : Prop :=
    forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) pc1 (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ζ02 ι1 ι2,
      ι1 = inst ζ12 ι2 ->
      instpc pc1 ι1 ->
      instpc pc2 ι2 ->
      inst δ1 ι1 = inst δ2 ι2 ->
      inst h1 ι1 = inst h2 ι2 ->
      inst ζ01 ι1 = inst ζ02 ι2 ->
      forall (P Q : A -> SCProp Γ2) (PQ : forall a δ h, P a δ h -> Q a δ h),
        smut_wp d1 ζ01 pc1 δ1 h1 ι1 P ->
        smut_wp d2 ζ02 pc2 δ2 h2 ι2 Q.

  Definition smut_dcl {Γ1 Γ2 AT Σ0 A} `{Inst AT A, Subst AT} (d : SMut Γ1 Γ2 AT Σ0) : Prop :=
    smut_geq d d.

  Definition smut_mapping_dcl {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} (f : smut_mapping AT BT Σ0) : Prop :=
    forall Σ1 Σ2 (ζ01 : Sub Σ0 Σ1) (ζ02 : Sub Σ0 Σ2) (a1 : AT Σ1) (a2 : AT Σ2) (ζ12 : Sub Σ1 Σ2),
    forall ι1 ι2,
      ι1 = inst ζ12 ι2 ->
      inst ζ01 ι1 = inst ζ02 ι2 ->
      inst a1 ι1 = inst a2 ι2 ->
      inst (f Σ1 ζ01 a1) ι1 = inst (f Σ2 ζ02 a2) ι2.

  Lemma smut_mapping_dcl_four {AT A BT B} `{Inst AT A, Inst BT B} {Σ0} (f : smut_mapping AT BT Σ0) (f_dcl : smut_mapping_dcl f) :
    forall Σ1 (ζ01 : Sub Σ0 Σ1),
      smut_mapping_dcl (smut_mapping_four f ζ01).
  Proof.
  Admitted.

  Definition smut_arrow_dcl {AT A BT B} `{Subst BT, Inst AT A, Inst BT B} {Γ1 Γ2 Σ0} (f : smut_arrow Γ1 Γ2 AT BT Σ0) : Prop :=
    forall Σ1 Σ2 ζ01 ζ02 a1 a2 Σ3 Σ4 ζ13 ζ24 ζ34 pc3 pc4 δ3 h3 δ4 h4,
    forall (ι3 : SymInstance Σ3) (ι4 : SymInstance Σ4),
      ι3 = inst ζ34 ι4 ->
      instpc pc3 ι3 ->
      instpc pc4 ι4 ->
      inst (subst ζ01 ζ13) ι3 = inst (subst ζ02 ζ24) ι4 ->
      inst a1 (inst ζ13 ι3) = inst a2 (inst ζ24 ι4) ->
      inst δ3 ι3 = inst δ4 ι4 ->
      inst h3 ι3 = inst h4 ι4 ->
      forall (P Q : B -> SCProp Γ2) (PQ : forall b δ h, P b δ h -> Q b δ h),
        smut_wp (f Σ1 ζ01 a1) ζ13 pc3 δ3 h3 ι3 P ->
        smut_wp (f Σ2 ζ02 a2) ζ24 pc4 δ4 h4 ι4 Q.

  Lemma smut_arrow_dcl_specialize {AT A BT B} `{Subst BT, Inst AT A, Inst BT B} {Γ1 Γ2 Σ0}
    (f : smut_arrow Γ1 Γ2 AT BT Σ0) (f_dcl : smut_arrow_dcl f) :
    forall Σ1 (ζ01 : Sub Σ0 Σ1) (a1 : AT Σ1),
      smut_dcl (f Σ1 ζ01 a1).
  Proof.
    unfold smut_dcl, smut_geq. intros until Q; intros PQ.
    eapply f_dcl; eauto; rewrite ?inst_subst; congruence.
  Qed.

  Lemma smut_pure_dcl {AT A} `{InstLaws AT A} {Γ Σ} (a : AT Σ) :
    smut_dcl (smut_pure (Γ := Γ) a).
  Proof.
    unfold smut_dcl, smut_geq. intros * -> Hpc1 Hpc2 Hδ Hh Hζ * PQ.
    rewrite ?smut_wp_pure. rewrite Hδ, Hh, Hζ. apply PQ.
  Qed.

  Ltac rewrite_inst :=
    repeat rewrite <- ?sub_comp_wk1_tail, ?inst_subst,
      ?inst_sub_id, ?inst_sub_wk1, ?inst_sub_snoc,
      ?inst_lift, ?inst_sub_single, ?inst_pathcondition_cons.

  Lemma smut_wp_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
    (d : SMut Γ1 Γ2 AT Σ0) (f : smut_arrow Γ2 Γ3 AT BT Σ0) (f_dcl : smut_arrow_dcl f)
    (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ζ01 : Sub Σ0 Σ1) (ι1 : SymInstance Σ1)
    (POST : B -> SCProp Γ3) (Hpc1 : instpc pc1 ι1) :
    smut_wp (smut_bind d f) ζ01 pc1 δ1 h1 ι1 POST <->
    smut_wp d ζ01 pc1 δ1 h1 ι1 (fun a δ h => smut_wp (f _ (sub_id _) (lift a)) ζ01 pc1 (lift δ) (lift h) ι1 POST).
  Proof.
    unfold smut_wp, smut_bind; cbn.
    rewrite Path.wp_bind; auto. split; apply Path.wp_monotonic.
    - intros [a scδ2 sch2]; cbn. rewrite sub_comp_id_right.
      eapply f_dcl; rewrite_inst; auto.
    - intros [a scδ2 sch2]; cbn. rewrite sub_comp_id_right.
      eapply f_dcl; rewrite_inst; auto.
    - unfold Path.arrow_dcl.
      intros P Q PQ Σ3 ζ23 pc3 Σ4 ζ24 pc4 ζ34 [a3 δ3 h3] [a4 δ4 h4]; cbn.
      intros ι3 ι4 Hι34 Hpc3 Hpc4 Hζ Hres.
      inversion Hres. clear Hres.
      specialize (f_dcl Σ3 Σ4 (subst ζ01 ζ23) (subst ζ01 ζ24) a3 a4).
      specialize (f_dcl Σ3 Σ4 (sub_id Σ3) (sub_id Σ4) ζ34 pc3 pc4 δ3 h3 δ4 h4 ι3 ι4 Hι34 Hpc3 Hpc4).
      inster f_dcl by (rewrite_inst; intuition).
      apply (f_dcl (fun b δ h => P (MkCMutResult b δ h)) (fun b δ h => Q (MkCMutResult b δ h))).
      intuition.
  Qed.

  Lemma smut_wp_fmap {AT A BT B} `{InstLaws AT A, Inst BT B, Subst BT} {Γ1 Γ2 Σ0 Σ2}
    (d : SMut Γ1 Γ2 AT Σ0) (f : forall Σ1, Sub Σ0 Σ1 -> AT Σ1 -> BT Σ1)
    (f_dcl : smut_mapping_dcl f)
    (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ζ02 : Sub Σ0 Σ2) (ι2 : SymInstance Σ2)
    (Q : B -> SCProp Γ2) (Hpc2 : instpc pc2 ι2) :
    smut_wp (smut_fmap d f) ζ02 pc2 δ2 h2 ι2 Q <->
    smut_wp d ζ02 pc2 δ2 h2 ι2 (fun a : A => Q (inst (f Σ2 ζ02 (lift a)) ι2)).
  Proof.
    unfold smut_fmap, smut_wp. rewrite Path.wp_map; auto.
    split; apply Path.wp_monotonic; intros [a δ2' h2']; cbn.
    - now rewrite sub_comp_id_right, ?inst_lift.
    - now rewrite sub_comp_id_right, ?inst_lift.
    - unfold Path.mapping_dcl. destruct a1 as [a1 δ1 h1], a2 as [a3 δ3 h3]; cbn.
      intros * -> Hζ. inversion 1. f_equal.
      eapply f_dcl; rewrite ?inst_subst; intuition.
  Qed.

  Lemma smut_wp_pair {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
    (da : SMut Γ1 Γ2 AT Σ0) (db : SMut Γ2 Γ3 BT Σ0) (db_dcl : smut_dcl db)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) δ1 h1 ι1 (Hpc : instpc pc1 ι1) P :
    smut_wp (smut_pair da db) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp da ζ01 pc1 δ1 h1 ι1 (fun a δ2 h2 => smut_wp db ζ01 pc1 (lift δ2) (lift h2) ι1 (fun b => P (a,b))).
  Proof.
    unfold smut_pair, smut_fmap2. rewrite smut_wp_bind; eauto.
    apply smut_wp_equiv. intros a δ2 h2. rewrite smut_wp_fmap; eauto.
    rewrite smut_wp_sub, sub_comp_id_left.
    apply smut_wp_equiv. intros b δ3 h3. cbn.
    now rewrite ?inst_subst, ?inst_sub_id, ?inst_lift.
    - unfold smut_mapping_dcl. intros *. cbn.
      rewrite ?inst_subst, ?inst_lift. intuition.
    - intros until Q; intros PQ.
      rewrite ?smut_wp_fmap; eauto.
      + rewrite ?smut_wp_sub. eapply db_dcl; eauto.
        intros *. cbn. rewrite ?inst_subst, ?inst_lift, H11.
        intuition.
      + unfold smut_mapping_dcl. intros *. cbn.
        rewrite ?inst_subst, ?inst_lift. intros. subst.
        f_equal; auto. f_equal; auto.
      + unfold smut_mapping_dcl. intros *. cbn.
        rewrite ?inst_subst, ?inst_lift. intros. subst.
        f_equal; auto. f_equal; auto.
  Qed.

  Lemma smut_wp_bind_right {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
        (d1 : SMut Γ1 Γ2 AT Σ0) (d2 : SMut Γ2 Γ3 BT Σ0) (d2_dcl : smut_dcl d2)
        (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : B -> SCProp Γ3) (Hpc1 : instpc pc1 ι1) :
    smut_wp (smut_bind_right d1 d2) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp d1 ζ01 pc1 δ1 h1 ι1 (fun a δ2 h2 => smut_wp d2 ζ01 pc1 (lift δ2) (lift h2) ι1 P).
  Proof.
    unfold smut_bind_right. rewrite smut_wp_bind; auto.
    unfold smut_wp, smut_sub.
    split; apply Path.wp_monotonic;
      intros [a sc2]; now rewrite sub_comp_id_left.
    unfold smut_arrow_dcl. intros until Q; intros PQ.
    rewrite ?smut_wp_sub. eapply d2_dcl; eauto.
  Qed.

  Lemma smut_bind_right_arrow_dcl {AT A BT B CT C} `{InstLaws AT A, InstLaws BT B, InstLaws CT C} {Γ1 Γ2 Γ3 Σ1}
    (d1 : smut_arrow Γ1 Γ2 AT BT Σ1) (d1_dcl : smut_arrow_dcl d1)
    (d2 : smut_arrow Γ2 Γ3 AT CT Σ1) (d2_dcl : smut_arrow_dcl d2) :
    smut_arrow_dcl (fun Σ2 ζ02 a2 => smut_bind_right (d1 Σ2 ζ02 a2) (d2 Σ2 ζ02 a2)).
  Proof.
    intros until Q. intros PQ.
    rewrite ?smut_wp_bind_right; eauto.
    eapply d1_dcl; eauto. intros ? ? ?.
    eapply d2_dcl; eauto; now rewrite ?inst_lift.
    now apply smut_arrow_dcl_specialize.
    now apply smut_arrow_dcl_specialize.
  Qed.

  Lemma smut_bind_arrow_dcl {AT A BT B CT C} `{InstLaws AT A, InstLaws BT B, InstLaws CT C}
      {Γ1 Γ2 Γ3 Σ0}
      (d1 : smut_arrow Γ1 Γ2 AT BT Σ0) (d1_dcl : smut_arrow_dcl d1)
      (d2 : smut_arrow Γ2 Γ3 BT CT Σ0) (d2_dcl : smut_arrow_dcl d2) :
    smut_arrow_dcl (fun Σ2 ζ02 a2 => smut_bind (d1 Σ2 ζ02 a2) (fun Σ3 ζ23 a3 => d2 Σ3 (subst ζ02 ζ23) a3)).
  Proof.
    unfold smut_arrow_dcl, smut_geq.
    intros * -> Hpc1 Hpc2 Hζ Ha Hδ Hh P Q PQ; cbn.
    rewrite ?smut_wp_bind; auto. eapply d1_dcl; eauto. intros a δ h.
    eapply d2_dcl; eauto; rewrite ?inst_subst in Hζ;
      rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; intuition.

    unfold smut_arrow_dcl.
    intros * -> Hpc3 Hpc4 Hζ2 Ha2 Hδ2 Hh2 P2 Q2 PQ2; cbn.
    eapply d2_dcl; eauto.
    rewrite ?inst_subst in Hζ2.
    now rewrite ?inst_subst, Hζ2.

    unfold smut_arrow_dcl.
    intros * -> Hpc3 Hpc4 Hζ2 Ha2 Hδ2 Hh2 P2 Q2 PQ2; cbn.
    eapply d2_dcl; eauto.
    rewrite ?inst_subst in Hζ2.
    now rewrite ?inst_subst, Hζ2.
  Qed.

  Lemma smut_sub_arrow_dcl {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ2 Γ3 Σ0} (d : SMut Γ2 Γ3 BT Σ0) (d_dcl : smut_dcl d) :
    smut_arrow_dcl (fun (Σ2 : LCtx) (ζ02 : Sub Σ0 Σ2) (_ : AT Σ2) => smut_sub ζ02 d).
  Proof. intros until Q; intros PQ. rewrite ?smut_wp_sub. eapply d_dcl; eauto. Qed.

  Lemma smut_pure_arrow_dcl {AT A} `{InstLaws AT A} {Γ Σ0} :
    smut_arrow_dcl (fun Σ1 (ζ01 : Sub Σ0 Σ1) (a1 : AT Σ1) => smut_pure (Γ := Γ) a1).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_pure.
    intros HP. apply PQ. revert HP.
    rewrite ?inst_subst. intuition.
  Qed.

  Lemma smut_wp_bind_left {AT A BT B} `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0 Σ1}
        (d1 : SMut Γ1 Γ2 AT Σ0) (d2 : SMut Γ2 Γ3 BT Σ0) (d2_dcl : smut_dcl d2)
        (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ3) (Hpc1 : instpc pc1 ι1) :
    smut_wp (smut_bind_left d1 d2) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp d1 ζ01 pc1 δ1 h1 ι1 (fun a δ2 h2 => smut_wp d2 ζ01 pc1 (lift δ2) (lift h2) ι1 (fun _ => P a)).
  Proof.
    unfold smut_bind_left. rewrite smut_wp_bind; auto. apply smut_wp_equiv.
    intros a scδ2 sch2. rewrite smut_wp_bind_right, smut_wp_sub; auto.
    split; eapply d2_dcl; rewrite ?inst_subst, ?inst_sub_id; auto;
      intros _ scδ3 sch3; now rewrite smut_wp_pure, ?inst_lift.
    apply smut_pure_dcl.
    apply smut_bind_right_arrow_dcl.
    now apply smut_sub_arrow_dcl.
    apply smut_pure_arrow_dcl.
  Qed.

  Lemma smut_wp_state {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ1 Σ2}
    (f : forall Σ2, Sub Σ1 Σ2 -> SStore Γ1 Σ2 -> SHeap Σ2 -> SMutResult Γ2 AT Σ2)
    (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ζ12 : Sub Σ1 Σ2) (ι2 : SymInstance Σ2) (Q : A -> SCProp Γ2) :
    smut_wp (smut_state f) ζ12 pc2 δ2 h2 ι2 Q <->
    match f Σ2 ζ12 δ2 h2 with MkSMutResult a δ2' h2' => Q (inst a ι2) (inst δ2' ι2) (inst h2' ι2) end.
  Proof.
    unfold smut_wp, smut_state; cbn.
    now destruct (f Σ2 ζ12 _).
  Qed.

  Lemma smut_wp_demonic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d1 d2 : SMut Γ1 Γ2 AT Σ0)
        (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) :
    smut_wp (smut_demonic_binary d1 d2) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp d1 ζ01 pc1 δ1 h1 ι1 P /\ smut_wp d2 ζ01 pc1 δ1 h1 ι1 P.
  Proof. reflexivity. Qed.

  Lemma smut_wp_angelic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ0 Σ1} (d1 d2 : SMut Γ1 Γ2 AT Σ0)
        (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) :
    smut_wp (smut_angelic_binary d1 d2) ζ01 pc1 δ1 h1 ι1 P <->
    smut_wp d1 ζ01 pc1 δ1 h1 ι1 P \/ smut_wp d2 ζ01 pc1 δ1 h1 ι1 P.
  Proof. reflexivity. Qed.

  Lemma smut_wp_angelic {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ0 Σ1} {x : option 𝑺} {σ : Ty}
    (k : forall Σ1 : LCtx, Sub Σ0 Σ1 -> Term Σ1 σ -> SMut Γ1 Γ2 AT Σ1) (k_dcl : smut_arrow_dcl k)
    (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ2) (Hpc : instpc pc1 ι1) :
    smut_wp (smut_angelic x σ k) ζ01 pc1 δ1 h1 ι1 P <->
    exists v : Lit σ, smut_wp (k _ (sub_id _) (lift (T := fun Σ => Term Σ σ) v)) ζ01 pc1 δ1 h1 ι1 P.
  Proof.
    unfold smut_wp, smut_angelic; cbn - [Path.angelic].
    split; intros [v Hwp]; exists v; revert Hwp; eapply k_dcl; unfold four;
      repeat rewrite ?inst_sub_snoc, ?inst_subst, ?inst_sub_wk1, ?inst_sub_id; auto.
    now instantiate (1 := term_lit _ v).
  Qed.


  Lemma smut_wp_demonicv {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ Σ1 x σ} (d : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ))) (d_dcl : smut_dcl d)
        (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
        (P : A -> SCProp Γ2) (hpc : instpc pc1 ι1) :
    smut_wp (smut_demonicv x σ d) ζ01 pc1 δ1 h1 ι1 P <->
    forall v : Lit σ, smut_wp d (sub_snoc ζ01 (x :: σ) (term_lit σ v)) pc1 δ1 h1 ι1 P.
  Proof.
    unfold smut_wp, smut_demonicv; cbn.
    split; intros Hwp v; specialize (Hwp v); revert Hwp.
    - apply (d_dcl
               (Σ1 ▻ (fresh Σ1 (Some x) :: σ)) Σ1 (sub_snoc (subst ζ01 sub_wk1) (x :: σ) (term_var (fresh Σ1 (Some x)))) (subst pc1 sub_wk1)
               (subst δ1 sub_wk1) (subst h1 sub_wk1) (sub_snoc (sub_id Σ1) (fresh Σ1 (Some x) :: σ) (term_lit σ v)) pc1 δ1 h1 (sub_snoc ζ01 (x :: σ) (term_lit σ v)));
        rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn.
      now rewrite inst_subst, inst_sub_wk1.
    - apply (d_dcl
               Σ1 (Σ1 ▻ (fresh Σ1 (Some x) :: σ)) (sub_snoc ζ01 (x :: σ) (term_lit σ v)) pc1 δ1 h1 sub_wk1 (subst pc1 sub_wk1) (subst δ1 sub_wk1) (subst h1 sub_wk1)
               (sub_snoc (subst ζ01 sub_wk1) (x :: σ) (term_var (fresh Σ1 (Some x)))));
        rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_wk1, ?inst_sub_id; auto; cbn.
      now rewrite inst_subst, inst_sub_wk1.
  Qed.

  Lemma smut_wp_angelic_list {AT A D} `{InstLaws AT A} {Γ Σ} (func msg : string) (data : D)
    (xs : List AT Σ) Σ1 (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ) :
    smut_wp (smut_angelic_list func msg data xs) ζ01 pc1 δ1 h1 ι1 P <->
    exists x : AT _, List.In x xs /\ P (inst x (inst ζ01 ι1)) (inst δ1 ι1) (inst h1 ι1).
  Proof.
    induction xs; cbn - [smut_wp].
    - rewrite smut_wp_fail. split. intro Fm; exfalso; intuition.
      intros []; intuition.
    - destruct xs; cbn - [smut_wp] in *.
      + rewrite smut_wp_fail in IHxs.
        rewrite smut_wp_pure.
        destruct IHxs. split; intros; destruct_conjs.
        exists a. intuition.
        intuition.
      + rewrite smut_wp_angelic_binary, smut_wp_pure.
        split. intros [Hwp|Hwp].
        * exists a. split; auto.
        * apply IHxs in Hwp. destruct Hwp as [x [Hwp HP]].
          exists x. split; auto.
        * intros [x [Hwp HP]].
          destruct Hwp as [Hwp|Hwp]. subst. left. auto.
          destruct Hwp as [Hwp|Hwp]. subst.
          right. apply IHxs. exists x. split; auto.
          right. apply IHxs. exists x. split; auto.
  Qed.

  (* Lemma smut_wp_demonic_list {AT A} `{InstLaws AT A} {Γ Σ} *)
  (*   (xs : List AT Σ) Σ1 (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1) *)
  (*   (P : A -> SCProp Γ) : *)
  (*   smut_wp (smut_demonic_list xs) ζ01 pc1 δ1 h1 ι1 P <-> *)
  (*   forall x : AT _, List.In x xs -> P (inst x (inst ζ01 ι1)) (inst δ1 ι1) (inst h1 ι1). *)
  (* Proof. *)
  (*   induction xs. *)
  (*   - cbn; firstorder. *)
  (*   - destruct xs; cbn. *)
  (*     + rewrite smut_wp_pure. *)
  (*       intuition. *)
  (*     + rewrite smut_wp_demonic_binary. *)
  (*       rewrite smut_wp_pure. *)
  (*       intuition. *)
  (* Qed. *)

  (* Lemma smut_wp_demonic_listk {AT BT B} `{InstLaws BT B} {Γ1 Γ2 Σ} *)
  (*       (xs : List AT Σ) (k : AT Σ -> SMut Γ1 Γ2 BT Σ) *)
  (*       Σ1 (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1) *)
  (*   (P : B -> SCProp Γ2) : *)
  (*   smut_wp (smut_demonic_listk xs k) ζ01 pc1 δ1 h1 ι1 P <-> *)
  (*   forall x : AT _, List.In x xs -> smut_wp (k x) ζ01 pc1 δ1 h1 ι1 P. *)
  (* Proof. *)
  (*   induction xs. *)
  (*   - cbn; firstorder. *)
  (*   - destruct xs. *)
  (*     + cbn in *. intuition. *)
  (*     + change (smut_wp (smut_demonic_listk (a :: a0 :: xs)%list k) ζ01 pc1 δ1 h1 ι1 P) *)
  (*         with (smut_wp (k a) ζ01 pc1 δ1 h1 ι1 P /\ smut_wp (smut_demonic_listk (a0 :: xs)%list k) ζ01 pc1 δ1 h1 ι1 P). *)
  (*       rewrite IHxs. cbn. intuition. *)
  (* Qed. *)

  Lemma smut_wp_demonic_termvar {Γ Σ Σ1 x σ}
    (ζ01 : Sub Σ Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : Lit σ -> SCProp Γ) (Hpc : instpc pc1 ι1) :
    smut_wp (smut_demonic_termvar x σ) ζ01 pc1 δ1 h1 ι1 P <->
    forall v : Lit σ, P v (inst δ1 ι1) (inst h1 ι1).
  Proof.
    unfold smut_wp, smut_demonic_termvar; cbn.
    split; intros Hwp v; specialize (Hwp v); revert Hwp;
      now rewrite ?inst_subst, ?inst_sub_wk1.
  Qed.

  Lemma smut_error_dcl `{Inst AT A, Subst AT} {D Γ1 Γ2 Σ} func msg data :
    smut_dcl (@smut_error Γ1 Γ2 AT Σ D func msg data).
  Proof.
    unfold smut_dcl, smut_geq. intros * -> Hpc1 Hpc2 Hδ Hh Hζ * PQ.
    now rewrite ?smut_wp_fail.
  Qed.

  Lemma smut_sub_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d : SMut Γ1 Γ2 AT Σ0) (d_dcl : smut_dcl d) :
    forall (Σ1 : LCtx) (ζ1 : Sub Σ0 Σ1), smut_dcl (smut_sub ζ1 d).
  Proof.
    unfold smut_dcl, smut_geq. intros * -> Hpc1 Hpc2 Hs Hζ * PQ. rewrite ?smut_wp_sub.
    apply d_dcl with ζ12; auto. rewrite ?inst_subst. congruence.
  Qed.

  Lemma smut_demonicv_dcl {AT A} `{Inst AT A, Subst AT} {Γ1 Γ2 Σ x σ} (d : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ))) (d_dcl : smut_dcl d) :
    smut_dcl (smut_demonicv x σ d).
  Proof.
    unfold smut_dcl, smut_geq. intros until Q; intros PQ.
    rewrite ?smut_wp_demonicv; auto.
    intros Hwp v. specialize (Hwp v). revert Hwp.
    eapply d_dcl; eauto. rewrite ?inst_sub_snoc.
    cbn. f_equal; auto.
  Qed.

  Lemma smut_demonic_termvar_dcl {Γ Σ x σ} :
    smut_dcl (@smut_demonic_termvar Γ Σ σ x).
  Proof. Admitted.

  Ltac fold_inst_term :=
    repeat change (@inst_term ?Σ ?σ ?t ?ι) with (@inst (fun Σ => Term Σ σ) (Lit σ) (@instantiate_term σ) Σ t ι) in *.

  Lemma smut_bind_dcl {AT A BT B} `{InstLaws AT A, InstLaws BT B}
      {Γ1 Γ2 Γ3 Σ0} (d : SMut Γ1 Γ2 AT Σ0) (d_dcl : smut_dcl d)
      (f : smut_arrow Γ2 Γ3 AT BT Σ0) (f_dcl : smut_arrow_dcl f) :
    smut_dcl (smut_bind d f).
  Proof.
    unfold smut_dcl, smut_geq. intros * -> Hpc1 Hpc2 Hδ Hh Hζ P Q PQ; cbn.
    rewrite ?smut_wp_bind; auto. eapply d_dcl; eauto. intros a δ h.
    eapply f_dcl; eauto; rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; intuition.
  Qed.

  Lemma smut_bind_right_dcl `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0}
    (d1 : SMut Γ1 Γ2 AT Σ0) (d2 : SMut Γ2 Γ3 BT Σ0)
    (d1_dcl : smut_dcl d1) (d2_dcl : smut_dcl d2) :
    smut_dcl (smut_bind_right d1 d2).
  Proof.
    unfold smut_bind_right, smut_sub. apply smut_bind_dcl; auto.
    unfold smut_arrow_dcl. intros. revert H14. eapply d2_dcl; eauto.
  Qed.

  Lemma smut_bind_left_dcl `{InstLaws AT A, InstLaws BT B} {Γ1 Γ2 Γ3 Σ0}
    (d1 : SMut Γ1 Γ2 AT Σ0) (d2 : SMut Γ2 Γ3 BT Σ0)
    (d1_dcl : smut_dcl d1) (d2_dcl : smut_dcl d2) :
    smut_dcl (smut_bind_left d1 d2).
  Proof.
    unfold smut_bind_left. apply smut_bind_dcl; auto.
    apply smut_bind_right_arrow_dcl.
    now apply smut_sub_arrow_dcl.
    apply smut_pure_arrow_dcl.
  Qed.

  Lemma smut_demonic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d1 d2 : SMut Γ1 Γ2 AT Σ0) (d1_dcl : smut_dcl d1) (d2_dcl : smut_dcl d2) :
    smut_dcl (smut_demonic_binary d1 d2).
  Proof.
    unfold smut_dcl, smut_geq. intros until Q; intros PQ.
    rewrite ?smut_wp_demonic_binary. intros [Hwp1 Hwp2].
    split.
    - revert Hwp1. eapply d1_dcl; eauto.
    - revert Hwp2. eapply d2_dcl; eauto.
  Qed.

  Lemma smut_angelic_binary_dcl {Γ1 Γ2 AT A Σ0} `{Inst AT A, Subst AT} (d1 d2 : SMut Γ1 Γ2 AT Σ0) (d1_dcl : smut_dcl d1) (d2_dcl : smut_dcl d2) :
    smut_dcl (smut_angelic_binary d1 d2).
  Proof.
    unfold smut_dcl, smut_geq. intros until Q; intros PQ.
    rewrite ?smut_wp_angelic_binary. intros [Hwp1|Hwp2].
    - left. revert Hwp1. eapply d1_dcl; eauto.
    - right. revert Hwp2. eapply d2_dcl; eauto.
  Qed.

  Lemma smut_state_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ}
    (f : forall Σ' : LCtx, Sub Σ Σ' -> SStore Γ1 Σ' -> SHeap Σ' -> SMutResult Γ2 AT Σ')
    (f_dcl :
       forall Σ1 Σ2 (ζ01 : Sub Σ Σ1) (ζ02 : Sub Σ Σ2) (ζ12 : Sub Σ1 Σ2)
         (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1)
         (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) ι1 ι2,
         ι1 = inst ζ12 ι2 ->
         inst δ1 ι1 = inst δ2 ι2 ->
         inst h1 ι1 = inst h2 ι2 ->
         inst ζ01 ι1 = inst ζ02 ι2 ->
         inst (f Σ1 ζ01 δ1 h1) ι1 = inst (f Σ2 ζ02 δ2 h2) ι2) :
    smut_dcl (smut_state f).
  Proof.
    unfold smut_dcl; intros until Q. intros PQ. rewrite ?smut_wp_state.
    pose proof (f_dcl Σ1 Σ2 ζ01 ζ02 ζ12 δ1 h1 δ2 h2 ι1 ι2) as Hf.
    destruct (f Σ1 ζ01 δ1 h1), (f Σ2 ζ02 δ2 h2); cbn.
    cbn in Hf. inster Hf by (f_equal; auto).
    inversion Hf. intros Hp. apply PQ. revert Hp. intuition.
  Qed.
  Local Hint Resolve smut_state_dcl : core.

  Lemma smut_put_local_dcl {Γ1 Γ2 Σ} (δ : SStore Γ2 Σ) :
    smut_dcl (smut_put_local (Γ := Γ1) δ).
  Proof.
    apply smut_state_dcl. intros * -> Heqδ Heqh Heqζ. cbn.
    f_equal; auto. rewrite ?inst_subst. intuition.
  Qed.
  Local Hint Resolve smut_put_local_dcl : core.

  Lemma smut_get_local_dcl {Γ Σ}  :
    smut_dcl (smut_get_local (Σ := Σ) (Γ := Γ)).
  Proof.
    apply smut_state_dcl. intros * -> Heqδ Heqh Heqζ. cbn.
    f_equal; auto.
  Qed.
  Local Hint Resolve smut_get_local_dcl : core.

  Lemma smut_put_heap_dcl {Γ Σ} (h : SHeap Σ) :
    smut_dcl (smut_put_heap (Γ := Γ) h).
  Proof.
    apply smut_state_dcl. intros * -> Heqδ Heqh Heqζ. cbn.
    f_equal; auto. rewrite ?inst_subst. intuition.
  Qed.
  Local Hint Resolve smut_put_heap_dcl : core.

  Lemma smut_get_heap_dcl {Γ Σ} :
    smut_dcl (smut_get_heap (Γ := Γ) (Σ := Σ)).
  Proof.
    apply smut_state_dcl. intros * -> Heqδ Heqh Heqζ.
    cbn. f_equal; auto.
  Qed.
  Local Hint Resolve smut_get_heap_dcl : core.

  Lemma smut_pop_local_dcl {Γ x σ Σ} :
    smut_dcl (@smut_pop_local Γ x σ Σ).
  Proof.
    unfold smut_pop_local. apply smut_state_dcl. intros * -> Hδ Hh Hζ.
    destruct (snocView δ1), (snocView δ2). cbn in Hδ.
    apply noConfusion_inv, (f_equal pr1) in Hδ. cbn in Hδ.
    cbn. f_equal. apply Hδ. auto.
  Qed.

  Lemma smut_block_dcl {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ}  :
    smut_dcl (Γ1 := Γ1) (Γ2 := Γ2) (Σ0 := Σ) smut_block.
  Proof. now unfold smut_dcl, smut_block. Qed.

  (* Lemma smut_demonic_list_dcl {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ} (l : list (SMut Γ1 Γ2 AT Σ)) *)
  (*   (l_dcl : forall d, List.In d l -> smut_dcl d) : *)
  (*   smut_dcl (smut_demonic_list l). *)
  (* Proof. *)
  (*   induction l; cbn. *)
  (*   - apply smut_block_dcl. *)
  (*   - destruct l. *)
  (*     + apply l_dcl. now left. *)
  (*     + apply smut_demonic_binary_dcl. *)
  (*       apply l_dcl. now left. *)
  (*       apply IHl. intros d' dIn'. *)
  (*       apply l_dcl. now right. *)
  (* Qed. *)

  Lemma smut_angelic_list_dcl {AT A D} `{Subst AT, SubstLaws AT, Inst AT A, InstLaws AT A}
        {Γ Σ} func msg (data : D) (l : list (AT Σ)) :
    smut_dcl (Γ2 := Γ) (smut_angelic_list func msg data l).
  Proof.
    induction l; cbn.
    - apply smut_error_dcl.
    - destruct l.
      + apply smut_pure_dcl.
      + apply smut_angelic_binary_dcl.
        apply smut_pure_dcl.
        apply IHl.
  Qed.

  Lemma smut_angelic_list_arrow_dcl {AT A BT B D} `{Subst AT, SubstLaws AT, Inst AT A, InstLaws AT A, Inst BT B, InstLaws BT B}
        {Γ Σ} func msg (data : D) (l : forall Σ2 (ζ : Sub Σ Σ2) s, list (BT Σ2))
    (Hl : forall (Σ1 Σ2 : LCtx) (ζ01 : Sub Σ Σ1) (ζ02 : Sub Σ Σ2) (a1 : AT Σ1) (a2 : AT Σ2) (Σ3 Σ4 : LCtx)
       (ζ13 : Sub Σ1 Σ3) (ζ24 : Sub Σ2 Σ4) (ζ34 : Sub Σ3 Σ4) (pc3 : PathCondition Σ3) (pc4 : PathCondition Σ4)
       (ι3 : SymInstance Σ3) (ι4 : SymInstance Σ4),
        ι3 = inst ζ34 ι4 ->
        instpc pc3 ι3 ->
        instpc pc4 ι4 ->
        inst (subst ζ01 ζ13) ι3 = inst (subst ζ02 ζ24) ι4 ->
        inst a1 (inst ζ13 ι3) = inst a2 (inst ζ24 ι4) ->
        inst (l Σ1 ζ01 a1) (inst ζ13 ι3) = inst (l Σ2 ζ02 a2) (inst ζ24 ι4)) :
    smut_arrow_dcl (Γ2 := Γ) (fun Σ2 (ζ : Sub Σ Σ2) s => smut_angelic_list func msg data (l Σ2 ζ s)).
  Proof.
    unfold smut_arrow_dcl.
    intros until Q.
    intros PQ.
    assert (eql : inst (l Σ1 ζ01 a1) (inst ζ13 ι3) = inst (l Σ2 ζ02 a2) (inst ζ24 ι4)) by (eapply Hl; eauto).
    rewrite ?smut_wp_angelic_list; eauto.
    intros (x & xInl1 & Px).
    apply (List.in_map (fun x => inst x (inst ζ13 ι3))) in xInl1.
    unfold inst at 1 3 in eql; cbn in eql.
    rewrite eql in xInl1.
    eapply List.in_map_iff in xInl1.
    destruct xInl1 as (x2 & eq2 & x2Inl2).
    apply PQ in Px.
    rewrite <-eq2,H17,H18 in Px.
    exists x2; eauto.
  Qed.

  (* Lemma smut_demonic_finite_dcl {F AT A} `{finite.Finite F, Subst AT, Inst AT A} {Γ Σ} *)
  (*   (k : F -> SMut Γ Γ AT Σ) (k_dcl : forall x, smut_dcl (k x)) : *)
  (*   smut_dcl (smut_demonic_finite F k). *)
  (* Proof. *)
  (*   unfold smut_demonic_finite. apply smut_demonic_list_dcl. *)
  (*   intros d. rewrite List.in_map_iff. *)
  (*   intros [x [? xIn]]. subst d. apply k_dcl. *)
  (* Qed. *)

  (* Lemma smut_angelic_finite_dcl {F AT A} `{finite.Finite F, Subst AT, Inst AT A} {Γ Σ} *)
  (*   (k : F -> SMut Γ Γ AT Σ) (k_dcl : forall x, smut_dcl (k x)) : *)
  (*   smut_dcl (smut_angelic_finite F k). *)
  (* Proof. *)
  (*   unfold smut_angelic_finite. apply smut_angelic_list_dcl. *)
  (*   intros d. rewrite List.in_map_iff. *)
  (*   intros [x [? xIn]]. subst d. apply k_dcl. *)
  (* Qed. *)

  Lemma smut_wp_assume_formula {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fml : Formula Σ1)
    (δ2 : SStore Γ Σ2) (h2 : SHeap Σ2) (ι2 : SymInstance Σ2) POST :
    instpc pc2 ι2 ->
    smut_wp (smut_assume_formula fml) ζ12 pc2 δ2 h2 ι2 POST <->
    ((inst fml (inst ζ12 ι2) : Prop) -> POST tt (inst δ2 ι2) (inst h2 ι2)).
  Proof.
    unfold smut_wp, smut_assume_formula. intros.
    rewrite Path.wp_bind; auto.
    - rewrite Path.wp_assume_formula; auto.
      unfold T. rewrite ?subst_sub_id, ?inst_subst.
      reflexivity.
    - unfold Path.arrow_dcl. cbn.
      intros * PQ * Hι Hpc1 Hpc2 Hζ Ha.
      rewrite ?inst_subst. intuition.
  Qed.

  Lemma smut_assume_formula_dcl {Γ Σ} (fml : Formula Σ) :
    smut_dcl (Γ1 := Γ) (smut_assume_formula fml).
  Proof.
    unfold smut_dcl, smut_geq; intros. revert H5.
    rewrite ?smut_wp_assume_formula; auto.
    rewrite H2, H3. intuition.
  Qed.

  Lemma smut_assume_formulas_dcl {Γ Σ} (fmls : list (Formula Σ)) :
    smut_dcl (Γ1 := Γ) (smut_assume_formulas fmls).
  Proof.
    induction fmls.
    + now eapply smut_pure_dcl.
    + cbn.
      eapply smut_bind_right_dcl.
      eapply smut_assume_formula_dcl.
      eapply IHfmls.
  Qed.

  Lemma smut_wp_assume_formulas {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fmls : list (Formula Σ1))
    (δ2 : SStore Γ Σ2) (h2 : SHeap Σ2) (ι2 : SymInstance Σ2) (Hpc2 : instpc pc2 ι2) POST :
    smut_wp (smut_assume_formulas fmls) ζ12 pc2 δ2 h2 ι2 POST <->
    (instpc fmls (inst ζ12 ι2) -> POST tt (inst δ2 ι2) (inst h2 ι2)).
  Proof.
    unfold smut_assume_formulas. revert δ2 h2.
    induction fmls; cbn [List.fold_right]; intros δ2 h2.
    - rewrite smut_wp_pure. cbn. intuition.
      apply H. constructor.
    - rewrite smut_wp_bind_right; auto.
      rewrite smut_wp_assume_formula; auto.
      rewrite IHfmls.
      rewrite inst_pathcondition_cons.
      rewrite ?inst_lift.
      intuition.
      eapply smut_assume_formulas_dcl.
  Qed.

  Lemma smut_wp_assert_formula {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fml : Formula Σ1)
    (δ2 : SStore Γ Σ2) (h2 : SHeap Σ2)
    (ι2 : SymInstance Σ2) (Hpc2 : instpc pc2 ι2) POST :
    smut_wp (smut_assert_formula fml) ζ12 pc2 δ2 h2 ι2 POST <->
    (inst fml (inst ζ12 ι2) /\ POST tt (inst δ2 ι2) (inst h2 ι2)).
  Proof.
    unfold smut_wp, smut_assert_formula.
    rewrite Path.wp_bind, Path.wp_assert_formula; cbn;
      rewrite ?inst_subst, ?inst_sub_id; auto.
    unfold Path.arrow_dcl. cbn. intros.
    revert H4. rewrite ?inst_subst.
    rewrite H2, H3. apply PQ.
  Qed.

  Lemma smut_wp_assert_formulak {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Σ2} (fml : Formula Σ1) (k : SMut Γ1 Γ2 AT Σ1) (k_dcl : smut_dcl k)
    (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2) (ι2 : SymInstance Σ2) (Hpc2 : instpc pc2 ι2) POST :
    smut_wp (smut_assert_formulak fml k) ζ12 pc2 δ2 h2 ι2 POST <->
    (inst fml (inst ζ12 ι2) /\ smut_wp k ζ12 pc2 δ2 h2 ι2 POST).
  Proof.
    unfold smut_assert_formulak.
    rewrite smut_wp_bind_right; auto.
    rewrite smut_wp_assert_formula; auto.
    split; intros [Hfml Hwp]; split; auto; revert Hwp;
      eapply k_dcl; rewrite ?inst_lift; eauto.
  Qed.

  Lemma smut_assert_formula_dcl {Γ Σ} (fml : Formula Σ) :
    smut_dcl (Γ1 := Γ) (smut_assert_formula fml).
  Proof.
    unfold smut_dcl, smut_geq. intros. revert H5.
    rewrite ?smut_wp_assert_formula; auto.
    rewrite H2, H3. intuition.
  Qed.

  Lemma smut_assert_formulas_dcl {Γ Σ} (fmls : list (Formula Σ)) :
    smut_dcl (smut_assert_formulas (Γ := Γ) fmls).
  Proof.
    induction fmls; cbn; [eapply smut_pure_dcl|].
    eapply smut_bind_right_dcl.
    eapply smut_assert_formula_dcl.
    eapply IHfmls.
  Qed.

  Lemma smut_assert_formulak_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (fml : Formula Σ) (k : SMut Γ1 Γ2 AT Σ) (k_dcl : smut_dcl k) :
    smut_dcl (smut_assert_formulak fml k).
  Proof.
    unfold smut_assert_formulak.
    apply smut_bind_right_dcl; auto.
    apply smut_assert_formula_dcl.
  Qed.

  Lemma smut_assert_formulask_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (fmls : List Formula Σ) (k : SMut Γ1 Γ2 AT Σ) (k_dcl : smut_dcl k) :
    smut_dcl (smut_assert_formulask fmls k).
  Proof.
    unfold smut_assert_formulask.
    induction fmls; cbn.
    - assumption.
    - now apply smut_assert_formulak_dcl.
  Qed.

  Lemma smut_wp_assert_formulask {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Σ2} (fmls : PathCondition Σ1) (k : SMut Γ1 Γ2 AT Σ1) (k_dcl : smut_dcl k)
    (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (δ2 : SStore Γ1 Σ2) (h2 : SHeap Σ2)
    (ι2 : SymInstance Σ2) (Hpc2 : instpc pc2 ι2) POST :
    smut_wp (smut_assert_formulask fmls k) ζ12 pc2 δ2 h2 ι2 POST <->
    (inst fmls (inst ζ12 ι2) /\ smut_wp k ζ12 pc2 δ2 h2 ι2 POST).
  Proof.
    unfold smut_assert_formulask. revert δ2 h2.
    induction fmls; cbn [List.fold_right]; intros δ2 h2.
    - intuition. constructor.
    - rewrite smut_wp_assert_formulak; auto.
      rewrite IHfmls.
      rewrite inst_pathcondition_cons.
      intuition.
      now apply smut_assert_formulask_dcl.
  Qed.

  Lemma smut_wp_assert_formulas {Γ Σ1 Σ2} (ζ12 : Sub Σ1 Σ2) (pc2 : PathCondition Σ2) (fmls : list (Formula Σ1))
    (δ2 : SStore Γ Σ2) (h2 : SHeap Σ2)
    (ι2 : SymInstance Σ2) (Hpc2 : instpc pc2 ι2) POST :
    smut_wp (smut_assert_formulas fmls) ζ12 pc2 δ2 h2 ι2 POST <->
    (instpc fmls (inst ζ12 ι2) /\ POST tt (inst δ2 ι2) (inst h2 ι2)).
  Proof.
    unfold smut_assert_formulas. revert δ2 h2.
    induction fmls; cbn [List.fold_right]; intros δ2 h2.
    - rewrite smut_wp_pure. intuition.
      constructor.
    - rewrite smut_wp_bind_right; auto.
      rewrite smut_wp_assert_formula; auto.
      rewrite IHfmls.
      rewrite inst_pathcondition_cons.
      rewrite ?inst_lift.
      intuition.
      apply smut_assert_formulas_dcl.
  Qed.

  Lemma smut_wp_angelic_match_bool {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (s : Term Σ1 ty_bool)
    (kt kf : SMut Γ1 Γ2 AT Σ1) (kt_dcl : smut_dcl kt) (kf_dcl : smut_dcl kf)
    Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ι2 P :
    instpc pc2 ι2 ->
    smut_wp (smut_angelic_match_bool s kt kf) ζ12 pc2 δ2 h2 ι2 P <->
    (inst (T := fun Σ => Term Σ _) (A := Lit ty_bool) s (inst ζ12 ι2) = true /\
     smut_wp kt ζ12 pc2 δ2 h2 ι2 P \/
     inst (T := fun Σ => Term Σ _) (A := Lit ty_bool) s (inst ζ12 ι2) = false /\
     smut_wp kf ζ12 pc2 δ2 h2 ι2 P).
  Proof.
  Admitted.

  (* Lemma smut_wp_demonic_match_enum {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E)) *)
  (*   (d : 𝑬𝑲 E -> SMut Γ1 Γ2 AT Σ1) (d_dcl : forall x, smut_dcl (d x)) *)
  (*   Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ι2 P : *)
  (*   instpc pc2 ι2 -> *)
  (*   smut_wp (smut_demonic_match_enum t d) ζ12 pc2 δ2 h2 ι2 P <-> *)
  (*   smut_wp (d (inst (T := fun Σ => Term Σ _) (A := 𝑬𝑲 E) t (inst ζ12 ι2))) ζ12 pc2 δ2 h2 ι2 P. *)
  (* Proof. *)
  (*   intros Hpc2. unfold smut_demonic_match_enum. cbn. *)
  (*   unfold smut_wp at 1. *)
  (*   destruct (term_get_lit_spec (subst (T := fun Σ => Term Σ (ty_enum E)) t ζ12)) as [k Heqιs|]; cbn [Lit] in *. *)
  (*   - fold_smut_wp. specialize (Heqιs ι2). rewrite inst_subst in Heqιs. now rewrite Heqιs. *)
  (*   - fold_smut_wp. rewrite smut_wp_demonic_finite. split; intros Hwp. *)
  (*     + specialize (Hwp (inst (T := fun Σ => Term Σ _) t (inst ζ12 ι2))). *)
  (*       rewrite smut_wp_bind_right, smut_wp_assume_formula, smut_wp_sub in Hwp; auto. *)
  (*       rewrite sub_comp_id_right, inst_sub_id in Hwp. cbn in Hwp. *)
  (*       inster Hwp by now rewrite inst_subst. revert Hwp. *)
  (*       eapply d_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto. *)
  (*       now apply smut_sub_dcl. *)
  (*     + intros x. rewrite smut_wp_bind_right; auto. *)
  (*       rewrite smut_wp_assume_formula; auto. cbn. *)
  (*       rewrite inst_subst, inst_sub_id. intros <-. *)
  (*       rewrite smut_wp_sub. rewrite sub_comp_id_right. revert Hwp. *)
  (*       eapply d_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto. *)
  (*       now apply smut_sub_dcl. *)
  (*     + intros x. *)
  (*       apply smut_bind_right_dcl. *)
  (*       apply smut_assume_formula_dcl. *)
  (*       now apply smut_sub_dcl. *)
  (*     + assumption. *)
  (* Qed. *)

  Lemma smut_wp_demonic_match_sum {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ0} (x y : 𝑺) (σ τ : Ty) (s : Term Σ0 (ty_sum σ τ))
    (dinl : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 σ -> SMut Γ1 Γ2 AT Σ1) (dinl_dcl : smut_arrow_dcl dinl)
    (dinr : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 τ -> SMut Γ1 Γ2 AT Σ1) (dinr_dcl : smut_arrow_dcl dinr)
    Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ι1 : SymInstance Σ1)
    (P : A -> SCProp Γ2) (Hpc : instpc pc1 ι1) :
    smut_wp (smut_demonic_match_sum x y s dinl dinr) ζ01 pc1 δ1 h1 ι1 P <->
    (forall vl,
        inst (T := fun Σ => Term Σ _) (A := Lit σ + Lit τ) s (inst ζ01 ι1) =
        @inl (Lit σ) (Lit τ) vl ->
        smut_wp (dinl _ (sub_id _) (term_lit σ vl)) ζ01 pc1 δ1 h1 ι1 P) /\
    (forall vr,
        inst (T := fun Σ => Term Σ (ty_sum σ τ)) (A := Lit σ + Lit τ) s (inst ζ01 ι1) =
        @inr (Lit σ) (Lit τ) vr ->
        smut_wp (dinr _ (sub_id _) (term_lit τ vr)) ζ01 pc1 δ1 h1 ι1 P).
  Proof.
    (* unfold smut_demonic_match_sum. *)
    (* unfold smut_wp at 1. cbn. *)
    (* destruct (term_get_sum_spec (subst (T := fun Σ => Term Σ (ty_sum σ τ)) s ζ01)) as [[sl|sr] Heqιs|_]. *)
    (* - fold_smut_wp. specialize (Heqιs ι1). rewrite inst_subst in Heqιs. split. *)
    (*   + intros Hwp. split. *)
    (*     * intros v Heq. revert Hwp. rewrite Heqιs in Heq. *)
    (*       apply noConfusion_inv in Heq. cbn in Heq. subst v. *)
    (*       eapply dinl_dcl; rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_snoc; eauto. *)
    (*     * intros v Heq. rewrite Heqιs in Heq. discriminate. *)
    (*   + intros [Hl Hr]. specialize (Hl (inst sl ι1) Heqιs). revert Hl. *)
    (*     eapply dinl_dcl; rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_snoc; eauto. *)
    (* - fold_smut_wp. specialize (Heqιs ι1). rewrite inst_subst in Heqιs. split. *)
    (*   + intros Hwp. split. *)
    (*     * intros v Heq. rewrite Heqιs in Heq. discriminate. *)
    (*     * intros v Heq. revert Hwp. rewrite Heqιs in Heq. *)
    (*       apply noConfusion_inv in Heq. cbn in Heq. subst v. *)
    (*       eapply dinr_dcl; rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_snoc; eauto. *)
    (*   + intros [Hl Hr]. specialize (Hr (inst sr ι1) Heqιs). revert Hr. *)
    (*     eapply dinr_dcl; rewrite ?inst_subst, ?inst_sub_id, ?inst_sub_snoc; eauto. *)
    (* - fold_smut_wp. unfold smut_demonic_match_sum'. *)
    (*   rewrite smut_wp_demonic_binary, ?smut_wp_bind, ?smut_wp_demonic_termvar; auto. *)
    (*   { split; intros [Hl Hr]; *)
    (*       (split; [clear Hr|clear Hl]). *)
    (*     - intros v Heq. specialize (Hl v). *)
    (*       rewrite smut_wp_bind_right, smut_wp_assume_formula in Hl; auto. *)
    (*       cbn in Hl. fold_inst_term. *)
    (*       rewrite ?subst_sub_id, ?inst_subst, ?inst_sub_id, ?inst_lift in Hl. *)
    (*       specialize (Hl Heq). revert Hl. *)
    (*       eapply dinl_dcl; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto. *)
    (*       admit. *)
    (*     - intros v Heq. specialize (Hr v). *)
    (*       rewrite smut_wp_bind_right, smut_wp_assume_formula in Hr; auto. *)
    (*       cbn in Hr. fold_inst_term. *)
    (*       rewrite ?subst_sub_id, ?inst_subst, ?inst_sub_id, ?inst_lift in Hr. *)
    (*       specialize (Hr Heq). revert Hr. *)
    (*       eapply dinr_dcl; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto. *)
    (*       admit. *)
    (*     - intros v. specialize (Hl v). *)
    (*       rewrite smut_wp_bind_right, smut_wp_assume_formula; auto. cbn. *)
    (*       fold_inst_term. *)
    (*       rewrite ?subst_sub_id, ?inst_subst, ?inst_sub_id, ?inst_lift. *)
    (*       intros Heq. specialize (Hl Heq). revert Hl. *)
    (*       eapply dinl_dcl; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto. *)
    (*       admit. *)
    (*     - intros v. specialize (Hr v). *)
    (*       rewrite smut_wp_bind_right, smut_wp_assume_formula; auto. cbn. *)
    (*       fold_inst_term. *)
    (*       rewrite ?subst_sub_id, ?inst_subst, ?inst_sub_id, ?inst_lift. *)
    (*       intros Heq. specialize (Hr Heq). revert Hr. *)
    (*       eapply dinr_dcl; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto. *)
    (*       admit. *)
    (*   } *)
    (*   admit. *)
    (*   admit. *)
  Admitted.

  (* Definition smut_wp_demonic_match_pair {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (x y : 𝑺) (σ τ : Ty) (s : Term Σ1 (ty_prod σ τ)) *)
  (*   (d : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (d_dcl : smut_dcl d) *)
  (*   Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 ι2 (Hpc : instpc pc2 ι2) P : *)
  (*   smut_wp (smut_demonic_match_pair x y s d) ζ12 pc2 δ2 h2 ι2 P <-> *)
  (*   (forall sl sr, *)
  (*       inst (T := fun Σ => Term Σ _) (A := Lit (ty_prod σ τ)) s (inst ζ12 ι2) = *)
  (*       (inst (T := fun Σ => Term Σ _) (A := Lit σ) sl ι2, *)
  (*        inst (T := fun Σ => Term Σ _) (A := Lit τ) sr ι2) -> *)
  (*       smut_wp d (sub_snoc (sub_snoc ζ12 (x :: σ) sl) (y :: τ) sr) pc2 δ2 h2 ι2 P). *)
  (* Proof. *)
  (*   unfold smut_demonic_match_pair. cbn - [sub_wk1]. *)
  (*   unfold smut_wp at 1. *)
  (*   destruct (term_get_pair_spec (subst (T := fun Σ => Term Σ _) s ζ12)) as [[sl sr] Heqs|]; *)
  (*     fold_smut_wp. *)
  (*   - specialize (Heqs ι2). rewrite inst_subst in Heqs. split; auto. *)
  (*     intros Hwp sl2 sr2 Heqs2. rewrite Heqs2 in Heqs. *)
  (*     inversion Heqs. revert Hwp. *)
  (*     eapply d_dcl; rewrite ?inst_subst, ?inst_sub_snoc, ?inst_sub_id, ?inst_lift; auto. *)
  (*     f_equal; auto. f_equal; auto. *)
  (*   - split; intros Hwp. *)
  (*     { intros sl sr Heqs. *)
  (*       rewrite smut_wp_demonicv in Hwp; auto. specialize (Hwp (inst sl ι2)). *)
  (*       rewrite smut_wp_demonicv in Hwp; auto. specialize (Hwp (inst sr ι2)). *)
  (*       rewrite smut_wp_bind_right in Hwp; auto. *)
  (*       rewrite smut_wp_assume_formula in Hwp; auto. *)
  (*       rewrite ?inst_sub_snoc in Hwp. cbn - [sub_wk1] in Hwp. *)
  (*       rewrite ?inst_subst, ?inst_sub_wk1 in Hwp. *)
  (*       specialize (Hwp Heqs). revert Hwp. *)
  (*       eapply d_dcl; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; eauto. *)
  (*       - apply smut_bind_right_dcl; auto. *)
  (*         apply smut_assume_formula_dcl. *)
  (*       - apply smut_demonicv_dcl. *)
  (*         apply smut_bind_right_dcl; auto. *)
  (*         apply smut_assume_formula_dcl. *)
  (*     } *)
  (*     { rewrite smut_wp_demonicv; auto. intros vl. *)
  (*       rewrite smut_wp_demonicv; auto. intros vr. *)
  (*       rewrite smut_wp_bind_right; auto. *)
  (*       rewrite smut_wp_assume_formula; auto. *)
  (*       rewrite ?inst_sub_snoc. cbn - [sub_wk1]. *)
  (*       rewrite ?inst_subst, ?inst_sub_wk1. intros Heqs. *)
  (*       specialize (Hwp (lift vl) (lift vr) Heqs). revert Hwp. *)
  (*       eapply d_dcl; rewrite ?inst_subst, ?inst_sub_id, ?inst_lift; eauto. *)
  (*       - apply smut_bind_right_dcl; auto. *)
  (*         apply smut_assume_formula_dcl. *)
  (*       - apply smut_demonicv_dcl. *)
  (*         apply smut_bind_right_dcl; auto. *)
  (*         apply smut_assume_formula_dcl. *)
  (*     } *)
  (* Qed. *)

  (* Lemma smut_wp_demonic_match_record {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Δ} (t : Term Σ1 (ty_record R)) *)
  (*   (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (d : SMut Γ1 Γ2 AT (Σ1 ▻▻ Δ)) (d_dcl : smut_dcl d) *)
  (*   Σ2 (ζ12 : Sub Σ1 Σ2) pc2 δ2 h2 (ι2 : SymInstance Σ2) (Hpc : instpc ι2 pc2) *)
  (*   (P : A -> SCProp Γ2) : *)
  (*   smut_wp (smut_demonic_match_record p t d) ζ12 pc2 δ2 h2 ι2 P <-> *)
  (*   forall ts : NamedEnv (Term _) (𝑹𝑭_Ty R), *)
  (*     inst (T := fun Σ => Term Σ _) (A := Lit (ty_record R)) (inst ι2 ζ12) t = 𝑹_fold (inst ι2 ts) -> *)
  (*     smut_wp d (ζ12 ►► record_pattern_match_env p ts) pc2 δ2 h2 ι2 P. *)
  (* Proof. *)
  (*   unfold smut_demonic_match_record. cbn. *)
  (*   unfold smut_wp at 1. *)
  (*   destruct (term_get_record_spec (subst (T := fun Σ => Term Σ _) ζ12 t)) as [ts Heqts|]; *)
  (*     fold_smut_wp. *)
  (*   - specialize (Heqts ι2). rewrite inst_subst in Heqts. split; auto. *)
  (*     intros Hwp ts2 Heqts2. rewrite Heqts2 in Heqts. *)
  (*     apply (f_equal (@𝑹_unfold R)) in Heqts. *)
  (*     rewrite ?𝑹_unfold_fold in Heqts. revert Hwp. *)
  (*     eapply d_dcl; rewrite ?inst_sub_id; eauto. *)
  (*     unfold inst; cbn. rewrite ?env_map_cat. *)
  (*     f_equal. *)
  (*     change (inst ι2 (record_pattern_match_env p ts) = inst ι2 (record_pattern_match_env p ts2)). *)
  (*     now rewrite ?inst_record_pattern_match, Heqts. *)
  (*   - rewrite smut_wp_bind; auto. *)
  (*     split; intros Hwp. *)
  (*     { intros ts Heqts. *)
  (*       unfold smut_demonic_freshen_recordpat in Hwp. *)
  (*       rewrite smut_wp_fmap in Hwp; auto. *)
  (*       rewrite smut_wp_demonic_freshen_recordpat' in Hwp; auto. *)
  (*       specialize (Hwp (inst ι2 ts) _ eq_refl). *)
  (*       rewrite <- inst_record_pattern_match in Hwp. *)
  (*       remember (record_pattern_match p ts) as ts__R. *)
  (*       cbn - [smut_wp inst_term] in Hwp. *)
  (*       rewrite subst_sub_id, inst_lift in Hwp. *)
  (*       rewrite smut_wp_bind_right, smut_wp_assume_formula in Hwp; auto. *)
  (*       cbn - [inst_term] in Hwp. fold_inst_term. *)
  (*       rewrite inst_lift in Hwp. rewrite Heqts in Hwp. *)
  (*       cbn in Hwp. inster Hwp by admit. *)
  (*       rewrite inst_lift, smut_wp_sub in Hwp. *)
  (*       revert Hwp. *)
  (*       eapply d_dcl; rewrite ?inst_subst, ?inst_lift, ?inst_sub_id; eauto. *)
  (*       unfold inst; cbn. *)
  (*       rewrite ?env_map_cat. *)
  (*       f_equal. *)
  (*       change (inst (inst ι2 ζ12) (sub_id Σ1) = inst ι2 ζ12). *)
  (*       now rewrite inst_sub_id. *)
  (*       change (inst (inst ι2 ζ12) (lift (inst ι2 ts__R)) = inst ι2 ts__R). *)
  (*       now rewrite inst_lift. *)
  (*       now apply smut_sub_dcl. *)
  (*       clear. unfold Path.mapping_dcl. destruct a1, a2; cbn - [inst_term]. *)
  (*       intros. fold_inst_term. subst. inversion H1. f_equal; auto. *)
  (*       admit. *)
  (*     } *)
  (* Admitted. *)

  Lemma spath_dcl_smut {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0 Σ1}
    (dt : SMut Γ1 Γ2 AT Σ0) (dt_dcl : smut_dcl dt) (pc1 : PathCondition Σ1)
    (δ1 : SStore Γ1 Σ1) (h1 : SHeap Σ1) (ζ01 : Sub Σ0 Σ1) :
    Path.dcl pc1 (fun Σ2 ζ12 pc2 => dt Σ2 (subst ζ01 ζ12) pc2 (subst δ1 ζ12) (subst h1 ζ12)).
  Proof.
    unfold Path.dcl.
    intros P Q PQ Σ2 ζ12 pc2 Σ3 ζ13 pc3 ζ23 ι2 ι3 Hι Hpc2 Hpc3 Hζ.
    pose proof (dt_dcl _ _ (subst ζ01 ζ12) pc2 (subst δ1 ζ12) (subst h1 ζ12) ζ23 pc3) as Hdcl.
    specialize (Hdcl (subst δ1 ζ13) (subst h1 ζ13) (subst ζ01 (subst ζ12 ζ23)) ι2 ι3).
    subst ι2. rewrite ?inst_subst, ?Hζ in Hdcl. inster Hdcl by auto.
    specialize (Hdcl (fun b δ h => P (MkCMutResult b δ h)) (fun b δ h => Q (MkCMutResult b δ h))).
    inster Hdcl by auto. intros Hwp.
    match type of Hdcl with
    | ?Hwp2 -> _ =>
      assert Hwp2 as Hwp23
    end.
    { revert Hwp. apply Path.wp_monotonic; now intros []. }
    clear Hwp. apply Hdcl in Hwp23. revert Hwp23. clear Hdcl.
    specialize (dt_dcl Σ3 Σ3 (subst ζ01 (subst ζ12 ζ23)) pc3 (subst δ1 ζ13) (subst h1 ζ13)).
    specialize (dt_dcl (sub_id _) pc3 (subst δ1 ζ13) (subst h1 ζ13)).
    specialize (dt_dcl (subst ζ01 ζ13) ι3 ι3).
    rewrite ?inst_sub_id, ?inst_subst, Hζ in dt_dcl. inster dt_dcl by auto.
    specialize (dt_dcl (fun b δ h => Q (MkCMutResult b δ h))).
    specialize (dt_dcl (fun b δ h => Q (MkCMutResult b δ h))).
    intros Hwp. apply dt_dcl in Hwp. revert Hwp.
    apply Path.wp_monotonic. intros []; cbn; auto. auto.
  Qed.

  Lemma smut_demonic_match_bool_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (s : Term Σ ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ) (dt_dcl : smut_dcl dt) (df_dcl : smut_dcl df) :
    smut_dcl (smut_demonic_match_bool s dt df).
  Proof.
    unfold smut_dcl, smut_geq. intros * Hι Hpc1 Hpc2 Hδ Hh Hζ P Q PQ.
    unfold smut_wp, smut_demonic_match_bool.
    rewrite ?Path.wp_demonic_match_bool, ?inst_subst; auto with dcl.
    rewrite Hζ. unfold T, smut_sub.
    destruct (inst s (inst ζ02 ι2)); rewrite ?subst_sub_id.
    eapply dt_dcl; eauto. eapply df_dcl; eauto.
    now apply spath_dcl_smut.
    now apply spath_dcl_smut.
    now apply spath_dcl_smut.
    now apply spath_dcl_smut.
  Qed.

  Lemma smut_angelic_match_bool_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (s : Term Σ ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ) (dt_dcl : smut_dcl dt) (df_dcl : smut_dcl df) :
    smut_dcl (smut_angelic_match_bool s dt df).
  Proof.
    intros until Q; intros PQ. rewrite ?smut_wp_angelic_match_bool; auto.
    rewrite H8. intros [[? Hwp]|[? Hwp]]; [left|right]; split; auto; revert Hwp.
    - eapply dt_dcl; rewrite ?inst_lift; auto.
    - eapply df_dcl; rewrite ?inst_lift; auto.
  Qed.

  Lemma smut_angelic_match_enum_dcl {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
    (d : 𝑬𝑲 E -> SMut Γ1 Γ2 AT Σ1) (d_dcl : forall K, smut_dcl (d K)) :
    smut_dcl (smut_angelic_match_enum t d).
  Proof.
  Admitted.

  Lemma smut_demonic_match_enum_dcl {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
    (d : 𝑬𝑲 E -> SMut Γ1 Γ2 AT Σ1) (d_dcl : forall K, smut_dcl (d K)) :
    smut_dcl (smut_demonic_match_enum t d).
  Proof.
  Admitted.

  (* Lemma smut_demonic_match_sum_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ x y σ τ} (s : Term Σ (ty_sum σ τ)) *)
  (*   (dinl : SMut Γ1 Γ2 AT (Σ ▻ (x :: σ))) (dinl_dcl : smut_dcl dinl) *)
  (*   (dinr : SMut Γ1 Γ2 AT (Σ ▻ (y :: τ))) (dinr_dcl : smut_dcl dinr) : *)
  (*   smut_dcl (smut_demonic_match_sum s dinl dinr). *)
  (* Proof. *)
  (*   intros until Q; intros PQ. rewrite ?smut_wp_demonic_match_sum; auto. cbn. *)
  (*   intros [Hl Hr]. *)
  (*   split. *)
  (*   - intros sl Heq. specialize (Hl (lift (inst ι2 sl))). *)
  (*     inster Hl by (rewrite inst_lift; intuition). revert Hl. *)
  (*     eapply dinl_dcl; rewrite ?inst_sub_snoc, ?inst_lift; auto. *)
  (*     f_equal. auto. *)
  (*   - intros sr Heq. specialize (Hr (lift (inst ι2 sr))). *)
  (*     inster Hr by (rewrite inst_lift; intuition). revert Hr. *)
  (*     eapply dinr_dcl; rewrite ?inst_sub_snoc, ?inst_lift; auto. *)
  (*     f_equal. auto. *)
  (* Qed. *)

  (* Lemma smut_demonic_match_pair_dcl {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 x y σ τ} (s : Term Σ1 (ty_prod σ τ)) *)
  (*   (d : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (d_dcl : smut_dcl d) : *)
  (*   smut_dcl (smut_demonic_match_pair s d). *)
  (* Proof. *)
  (*   intros until Q; intros PQ. rewrite ?smut_wp_demonic_match_pair; auto. *)
  (*   intros Hwp sl sr Heqs. specialize (Hwp (lift (inst sl ι2)) (lift (inst sr ι2))). *)
  (*   rewrite ?inst_lift in Hwp. rewrite <- H8 in Heqs. specialize (Hwp Heqs). revert Hwp. *)
  (*   eapply d_dcl; rewrite ?inst_sub_snoc, ?inst_lift; auto. *)
  (*   f_equal; auto. f_equal; auto. *)
  (* Qed. *)

  (* Lemma smut_demonic_match_record_dcl {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1 Δ} (t : Term Σ1 (ty_record R)) *)
  (*   (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (d : SMut Γ1 Γ2 AT (Σ1 ▻▻ Δ)) (d_dcl : smut_dcl d) : *)
  (*   smut_dcl (@smut_demonic_match_record AT R Γ1 Γ2 Σ1 Δ p t d). *)
  (* Proof. *)
  (*   intros until Q; intros PQ. rewrite ?smut_wp_demonic_match_record; auto. *)
  (*   intros Hwp ζ__R Heqs. specialize (Hwp (lift (inst ι2 ζ__R))). *)
  (*   rewrite ?inst_lift in Hwp. rewrite <- H8 in Heqs. specialize (Hwp Heqs). revert Hwp. *)
  (*   eapply d_dcl; eauto. unfold inst at 1 3; cbn. rewrite ?env_map_cat. *)
  (*   f_equal. exact H8. admit. *)
  (* Admitted. *)

  Lemma smut_produce_chunk_dcl {Γ Σ} (c : Chunk Σ) :
    smut_dcl (Γ1 := Γ) (smut_produce_chunk c).
  Proof.
    unfold smut_produce_chunk. apply smut_state_dcl.
    intros * -> Hδ Hh Hζ. cbn.
    change (List.map (fun x => inst x ?ι) ?h) with (inst h ι).
    rewrite ?inst_subst. congruence.
  Qed.

  Lemma smut_debug_dcl {AT A DT D} `{InstLaws AT A, Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2 Σ1}
    (d : forall Σ2 : LCtx, Sub Σ1 Σ2 -> PathCondition Σ2 -> SStore Γ1 Σ2 -> SHeap Σ2 -> DT Σ2)
    (k : SMut Γ1 Γ2 AT Σ1) (k_dcl : smut_dcl k) :
    smut_dcl (smut_debug d k).
  Proof.
    intros until Q; intros PQ.
    rewrite ?smut_wp_debug.
    eapply k_dcl; eauto.
  Qed.

  Lemma smut_produce_dcl {Γ Σ} (asn : Assertion Σ) :
    smut_dcl (Γ1 := Γ) (smut_produce asn).
  Proof.
    induction asn; cbn.
    - apply smut_assume_formula_dcl.
    - apply smut_produce_chunk_dcl.
    - now apply smut_demonic_match_bool_dcl.
    - now apply smut_demonic_match_enum_dcl.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - now apply smut_bind_right_dcl.
    - admit.
    - apply smut_debug_dcl, smut_pure_dcl.
  Admitted.

  Lemma smut_consume_chunk_dcl {Γ Σ} (c : Chunk Σ) :
    smut_dcl (Γ1 := Γ) (smut_consume_chunk c).
  Proof.
  Admitted.

  Lemma smut_consume_dcl {Γ Σ} (asn : Assertion Σ) :
    smut_dcl (Γ1 := Γ) (smut_consume asn).
  Proof.
    induction asn; cbn.
    - apply smut_assert_formula_dcl.
    - apply smut_consume_chunk_dcl.
    - now apply smut_angelic_match_bool_dcl.
    - now apply smut_angelic_match_enum_dcl.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - now apply smut_bind_right_dcl.
    - admit.
    - apply smut_debug_dcl, smut_pure_dcl.
  Admitted.

  Lemma smut_exec_dcl {Γ τ Σ} (s : Stm Γ τ) :
    smut_dcl (Σ0 := Σ) (smut_exec s).
  Proof. Admitted.

  Definition APPROX Γ1 Γ2 AT A {instA : Inst AT A} : Type :=
    forall Σ (ι : SymInstance Σ),
      SMut Γ1 Γ2 AT Σ -> CMut Γ1 Γ2 A -> Prop.
  Arguments APPROX _ _ _ _ {_}.

  Definition bapprox {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
    fun Σ0 ι0 dm sm =>
      forall Σ1 (ζ01 : Sub Σ0 Σ1) (pc1 : PathCondition Σ1) (ι1 : SymInstance Σ1) POST δ1 h1,
        ι0 = inst ζ01 ι1 ->
        instpc pc1 ι1 ->
        smut_wp dm ζ01 pc1 δ1 h1 ι1 POST ->
        cmut_wp sm POST (inst δ1 ι1) (inst h1 ι1).

  Definition bapprox2 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
    fun Σ0 ι0 dm sm =>
      forall POST δ h,
        smut_wp dm (lift ι0) nil (lift δ) (lift h) env_nil POST ->
        cmut_wp sm POST δ h.

  Lemma bapprox_bapprox2 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (dm_dcl : smut_dcl dm) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm <-> bapprox2 ι dm sm.
  Proof.
    unfold bapprox, bapprox2. split; intros HYP.
    - intros POST δ h Hwp.
      specialize (HYP ctx_nil (lift ι) nil env_nil POST (lift δ) (lift h)).
      rewrite ?inst_lift in HYP. apply HYP; auto. constructor.
    - intros ? ? ? ? ? ? ? Hι Hpc Hwp. specialize (HYP POST (inst δ1 ι1) (inst h1 ι1)).
      apply HYP. revert Hwp.
      apply (dm_dcl Σ1 ε ζ01 _ _ _ (lift ι1)); rewrite ?inst_lift; auto.
      constructor.
  Qed.

  Definition inst_dmut {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (d : SMut Γ1 Γ2 AT Σ) : CMut Γ1 Γ2 A :=
    fun δ h => inst_spath (d Σ (sub_id Σ) nil (lift δ) (lift h)) ι.
  Definition inst_dmut' {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (d : SMut Γ1 Γ2 AT Σ) : CMut Γ1 Γ2 A :=
    fun δ h => inst_spath (d ctx_nil (lift ι) nil (lift δ) (lift h)) env_nil.

  Definition bapprox3 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
    fun Σ0 ι0 dm sm =>
      forall POST δ h,
        cmut_wp (inst_dmut ι0 dm) POST δ h ->
        cmut_wp sm POST δ h.

  Definition bapprox4 {Γ1 Γ2 AT A} {instA : Inst AT A} : APPROX Γ1 Γ2 AT A :=
    fun Σ0 ι0 dm sm =>
      forall POST δ h,
        cmut_wp (inst_dmut' ι0 dm) POST δ h ->
        cmut_wp sm POST δ h.

  Lemma bapprox_bapprox3 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (dm_dcl : smut_dcl dm) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm <-> bapprox3 ι dm sm.
  Proof.
    split; unfold bapprox, bapprox3; intros HYP.
    - intros POST δ h Hwp.
      specialize (HYP Σ (sub_id _) nil ι POST (lift δ) (lift h)).
      inster HYP by rewrite ?inst_sub_id; constructor.
      rewrite ?inst_lift in HYP. apply HYP.
      unfold smut_wp. rewrite Path.wp_wp'. exact Hwp.
    - intros ? ? ? ? ? ? ? Hι Hpc Hwp. apply HYP.
      unfold cmut_wp, inst_dmut.
      (* change (Path.wp' (dm Σ (sub_id Σ) nil (lift (inst ι1 δ1)) (lift (inst ι1 h1))) ι *)
      (*                  (fun X : CMutResult Γ2 A => POST (scmutres_value X) (scmutres_state X))). *)
      (* rewrite <- Path.wp_wp'. fold_smut_wp. revert Hwp. *)
      (* eapply dm_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto. *)
      (* constructor. *)
  Admitted.

  Lemma bapprox_bapprox4 {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (dm_dcl : smut_dcl dm) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm <-> bapprox4 ι dm sm.
  Proof.
    split; unfold bapprox, bapprox4; intros HYP.
    - intros POST δ h Hwp.
      specialize (HYP ctx_nil (lift ι) nil env_nil POST (lift δ) (lift h)).
      inster HYP by rewrite ?inst_lift; constructor.
      rewrite ?inst_lift in HYP. apply HYP.
      unfold smut_wp. rewrite Path.wp_wp'. exact Hwp.
    - intros ? ? ? ? ? ? ? Hι Hpc Hwp. apply HYP.
      unfold cmut_wp, inst_dmut'.
      (* change (Path.wp' (dm ctx_nil (lift ι) nil (lift (inst ι1 s1))) env_nil *)
      (*                  (fun X : CMutResult Γ2 A => POST (scmutres_value X) (scmutres_state X))). *)
      (* rewrite <- Path.wp_wp'. fold_smut_wp. revert Hwp. *)
      (* eapply dm_dcl; rewrite ?inst_sub_id, ?inst_lift; eauto. *)
      (* constructor. *)
  Admitted.

  Lemma bapprox_demonic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
        (dm1 dm2 : SMut Γ1 Γ2 AT Σ) (sm1 sm2 : CMut Γ1 Γ2 A) :
    bapprox ι dm1 sm1 ->
    bapprox ι dm2 sm2 ->
    bapprox ι (smut_demonic_binary dm1 dm2) (cmut_demonic_binary sm1 sm2).
  Proof.
    intros ? ?. unfold bapprox. intros *.
    rewrite smut_wp_demonic_binary, cmut_wp_demonic_binary.
    intuition.
  Qed.

  Lemma bapprox_angelic_binary {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ)
        (dm1 dm2 : SMut Γ1 Γ2 AT Σ) (sm1 sm2 : CMut Γ1 Γ2 A) :
    bapprox ι dm1 sm1 ->
    bapprox ι dm2 sm2 ->
    bapprox ι (smut_angelic_binary dm1 dm2) (cmut_angelic_binary sm1 sm2).
  Proof.
    intros ? ?. unfold bapprox. intros *.
    rewrite smut_wp_angelic_binary, cmut_wp_angelic_binary.
    intuition.
  Qed.

  Lemma bapprox_demonicv {AT A} `{InstLaws AT A} {Γ Σ ς τ} (ι : SymInstance Σ)
        (dm : SMut Γ Γ AT (Σ ▻ (ς,τ))) (d_dcl : smut_dcl dm)
        (sm : Lit τ -> CMut Γ Γ A) :
    (forall v, bapprox (env_snoc ι _ v) dm (sm v)) ->
    bapprox ι
      (smut_demonicv ς τ dm)
      (cmut_demonic sm).
  Proof.
    unfold bapprox. intros HYP * Hι Hpc.
    rewrite smut_wp_demonicv, cmut_wp_demonic; auto.
    intros Hwp vτ.
    apply (HYP vτ _ (sub_snoc ζ01 (ς :: τ) (term_lit τ vτ)) pc1); auto.
    subst ι; reflexivity.
  Qed.

  Lemma bapprox_pure {AT A} `{InstLaws AT A} {Γ Σ} (ι : SymInstance Σ) (t : AT Σ) (a : A) :
    a = inst t ι ->
    bapprox ι (smut_pure (Γ := Γ) t) (cmut_pure a).
  Proof.
    unfold bapprox. intros -> * -> Hpc.
    rewrite smut_wp_pure. intros Hwp; apply Hwp.
  Qed.

  Lemma bapprox_block {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) :
    bapprox ι (@smut_block Γ1 Γ2 AT Σ) cmut_block.
  Proof. unfold bapprox; auto. Qed.

  Lemma bapprox_bind {AT A BT B} `{InstLaws AT A, InstLaws BT B}
    {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
    (dma : SMut Γ1 Γ2 AT Σ0) (sma : CMut Γ1 Γ2 A)
    (dmf : smut_arrow Γ2 Γ3 AT BT Σ0)
    (dmf_dcl : smut_arrow_dcl dmf)
    (smf : A -> CMut Γ2 Γ3 B) :
    bapprox ι0 dma sma ->
    (forall (a0 : AT Σ0),
        bapprox ι0 (dmf Σ0 (sub_id _) a0) (smf (inst a0 ι0))) ->
    bapprox ι0 (smut_bind dma dmf) (cmut_bind sma smf).
  Proof.
    unfold bapprox. intros Hapa Hapf * Hι Hpc.
    rewrite smut_wp_bind; eauto. rewrite cmut_wp_bind.
    intros Hwp. eapply Hapa; eauto. revert Hwp.
    apply smut_wp_monotonic. intros a δ2 h2 Hwp.
    apply Hapf in Hwp; auto. revert Hwp. now rewrite ?inst_lift.
  Qed.

  Lemma bapprox_bind_right {AT A BT B} `{InstLaws AT A, InstLaws BT B}
    {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
    (dma : SMut Γ1 Γ2 AT Σ0) (sma : CMut Γ1 Γ2 A)
    (dmb : SMut Γ2 Γ3 BT Σ0) (dmb_dcl : smut_dcl dmb) (smb : CMut Γ2 Γ3 B) :
    bapprox ι0 dma sma ->
    bapprox ι0 dmb smb ->
    bapprox ι0 (smut_bind_right dma dmb) (cmut_bind_right sma smb).
  Proof.
    unfold bapprox. intros A1 A2 * -> Hpc1.
    rewrite smut_wp_bind_right; auto.
    unfold cmut_bind_right. rewrite cmut_wp_bind.
    intros Hwp; eapply A1 in Hwp; eauto. revert Hwp.
    apply cmut_wp_monotonic; intros a δ2 h2.
    intros Hwp; eapply A2 in Hwp; eauto. revert Hwp.
    now rewrite ?inst_lift.
  Qed.

  Lemma bapprox_bind_left {AT A BT B} `{InstLaws AT A, InstLaws BT B}
    {Γ1 Γ2 Γ3 Σ0} (ι0 : SymInstance Σ0)
    (dma : SMut Γ1 Γ2 AT Σ0) (sma : CMut Γ1 Γ2 A)
    (dmb : SMut Γ2 Γ3 BT Σ0) (dmb_dcl : smut_dcl dmb) (smb : CMut Γ2 Γ3 B) :
    bapprox ι0 dma sma ->
    bapprox ι0 dmb smb ->
    bapprox ι0 (smut_bind_left dma dmb) (cmut_bind_left sma smb).
  Proof.
    intros A1 A2. unfold bapprox. intros * -> Hpc1.
    rewrite smut_wp_bind_left; auto.
    unfold cmut_bind_left. rewrite cmut_wp_bind.
    intros Hwp; eapply A1 in Hwp; eauto. revert Hwp.
    apply cmut_wp_monotonic; intros a δ2 h2. rewrite cmut_wp_bind.
    intros Hwp; eapply A2 in Hwp; eauto. revert Hwp.
    now rewrite ?inst_lift.
  Qed.

  Lemma bapprox2_assume_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
    bapprox2
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_assume_formula fml)
      (cmut_assume_formula ι fml).
  Proof.
    unfold bapprox2. intros POST δ h.
    rewrite smut_wp_assume_formula; auto. rewrite ?inst_lift.
    intuition.
    constructor.
  Qed.

  Lemma bapprox_angelic {AT A} `{InstLaws AT A} (x : option 𝑺) (σ : Ty) {Γ1 Γ2 Σ0} (ι0 : SymInstance Σ0)
    (dm : forall Σ1, Sub Σ0 Σ1 -> Term Σ1 σ -> SMut Γ1 Γ2 AT Σ1) (dm_dcl : smut_arrow_dcl dm)
    (sm : Lit σ -> CMut Γ1 Γ2 A) :
    (forall v : Lit σ, bapprox ι0 (dm Σ0 (sub_id _) (lift v)) (sm v)) ->
    bapprox ι0
      (smut_angelic x σ dm)
      (cmut_angelic sm).
  Proof.
    intros HYP. unfold bapprox. intros * Hι Hpc.
    rewrite smut_wp_angelic, cmut_wp_angelic; auto.
    intros [v Hwp]. exists v. revert Hwp. apply HYP; auto.
  Qed.

  Lemma bapprox_sub {AT A} `{Inst AT A, Subst AT} {Γ Σ0 Σ1} (ζ01 : Sub Σ0 Σ1)
    (d : SMut Γ Γ AT Σ0) (s : CMut Γ Γ A) (ι0 : SymInstance Σ0) (ι1 : SymInstance Σ1) :
    ι0 = inst ζ01 ι1 ->
    bapprox ι0 d s -> bapprox ι1 (smut_sub ζ01 d) s.
  Proof.
    intros Hι0 Hap. unfold bapprox. intros * Hι1 Hpc2.
    rewrite smut_wp_sub. apply Hap; auto.
    rewrite inst_subst; now subst.
  Qed.

  Lemma bapprox_assume_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_assume_formula fml)
      (cmut_assume_formula ι fml).
  Proof.
    unfold bapprox. intros * -> Hpc Hwp Hfml. revert Hwp.
    rewrite smut_wp_assume_formula; eauto. cbn. intuition.
  Qed.

  Lemma bapprox_assert_formula {Γ Σ} (ι : SymInstance Σ) (fml : Formula Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_assert_formula fml)
      (cmut_assert_formula ι fml).
  Proof.
    unfold bapprox. intros * Hι Hpc1.
    rewrite smut_wp_assert_formula, cmut_wp_assert_formula; auto.
    intuition.
  Qed.

  Lemma bapprox_assert_formulak {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (fml : Formula Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (dm_dcl : smut_dcl dm) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm ->
    bapprox ι (smut_assert_formulak fml dm) (cmut_assert_formulak ι fml sm).
  Proof.
    intros HYP. unfold bapprox. intros * -> Hpc.
    rewrite smut_wp_assert_formulak; auto.
    rewrite cmut_wp_assert_formulak.
    intros [Hfml Hwp]; split; auto; revert Hwp.
    apply HYP; auto.
  Qed.

  Lemma bapprox_assert_formulask {AT A} `{Inst AT A} {Γ1 Γ2 Σ} (ι : SymInstance Σ) (fmls : List Formula Σ)
    (dm : SMut Γ1 Γ2 AT Σ) (sm : CMut Γ1 Γ2 A) :
    bapprox ι dm sm ->
    bapprox ι (smut_assert_formulask fmls dm) (cmut_assert_formulask ι fmls sm).
  Proof.
  Admitted.

  Lemma bapprox_state {AT A} `{Subst AT, Inst AT A} {Γ1 Γ2 Σ0} (ι0 : SymInstance Σ0)
    (f : forall Σ1 (ζ01 : Sub Σ0 Σ1), SStore Γ1 Σ1 -> SHeap Σ1 -> SMutResult Γ2 AT Σ1)
    (g : LocalStore Γ1 -> SCHeap -> CMutResult Γ2 A)
    (fg : forall Σ1 ζ01 δ1 h1 ι1,
        ι0 = inst ζ01 ι1 -> inst (f Σ1 ζ01 δ1 h1) ι1 = g (inst δ1 ι1) (inst h1 ι1)) :
    bapprox ι0 (smut_state f) (cmut_state g).
  Proof.
    unfold bapprox. intros * Hι Hpc.
    rewrite smut_wp_state, cmut_wp_state.
    specialize (fg Σ1 ζ01 δ1 h1 ι1 Hι).
    destruct (f Σ1 ζ01 _ _) as [a1 δ2 h2]. cbn in *.
    destruct (g _ _) as [a δ3 h3].
    inversion fg. now subst.
  Qed.

  Lemma bapprox_produce_chunk {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_produce_chunk c)
      (cmut_produce_chunk (inst c ι)).
  Proof.
    unfold bapprox. intros * Hι Hpc.
    unfold smut_produce_chunk, cmut_produce_chunk.
    rewrite smut_wp_state, cmut_wp_state. cbn. subst.
    now rewrite inst_subst.
  Qed.

  Lemma bapprox_angelic_match_bool {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (s : Term Σ1 ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ1) (dt_dcl : smut_dcl dt) (df_dcl : smut_dcl df)
    (st sf : CMut Γ1 Γ2 A) (ι : SymInstance Σ1) :
    bapprox ι dt st ->
    bapprox ι df sf ->
    bapprox
      ι
      (smut_angelic_match_bool s dt df)
      (cmut_match_bool (inst s ι) st sf).
  Proof.
    intros ? ?. unfold bapprox. intros * -> ?.
    unfold smut_wp, smut_angelic_match_bool.
    (* rewrite Path.wp_angelic_match_bool, *)
    (*   cmut_wp_match_bool, ?inst_subst; auto. *)
    (* unfold T. destruct (inst s (inst ζ01 ι1)); fold_smut_wp. *)
    (* - rewrite smut_wp_sub, ?subst_sub_id. *)
    (*   apply H3; auto. *)
    (* - rewrite smut_wp_sub, ?subst_sub_id. *)
    (*   apply H4; auto. *)
    (* - now apply spath_dcl_smut. *)
    (* - now apply spath_dcl_smut. *)
  Admitted.

  Lemma bapprox_demonic_match_bool {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} (s : Term Σ1 ty_bool)
    (dt df : SMut Γ1 Γ2 AT Σ1) (dt_dcl : smut_dcl dt) (df_dcl : smut_dcl df)
    (st sf : CMut Γ1 Γ2 A) (ι : SymInstance Σ1) :
    bapprox ι dt st ->
    bapprox ι df sf ->
    bapprox
      ι
      (smut_demonic_match_bool s dt df)
      (cmut_match_bool (inst s ι) st sf).
  Proof.
    intros ? ?. unfold bapprox. intros * -> ?.
    unfold smut_wp, smut_demonic_match_bool.
    rewrite Path.wp_demonic_match_bool,
      cmut_wp_match_bool, ?inst_subst; auto.
    unfold T. destruct (inst s (inst ζ01 ι1)); fold_smut_wp.
    - rewrite smut_wp_sub, ?subst_sub_id.
      apply H3; auto.
    - rewrite smut_wp_sub, ?subst_sub_id.
      apply H4; auto.
    - now apply spath_dcl_smut.
    - now apply spath_dcl_smut.
  Qed.

  Lemma bapprox_angelic_match_enum {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
    (dm : Lit (ty_enum E) -> SMut Γ1 Γ2 AT Σ1) (dm_dcl : forall x, smut_dcl (dm x))
    (sm : Lit (ty_enum E) -> CMut Γ1 Γ2 A)
    (ι : SymInstance Σ1) :
    (forall k, bapprox ι (dm k) (sm k)) ->
    bapprox
      ι
      (smut_angelic_match_enum t dm)
      (cmut_match_enum (inst (T := fun Σ => Term Σ (ty_enum E)) t ι) sm).
  Proof.
    (* unfold bapprox. intros Hap * ? Hpc. subst. *)
    (* rewrite smut_wp_demonic_match_enum; auto. now apply Hap. *)
  Admitted.

  Lemma bapprox_demonic_match_enum {AT A E} `{InstLaws AT A} {Γ1 Γ2 Σ1} (t : Term Σ1 (ty_enum E))
    (dm : Lit (ty_enum E) -> SMut Γ1 Γ2 AT Σ1) (dm_dcl : forall x, smut_dcl (dm x))
    (sm : Lit (ty_enum E) -> CMut Γ1 Γ2 A)
    (ι : SymInstance Σ1) :
    (forall k, bapprox ι (dm k) (sm k)) ->
    bapprox
      ι
      (smut_demonic_match_enum t dm)
      (cmut_match_enum (inst (T := fun Σ => Term Σ (ty_enum E)) t ι) sm).
  Proof.
    (* unfold bapprox. intros Hap * ? Hpc. subst. *)
    (* rewrite smut_wp_demonic_match_enum; auto. now apply Hap. *)
  Admitted.


  (* Lemma bapprox_demonic_match_sum {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} {x y : 𝑺} {σ τ} (s : Term Σ1 (ty_sum σ τ)) *)
  (*   (dinl : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ))) (dinl_dcl : smut_dcl dinl) *)
  (*   (dinr : SMut Γ1 Γ2 AT (Σ1 ▻ (y :: τ))) (dinr_dcl : smut_dcl dinr) *)
  (*   (sinl : Lit σ -> CMut Γ1 Γ2 A) (sinr : Lit τ -> CMut Γ1 Γ2 A) (ι : SymInstance Σ1) : *)
  (*   (forall v, bapprox (env_snoc ι _ v) dinl (sinl v)) -> *)
  (*   (forall v, bapprox (env_snoc ι _ v) dinr (sinr v)) -> *)
  (*   bapprox *)
  (*     ι *)
  (*     (smut_demonic_match_sum x y s dinl dinr) *)
  (*     (cmut_match_sum (inst (T := fun Σ => Term Σ (ty_sum σ τ)) (A := Lit σ + Lit τ) ι s) sinl sinr). *)
  (* Proof. *)
  (*   unfold bapprox. intros Hapl Hapr * ? Hpc. *)
  (*   rewrite smut_wp_demonic_match_sum; auto. intros [Hl Hr]. *)
  (*   destruct (inst ι s) eqn:Heqs; [ clear Hr | clear Hl ]; subst ι. *)
  (*   + specialize (Hl (term_lit σ l) Heqs). revert Hl. now apply Hapl. *)
  (*   + specialize (Hr (term_lit τ l) Heqs). revert Hr. now apply Hapr. *)
  (* Qed. *)

  (* Lemma bapprox_demonic_match_pair {AT A} `{InstLaws AT A} {Γ1 Γ2 Σ1} {x y : 𝑺} {σ τ} (s : Term Σ1 (ty_prod σ τ)) *)
  (*   (dm : SMut Γ1 Γ2 AT (Σ1 ▻ (x :: σ) ▻ (y :: τ))) (dm_dcl : smut_dcl dm) *)
  (*   (sm : Lit σ -> Lit τ -> CMut Γ1 Γ2 A) (ι : SymInstance Σ1) : *)
  (*   (forall vl vr, bapprox (env_snoc (env_snoc ι _ vl) _ vr) dm (sm vl vr)) -> *)
  (*   bapprox *)
  (*     ι *)
  (*     (smut_demonic_match_pair s dm) *)
  (*     (cmut_match_pair (inst (T := fun Σ => Term Σ (ty_prod σ τ)) (A := Lit σ * Lit τ) s ι) sm). *)
  (* Proof. *)
  (*   unfold bapprox. intros Hap * ? Hpc. *)
  (*   rewrite smut_wp_demonic_match_pair; auto. intros Hwp. *)
  (*   destruct (inst s ι) as [vl vr] eqn:Heqs. subst ι. *)
  (*   specialize (Hwp (lift vl) (lift vr) Heqs). revert Hwp. *)
  (*   now apply Hap. *)
  (* Qed. *)

  (* Lemma bapprox_demonic_match_record {R AT A} `{InstLaws AT A} {Γ1 Γ2 Σ0 Δ} (t : Term Σ0 (ty_record R)) *)
  (*   (p : @RecordPat 𝑺 (𝑹𝑭_Ty R) Δ) (dm : SMut Γ1 Γ2 AT (Σ0 ▻▻ Δ)) (dm_dcl : smut_dcl dm) *)
  (*   (sm : SymInstance Δ -> CMut Γ1 Γ2 A) (ι : SymInstance Σ0) : *)
  (*   (forall ι__Δ : SymInstance Δ, bapprox (env_cat ι ι__Δ) dm (sm ι__Δ)) -> *)
  (*   bapprox *)
  (*     ι *)
  (*     (smut_demonic_match_record p t dm) *)
  (*     (cmut_match_record p (inst (T := fun Σ => Term Σ (ty_record R)) ι t) sm). *)
  (* Proof. *)
  (*   (* unfold bapprox. intros Hap * Hι Hpc. *) *)
  (*   (* rewrite smut_wp_demonic_match_record; auto. intros Hwp. *) *)
  (*   (* unfold cmut_match_record. *) *)
  (*   (* specialize (Hwp (lift (𝑹_unfold (inst (T := fun Σ => Term Σ _) ι t)))). *) *)
  (*   (* inster Hwp by now rewrite inst_lift, 𝑹_fold_unfold, Hι. *) *)
  (*   (* eapply Hap; eauto. cbn [Lit]. *) *)
  (*   (* generalize (𝑹_unfold (inst (T := fun Σ => Term Σ (ty_record R)) (A := 𝑹𝑻 R) ι t)). *) *)
  (*   (* subst. clear. intros ts. unfold inst at 2; cbn. *) *)
  (*   (* rewrite env_map_cat. f_equal. *) *)
  (*   (* change (record_pattern_match p ts = inst ι1 (record_pattern_match p (lift ts))). *) *)
  (*   (* now rewrite inst_record_pattern_match, inst_lift. *) *)
  (* Admitted. *)

  Lemma bapprox_debug {AT A DT D} `{InstLaws AT A, Subst DT, Inst DT D, OccursCheck DT} {Γ1 Γ2 Σ0}
    (ι : SymInstance Σ0)
    (d : forall Σ1, Sub Σ0 Σ1 -> PathCondition Σ1 -> SStore Γ1 Σ1 -> SHeap Σ1 -> DT Σ1)
    (dm : SMut Γ1 Γ2 AT Σ0) sm :
    bapprox ι dm sm ->
    bapprox ι (smut_debug d dm) sm.
  Proof.
    intros HYP. unfold bapprox. intros * -> Hpc Hwp.
    eapply HYP; eauto. apply Hwp.
  Qed.

  Lemma bapprox_produce {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_produce asn)
      (cmut_produce ι asn).
  Proof.
    induction asn; cbn - [subst].
    - apply bapprox_assume_formula.
    - apply bapprox_produce_chunk.
    - apply bapprox_demonic_match_bool; auto using smut_produce_dcl.
    - apply bapprox_demonic_match_enum; auto using smut_produce_dcl.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - apply bapprox_bind_right; auto using smut_produce_dcl.
    - admit.
    - now apply bapprox_debug, bapprox_pure.
  Admitted.

  Lemma bapprox_consume_chunk {Γ Σ} (ι : SymInstance Σ) (c : Chunk Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_consume_chunk c)
      (cmut_consume_chunk (inst c ι)).
  Proof.
    (* unfold bapprox. intros * Hι Hpc. *)
    (* unfold smut_consume_chunk, cmut_consume_chunk. *)
    (* unfold smut_get_heap, cmut_get_heap. *)
    (* unfold smut_put_heap, cmut_put_heap. *)
    (* rewrite smut_wp_bind, cmut_wp_bind; auto. *)
    (* rewrite smut_wp_state, cmut_wp_state. *)
    (* rewrite smut_wp_bind; auto. *)
    (* rewrite smut_wp_angelic_list. intros [[Δpc h'] [HIn Hwp]]. *)
    (* rewrite subst_sub_id in HIn. *)
    (* cbn in Hwp. rewrite smut_wp_bind_right in Hwp; auto. *)
    (* rewrite smut_wp_assert_formulas in Hwp; auto. *)
    (* rewrite ?inst_lift in Hwp. destruct Hwp as [HΔpc Hwp]. *)
    (* rewrite smut_wp_state in Hwp; auto. cbn in Hwp, HIn. *)
    (* rewrite ?inst_subst, ?inst_lift in Hwp. cbn. *)
    (* rewrite cmut_wp_angelick_list. *)
    (* exists (inst h' ι). *)
    (* split. *)
    (* - apply base.elem_of_list_In in HIn. *)
    (*   unfold extract_chunk_eqb, extract_scchunk_eqb in *. *)
    (*   unfold base.omap in HIn. *)
    (*   apply list.elem_of_list_omap in HIn. *)
    (*   destruct HIn as [[c' h''] [HIn Heq]]. *)
    (*   apply List.in_map_iff. *)
    (*   destruct (match_chunk_eqb_spec c c' nil); cbn in Heq; try discriminate. *)
    (*   inversion Heq. subst h'' a. clear Heq. *)
    (*   specialize (H ι). inster H by (subst; auto). destruct H as [H _]. *)
    (*   exists (inst c' ι, inst (T := List Chunk) h' ι). cbn. *)
    (*   apply base.elem_of_list_In in HIn. *)
    (*   split; auto. apply List.filter_In. *)
    (*   split. *)
    (*   + unfold lift, inst in HIn. cbn in HIn. *)
    (*     rewrite List.map_map in HIn. *)
    (*     rewrite heap_extractions_map in HIn. *)
    (*     rewrite List.in_map_iff in HIn. *)
    (*     destruct HIn as [[c1 h1'] [Heq HIn]]. *)
    (*     unfold base.prod_map in Heq; cbn in Heq. *)
    (*     rewrite <- List.map_map in Heq. *)
    (*     change (lift (inst c1 ι1) :: lift (inst h1' ι1) = c' :: h') in Heq. *)
    (*     inversion Heq. subst. clear Heq. *)
    (*     rewrite ?inst_lift in *. *)
    (*     unfold inst at 3. cbn. *)
    (*     rewrite heap_extractions_map. *)
    (*     rewrite List.in_map_iff. *)
    (*     exists (c1, h1'). split; auto. *)
    (*   + destruct (match_scchunk_eqb_spec (inst c ι) (inst c' ι)); auto. *)
    (* - cbn; now subst. *)
    (* - apply smut_state_dcl. intros * ->. cbn. *)
    (*   rewrite ?inst_subst, ?inst_lift. congruence. *)
    (* - admit. *)
    (* - admit. *)
  Admitted.

  Lemma bapprox_consume {Γ Σ} (ι : SymInstance Σ) (asn : Assertion Σ) :
    bapprox
      (Γ1 := Γ) (Γ2 := Γ) ι
      (smut_consume asn)
      (cmut_consume ι asn).
  Proof.
    induction asn; cbn - [subst].
    - apply bapprox_assert_formula.
    - apply bapprox_consume_chunk.
    - apply bapprox_angelic_match_bool; auto using smut_consume_dcl.
    - apply bapprox_angelic_match_enum; auto using smut_consume_dcl.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - apply bapprox_bind_right; auto using smut_consume_dcl.
    - admit.
    - now apply bapprox_debug, bapprox_pure.
  Admitted.

  Lemma bapprox_call {Γ Δ τ Σ} (c : SepContract Δ τ) (ts : NamedEnv (Term Σ) Δ) (ι : SymInstance Σ) :
    bapprox ι (@smut_call Γ Δ τ Σ c ts) (cmut_call c (inst ts ι)).
  Proof.
    (* destruct c as [Σ__c δ pre result post]; cbn [smut_call cmut_call]. *)
    (* apply bapprox_angelicvs. admit. *)
    (* intros ιc. change (SymInstance Σ__c) in ιc. *)
    (* unfold bapprox. intros * Hι Hpc. *)
    (* destruct (catView ζ01) as [ζ01 ζc]. *)
    (* change (Sub Σ Σ1) in ζ01. *)
    (* change (Sub Σ__c Σ1) in ζc. *)
    (* rewrite smut_wp_assert_formulask; auto. *)
    (* rewrite cmut_wp_assert_formulask. *)
    (* rewrite ?inst_formula_eqs. *)
    (* rewrite ?inst_subst, ?inst_lift. *)
    (* intros [Hfmls Hwp]. split. *)
    (* - admit. *)
    (* - rewrite smut_wp_sub in Hwp. revert Hwp. *)
    (*   rewrite sub_comp_cat_right. *)
    (*   eapply bapprox_bind_right; eauto. admit. *)
    (*   admit. *)
    (*   eapply bapprox_demonicv. admit. *)
    (*   intros v. *)
    (*   apply bapprox_bind_right; auto. admit. *)
    (*   admit. *)
    (*   admit. *)
    (* - admit. *)
  Admitted.

  Lemma bapprox_eval_exp {Γ Σ τ} (e : Exp Γ τ) (ι : SymInstance Σ) :
    bapprox ι (smut_eval_exp e) (cmut_eval_exp e).
  Proof.
    unfold smut_eval_exp, cmut_eval_exp.
    apply bapprox_state. intros. cbn. f_equal.
    now rewrite eval_exp_inst.
  Qed.

  Lemma bapprox_pushpop {AT A} `{InstLaws AT A} {Γ1 Γ2 x σ Σ} (ι : SymInstance Σ) (a : Term Σ σ)
    (dm : SMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) AT Σ) (dm_dcl : smut_dcl dm)
    (sm : CMut (Γ1 ▻ (x :: σ)) (Γ2 ▻ (x :: σ)) A) :
    bapprox ι dm sm ->
    bapprox ι (smut_pushpop a dm) (cmut_pushpop (inst a ι) sm).
  Proof.
    intros Hap. unfold smut_pushpop, cmut_pushpop.
    apply bapprox_bind_right; auto.
    apply smut_bind_left_dcl; auto.
    apply smut_pop_local_dcl.
    unfold smut_push_local, cmut_push_local.
    apply bapprox_state. intros. cbn.
    f_equal. f_equal. subst. now rewrite <- inst_subst.
    apply bapprox_bind_left; eauto.
    apply smut_pop_local_dcl.
    unfold smut_pop_local, cmut_pop_local.
    apply bapprox_state. intros. cbn.
    f_equal. subst. now destruct (snocView δ1).
  Qed.

  Lemma bapprox_pushspops {AT A} `{InstLaws AT A} {Γ1 Γ2 Δ Σ} (ι : SymInstance Σ)
    (dm : SMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) AT Σ) (dm_dcl : smut_dcl dm)
    (sm : CMut (Γ1 ▻▻ Δ) (Γ2 ▻▻ Δ) A) (Hap : bapprox ι dm sm) :
    forall (δ__sym : SStore Δ Σ) (δ__sc : LocalStore Δ),
      δ__sc = inst δ__sym ι ->
      bapprox ι (smut_pushspops δ__sym dm) (cmut_pushspops δ__sc sm).
  Proof. Admitted.

  Lemma bapprox_exec {Γ σ} (s : Stm Γ σ) :
    forall Σ (ι : SymInstance Σ),
      bapprox ι (smut_exec s) (cmut_exec s).
  Proof.
    induction s; cbn [smut_exec cmut_exec]; intros Σ ι.
    - unfold bapprox. cbn. auto.
    - now apply bapprox_eval_exp.
    - apply bapprox_bind; auto. admit.
      intros a. apply bapprox_pushpop; auto.
      apply smut_exec_dcl; auto.
    - apply bapprox_pushspops;
        rewrite ?inst_lift;
        auto using smut_exec_dcl.
    - apply bapprox_bind; auto. admit.
      intros a.
      apply bapprox_bind_right; auto.
      apply smut_pure_dcl.
      apply bapprox_state.
      intros * ->; cbn.
      f_equal. rewrite <- inst_subst.
      unfold inst at 1; cbn.
      now rewrite env_map_update.
      now apply bapprox_pure.
    - destruct (CEnv f).
      + apply bapprox_bind; auto. admit. admit.
        intros ?. apply bapprox_call.
      + admit.
    - apply bapprox_bind. admit.
      { apply bapprox_state. cbn; auto. }
      intros δ0. apply bapprox_bind_right.
      apply smut_bind_left_dcl. apply smut_exec_dcl.
      apply smut_put_local_dcl.
      { apply bapprox_state. cbn; intros.
        now rewrite inst_subst, inst_lift. }
      admit.
    - apply bapprox_bind. admit. admit. intros args.
      apply bapprox_call.
    - admit.
    - apply bapprox_bind_right; auto. apply smut_exec_dcl.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      intros t. admit.
    - apply bapprox_block.
    - admit.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      admit.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      intros t. admit.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      intros t. admit.
    - admit.
    - admit.
    - admit.
    - apply bapprox_angelic; auto. admit.
      intros v.
      apply bapprox_bind_right. admit.
      apply bapprox_consume_chunk.
      apply bapprox_bind_right. apply smut_pure_dcl.
      apply bapprox_produce_chunk.
      now apply bapprox_pure.
    - apply bapprox_bind. admit.
      apply bapprox_eval_exp.
      intros tnew.
      apply bapprox_angelic. admit.
      intros vold. apply bapprox_bind_right. admit.
      apply bapprox_consume_chunk. rewrite subst_sub_id.
      apply bapprox_bind_right. apply smut_pure_dcl.
      apply (bapprox_produce_chunk (chunk_ptsreg reg tnew)).
      now apply bapprox_pure.
    - admit.
    - admit.
  Admitted.

  Lemma bapprox_contract {Γ τ} (c : SepContract Γ τ) (s : Stm Γ τ) (ι : SymInstance (sep_contract_logic_variables c)) :
    bapprox ι (@smut_contract Γ τ c s) (@cmut_contract Γ τ c s ι).
  Proof.
    unfold smut_contract, cmut_contract; destruct c as [Σ δ pre result post]; cbn in *.
    apply bapprox_bind_right. admit.
    apply bapprox_produce.
    apply bapprox_bind. admit.
    apply bapprox_exec.
    intros res.
    apply bapprox_bind_right.
    apply smut_block_dcl.
    eapply bapprox_sub; eauto.
    rewrite inst_sub_snoc, inst_sub_id.
    apply bapprox_consume.
    apply bapprox_block.
  Admitted.

  Lemma symbolic_sound {Γ τ} (c : SepContract Γ τ) (body : Stm Γ τ) :
    ValidContractNoEvar c body ->
    ValidContractCMut c body.
  Proof.
    unfold ValidContractNoEvar, ValidContractCMut. intros [Hwp].
    intros ι. cbn. cbn in Hwp.
    unfold smut_contract_outcome in Hwp.
    (* specialize (Hwp ι). *)
    (* pose proof (bapprox_contract c body) as H. *)
    (* specialize (H ι _ (sub_id _) nil ι (fun _ _ _ => True)). *)
    (* specialize (H (sep_contract_localstore c) nil). *)
    (* rewrite inst_sub_id in H. inster H by constructor. *)
    (* apply H. clear H. *)
  Admitted.

  (* Print Assumptions smut_wp_assume_formula. *)
  (* Print Assumptions smut_wp_bind. *)
  (* Print Assumptions smut_wp_bind_right. *)
  (* Print Assumptions smut_wp_equiv. *)
  (* Print Assumptions smut_wp_fmap. *)
  (* Print Assumptions smut_wp_fresh. *)
  (* Print Assumptions smut_wp_match_pair. *)
  (* Print Assumptions smut_wp_match_sum. *)
  (* Print Assumptions smut_wp_pair. *)
  (* Print Assumptions smut_wp_pure. *)
  (* Print Assumptions smut_wp_sub. *)

  (* Print Assumptions smut_pure_dcl. *)
  (* Print Assumptions smut_fresh_dcl. *)
  (* Print Assumptions smut_arrow_dcl_specialize. *)
  (* Print Assumptions smut_arrow_dcl_specialize. *)
  (* Print Assumptions smut_bind_dcl. *)
  (* Print Assumptions smut_bind_right_dcl. *)

  (* Print Assumptions symbolic_sound. *)

End Soundness.
