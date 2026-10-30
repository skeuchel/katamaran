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

From Equations Require Import
     Equations Signature.
Require Import Equations.Prop.EqDec.

From stdpp Require finite gmap list.

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     base_logic.lib.fancy_updates
     base_logic.lib.gen_heap
     base_logic.lib.own
     bi.big_op
     bi.interface
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.proofmode.

From Katamaran Require Import
     Iris.Base
     Iris.Instance
     Prelude
     Semantics
     Sep.Logic
     Signature
     SmallStep.Step
     Staging.NewShallow.Executor.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

(* The following three modules define the Iris instance of the program logic
   depending solely on the operational semantics (through IrisBase) and the
   user-defined predicates (in IrisPredicates), but without depending on a
   Specification module. The program logic rules of this subset are implemented
   in IrisSignatureRules, which is combined with IrisPredicates to form
   IrisInstance.

   This split allows us to use multiple different specifications with the same
   Iris model, so that the resulting triples can be combined. This is important
   particularly when combining specifications of universal contracts for unknown
   code with known code verifications, e.g. as in the RiscvPmp.BlockVerification
   proofs. *)
Module Type IrisPredicates
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import IB     : IrisBase GLOBAL PROG SEM).
  Parameter luser_inst : forall `{sRG : sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)), iProp Σ.
  Parameter lduplicate_inst : forall `{sRG : sailRegGS Σ} `{invGS Σ} (mG : memGS Σ) (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true -> bi_entails (luser_inst (sRG := sRG) mG ts) (luser_inst (sRG := sRG) mG ts ∗ luser_inst (sRG := sRG) mG ts).

End IrisPredicates.

Module Type IrisSignatureRules
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import IB     : IrisBase GLOBAL PROG SEM)
  (Import IPred  : IrisPredicates GLOBAL SIG PROG SEM IB).
Section Soundness.

  Import SmallStepNotations.

  Context `{sG : sailGS Σ}.

  #[export] Instance PredicateDefIProp : PredicateDef (iProp Σ) :=
    {| lptsreg σ r v        := reg_pointsTo r v;
       luser p ts           := luser_inst sailGS_memGS ts;
       lduplicate p ts Hdup := lduplicate_inst (sRG := sailGS_sailRegGS) sailGS_memGS ts Hdup
    |}.

  Definition semTriple {Γ τ} (δ : CStore Γ)
             (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
    PRE -∗ semWP s POST δ.
  (* always modality needed? perhaps not because sail not higher-order? *)
  Global Arguments semTriple {Γ} {τ} δ PRE%_I s%_exp POST%_I.

  Definition ValidLemma {Δ} (lem : Lemma Δ) : Prop :=
    match lem with
      {| lemma_logic_variables := Σ;
         lemma_patterns        := θΔ;
         lemma_precondition    := req;
         lemma_postcondition   := ens;
      |} =>
      forall (ι : Valuation Σ),
        ⊢ asn.interpret req ι -∗
          asn.interpret ens ι
    end.

  Lemma iris_rule_consequence {Γ σ} {δ : CStore Γ}
        {P P'} {Q Q' : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
        semTriple δ P' s Q' -∗ semTriple δ P s Q.
  Proof.
    iIntros (PP QQ) "trips P".
    iApply (wp_mono _ _ _ (fun v => match v with MkValConf _ v δ' => Q' v δ' end)).
    + intros [v δ']; cbn.
      apply QQ.
    + iApply "trips".
      iApply PP; iFrame.
  Qed.

  Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
        (R P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
        (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
  Proof.
    iIntros "trips [HR HP]".
    iApply (wp_frame_l _ _ (MkConf s δ) (fun v => match v with MkValConf _ v δ' => Q v δ' end) R).
    iFrame.
    by iApply "trips".
  Qed.

  Lemma iris_rule_pull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
        (P : iProp Σ) (Q : Prop) (R : Val σ -> CStore Γ -> iProp Σ) :
        (⊢ (⌜ Q ⌝ → semTriple δ P s R) -∗ semTriple δ (P ∧ bi_pure Q) s R).
  Proof.
    iIntros "QP [P %]".
    by iApply "QP".
  Qed.

  Lemma iris_rule_exist {σ Γ} (δ : CStore Γ)
        (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
        {Q :  Val σ -> CStore Γ -> iProp Σ} :
        ⊢ ((∀ x, semTriple δ (P x) s Q) -∗ semTriple δ (∃ x, P x) s Q).
  Proof.
    iIntros "trips Px".
    iDestruct "Px" as (x) "Px".
    by iApply "trips".
  Qed.

  Lemma iris_rule_stm_val {Γ} (δ : CStore Γ)
        {τ : Ty} {v : Val τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q v δ)%I -∗ semTriple δ P (stm_val τ v) Q).
  Proof.
    iIntros "PQ P".
    iApply semWP_val.
    by iApply "PQ".
  Qed.

  Lemma iris_rule_stm_exp {Γ} (δ : CStore Γ)
        {τ : Ty} {e : Exp Γ τ}
        {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
        ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTriple δ P (stm_exp e) Q).
  Proof.
    iIntros "PQ P".
    iApply semWP_exp.
    now iApply "PQ".
  Qed.

  Lemma iris_rule_stm_let {Γ} (δ : CStore Γ)
        (x : PVar) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
                     (∀ (v : Val σ) (δ' : CStore Γ),
                         semTriple (env.snoc δ' (x∷σ) v) (Q v δ') k (fun v δ'' => R v (env.tail δ'')) ) -∗
                     semTriple δ P (let: x := s in k) R).
  Proof.
    iIntros "trips tripk P".
    iApply semWP_let.
    iSpecialize ("trips" with "P").
    by iApply (semWP_mono with "trips").
  Qed.

  Lemma iris_rule_stm_block {Γ} (δ : CStore Γ)
        (Δ : PCtx) (δΔ : CStore Δ)
        (τ : Ty) (k : Stm (Γ ▻▻ Δ) τ)
        (P : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple (δ ►► δΔ) P k (fun v δ'' => R v (env.drop Δ δ'')) -∗
                   semTriple δ P (stm_block δΔ k) R).
  Proof.
    iIntros "tripk P". iPoseProof ("tripk" with "P") as "wpk".
    by iApply semWP_block.
  Qed.

  Lemma iris_rule_stm_seq {Γ} (δ : CStore Γ)
        (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
        (P : iProp Σ) (Q : CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P s1 (fun _ => Q) -∗
                 (∀ δ', semTriple δ' (Q δ') s2 R) -∗
                 semTriple δ P (s1 ;; s2) R).
  Proof.
    iIntros "trips1 trips2 P".
    iSpecialize ("trips1" with "P").
    iApply semWP_seq.
    iApply (semWP_mono with "trips1").
    by iFrame.
  Qed.

  Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
        (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                      (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (⌜ eval e1 δ = true ⌝ → semTriple δ P k Q) -∗
      semTriple δ P (stm_assertk e1 e2 k) Q.
  Proof.
    iIntros "tripk P".
    iApply semWP_assertk.
    iIntros (->).
    by iApply "tripk".
  Qed.

  Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
        (τ : Ty) (s : Val ty.string) :
        forall (Q : Val τ -> CStore Γ -> iProp Σ),
          ⊢ semTriple δ True (stm_fail τ s) Q.
  Proof.
    iIntros (Q) "_".
    by iApply semWP_fail.
  Qed.

  Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
        ⊢ (semTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => ⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝ ∧ lptsreg r v)).
  Proof.
    iIntros "Hreg".
    iApply semWP_read_register.
    iExists v.
    iFrame.
    iIntros "Hreg".
    repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_write_register {Γ} (δ : CStore Γ)
        {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                              (Q : Val σ -> CStore Γ -> iProp Σ)
                              (v : Val σ) :
        ⊢ semTriple δ (lptsreg r v) (stm_write_register r w)
                  (fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v').
  Proof.
    iIntros "Hreg".
    iApply semWP_write_register.
    iExists v.
    iFrame.
    iIntros "Hreg".
    repeat iSplit; auto.
  Qed.

  Lemma iris_rule_stm_assign {Γ} (δ : CStore Γ)
        (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
        (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
           semTriple δ P (stm_assign x s) R).
  Proof.
    iIntros "trips P".
    iPoseProof ("trips" with "P") as "wpv".
    by iApply semWP_assign.
  Qed.

  Lemma iris_rule_stm_bind {Γ} (δ : CStore Γ)
        {σ τ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
        (R : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s Q -∗
           (∀ (v__σ : Val σ) (δ' : CStore Γ),
               semTriple δ' (Q v__σ δ') (k v__σ) R) -∗
           semTriple δ P (stm_bind s k) R).
  Proof.
    iIntros "trips tripk P".
    iSpecialize ("trips" with "P").
    iApply semWP_bind.
    by iApply (semWP_mono with "trips").
  Qed.

  Lemma iris_rule_stm_call_inline_later
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ ▷ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "tripbody P".
    iApply semWP_call_inline_later.
    iModIntro.
    by iApply "tripbody".
  Qed.

  Lemma iris_rule_stm_call_inline
    {Γ} (δΓ : CStore Γ)
    {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
    (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
    ⊢ semTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
      semTriple δΓ P (stm_call f es) Q.
  Proof.
    iIntros "Hdef".
    iApply (iris_rule_stm_call_inline_later with "Hdef").
  Qed.

  Lemma iris_rule_stm_debugk
    {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
    (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
    ⊢ (semTriple δ P k Q -∗
       semTriple δ P (stm_debugk k) Q).
  Proof. iIntros "tripk P". iApply semWP_debugk. now iApply "tripk". Qed.

  Lemma iris_rule_noop {Γ σ} {δ : CStore Γ}
        {P} {Q : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
    stm_to_val s = None ->
    (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ ->
                            (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\
                            ((exists v, s' = stm_val _ v) \/ (exists msg, s' = stm_fail _ msg))) ->
    (∀ v, P ={⊤}=∗ Q v δ) -∗
                 semTriple δ P s Q.
  Proof.
    iIntros (Hnv Hnoop) "HPQ HP". rewrite <-semWP_unfold_nolc. rewrite Hnv.
    iIntros (γ1 μ1) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2) "%".
    destruct (Hnoop _ _ _ _ _ _ H) as (-> & -> & -> & [[v ->]|[msg ->]]).
    - do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame. iApply semWP_val. now iApply "HPQ".
    - do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
      iFrame. now iApply semWP_fail.
  Qed.

  Definition ValidContractSemCurried {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      Sep.Logic.Forall (fun (ι : Valuation ctxΣ) =>
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
                  (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v)))
    end.

  Definition ValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
    match contract with
    | MkSepContract _ _ ctxΣ θΔ pre result post =>
      ∀ (ι : Valuation ctxΣ),
        semTriple (inst θΔ ι) (asn.interpret pre ι) body
                  (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v))
    end.

  Definition ValidContractForeign {Δ τ} (contract : SepContract Δ τ) (f : 𝑭𝑿 Δ τ) : Prop :=
    forall Γ (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ),
      match contract with
      | MkSepContract _ _ Σ' θΔ req result ens =>
        forall (ι : Valuation Σ'),
        evals es δ = inst θΔ ι ->
        ⊢ semTriple δ (asn.interpret req ι) (stm_foreign f es)
          (fun v δ' => asn.interpret ens (env.snoc ι (result∷τ) v) ∗ bi_pure (δ' = δ))
      end.

  Definition valid_contract_curry {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) :
    ValidContractSem body contract ⊣⊢ ValidContractSemCurried body contract.
  Proof.
    destruct contract as [lvars δ req res ens]; cbn.
    now rewrite Forall_forall.
  Qed.

End Soundness.
End IrisSignatureRules.

Module Type IrisAdequacy
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import IB     : IrisBase GLOBAL PROG SEM)
  (Import IAP    : IrisAdeqParameters GLOBAL IB)
  (Import IPred  : IrisPredicates GLOBAL SIG PROG SEM IB)
  (Import ISR    : IrisSignatureRules GLOBAL SIG PROG SEM IB IPred).


  Import SmallStepNotations.

  Definition RegStore_to_map (γ : RegStore) : gmap SomeReg (exclR (leibnizO SomeVal)) :=
    list_to_map (K := SomeReg)
                (fmap (fun x => match x with
                              existT _ r =>
                                pair (existT _ r) (Excl (existT _ (read_register γ r)))
                            end)
                     (finite.enum (sigT 𝑹𝑬𝑮))).

  Lemma RegStore_to_map_Forall (γ : RegStore) :
    map_Forall (K := SomeReg)
      (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register γ reg)) = v end)
      (RegStore_to_map γ).
  Proof.
    eapply map_Forall_lookup_2.
    intros [σ r] x eq.
    unfold RegStore_to_map in eq.
    remember (list_to_map _ !! _) as o in eq.
    destruct o; inversion eq; subst.
    assert (eq' := eq_sym Heqo).
    rewrite <-elem_of_list_to_map in eq'.
    - eapply list_elem_of_fmap_1 in eq'.
      destruct eq' as ([σ' r'] & eq2 & eq3).
      now inversion eq2.
    - rewrite <-list_fmap_compose.
      rewrite (list_fmap_ext _ id).
      + rewrite list_fmap_id.
        eapply finite.NoDup_enum.
      + now intros i [σ' r'].
  Qed.

  Lemma RegStore_to_map_valid (γ : RegStore) :
    valid (RegStore_to_map γ).
  Proof.
    intros i.
    cut (exists v, RegStore_to_map γ !! i = Some (Excl v)).
    - intros [v eq].
      now rewrite eq.
    - destruct i as [σ r].
      exists (existT _ (read_register γ r)).
      eapply elem_of_list_to_map_1'.
      + intros y eq.
        eapply list_elem_of_fmap_1 in eq.
        destruct eq as ([σ2 r2] & eq1 & eq2).
        now inversion eq1.
      + refine (list_elem_of_fmap_2 _ _ (existT _ r) _).
        eapply finite.elem_of_enum.
  Qed.

  Lemma steps_to_erased {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}:
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    rtc erased_step ([MkConf s δ]%list, (γ,μ)) ([MkConf s' δ']%list, (γ',μ')).
  Proof.
    induction 1; first done.
    refine (rtc_l _ _ _ _ _ IHSteps).
    exists nil.
    refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
    by eapply mk_prim_step.
  Qed.

  Lemma steps_to_nsteps {σ Γ γ μ δ} (s : Stm Γ σ) {γ' μ' δ' s'}:
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    exists n, language.nsteps n ([MkConf s δ]%list , (γ,μ)) [] ([MkConf s' δ']%list , (γ',μ')).
  Proof.
    induction 1.
    - exists 0. now constructor.
    - destruct IHSteps as [n steps].
      exists (S n).
      refine (language.nsteps_l _ _ _ _ [] _ _ steps).
      refine (step_atomic _ _ _ _ _ nil nil eq_refl eq_refl _).
      now eapply mk_prim_step.
  Qed.

  Lemma own_RegStore_to_map_reg_pointsTos `{sailRegGS Σ'} {γ : RegStore} {l : list (sigT 𝑹𝑬𝑮)} :
    NoDup l ->
    ⊢ own reg_gv_name (◯ list_to_map (K := SomeReg)
                         (fmap (fun x => match x with existT _ r =>
                                                     pair (existT _ r) (Excl (existT _ (read_register γ r)))
                                      end) l)) -∗
      [∗ list] x ∈ l,
        let (x0, r) := (x : sigT 𝑹𝑬𝑮) in reg_pointsTo r (read_register γ r).
  Proof.
    iIntros (nodups) "Hregs".
    iInduction l as [|[x r]] "IH".
    - now iFrame.
    - rewrite big_sepL_cons. cbn.
      rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ r)))).
      rewrite auth_frag_op.
      iPoseProof (own_op with "Hregs") as "[Hreg Hregs]".
      iFrame.
      iApply "IH".
      + iPureIntro.
        refine (NoDup_cons_1_2 (existT x r) l nodups).
      + iFrame.
      + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
        refine (not_elem_of_list_to_map_1 _ (existT x r) _).
        rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext _ id).
        now rewrite list_fmap_id.
        now intros i [σ2 r2].
  Qed.

  Definition own_regstore `{sailGS Σ} (γ : RegStore) : iProp Σ :=
    [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮),
      match x with | existT _ r => reg_pointsTo r (read_register γ r) end.


  Definition sailΣ : gFunctors := #[ memΣ ; invΣ ; GFunctor regUR].

  Class sailGpreS Σ := SailGpreS { (* resources for the implementation side *)
                       sailGpresS_invGpreS : invGpreS Σ; (* for fancy updates, invariants... *)

                       (* ghost variable for tracking state of registers *)
                       reg_pre_inG : inG Σ regUR;

                       (* ghost variable for tracking state of memory cells *)
                       sailPreG_gen_memGpreS : memGpreS Σ
                     }.
  #[export] Existing Instance sailGpresS_invGpreS.
  #[export] Existing Instance reg_pre_inG.


  #[export] Instance subG_sailGpreS {Σ} : subG sailΣ Σ -> sailGpreS Σ.
  Proof.
    intros.
    lazymatch goal with
    | H:subG ?xΣ _ |- _ => try unfold xΣ in H
    end.
    repeat match goal with
           | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
           end.
    split; eauto using memΣ_GpreS, subG_invΣ.
    solve_inG.
  Qed.

  Lemma adequacy {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'}
        {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : Val σ -> Prop} :
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
    (forall `{sailGS Σ'},
        ⊢ semTriple (Σ := Σ') δ
          (mem_res μ ∗ own_regstore γ) s
          (fun v δ' => bi_pure (Q v))) ->
    ResultOrFail s' Q.
  Proof.
    intros steps fins trips.
    cut (adequate MaybeStuck (MkConf s δ) (γ,μ)
             (λ (v : val (microsail_lang Γ σ)) (_ : state (microsail_lang Γ σ)),
                (λ v0 : val (microsail_lang Γ σ), match v0 with
                                                  | MkValConf _ v' _ => Q v'
                                                  end) v)).
    - destruct s'; cbn in fins; destruct fins; last done.
      intros adeq.
      apply (adequate_result MaybeStuck (MkConf s δ) (γ , μ) (fun v _ => match v with | MkValConf _ v' δ' => Q v' end) adeq nil (γ' , μ') (MkValConf _ v δ')).
      by apply steps_to_erased.
    - constructor; last done.
      intros t2 σ2 [v2 δ2] eval.
      assert (eq := RegStore_to_map_Forall γ).
      assert (regsmapv := RegStore_to_map_valid γ).
      pose proof (wp_adequacy sailΣ (microsail_lang Γ σ) MaybeStuck (MkConf s δ) (γ , μ) (fun v => match v with | MkValConf _ v' δ' => Q v' end)) as adeq.
      refine (adequate_result _ _ _ _ (adeq _) _ _ _ eval); clear adeq.
      iIntros (Hinv κs) "".
      iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]";
        first by apply auth_both_valid.
      pose proof (memΣ_GpreS (Σ := sailΣ) _) as mGS.
      iMod (mem_init (mGS := mGS)) as (memG) "[Hmem Rmem]".
      iModIntro.
      iExists (fun σ _ => regs_inv (srGS := (SailRegGS _ spec_name)) (σ.1) ∗ mem_state_interp (σ.2))%I.
      iExists _.
      iSplitR "Hs2 Rmem".
      * iFrame.
        iExists (RegStore_to_map γ).
        now iFrame.
      * iApply wp_mono.
        2: {
          iApply (trips _ (SailGS Hinv (SailRegGS reg_pre_inG spec_name) memG) with "[Rmem Hs2]").
          iFrame.
          iApply (own_RegStore_to_map_reg_pointsTos (H := SailRegGS reg_pre_inG spec_name)(γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2").
          eapply finite.NoDup_enum.
        }
        done.
  Qed.

  Lemma adequacy_gen {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'}
        {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : forall `{sailGS Σ}, Val σ -> CStore Γ -> iProp Σ} (φ : Prop):
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    (forall `{sailGS Σ'},
        mem_res μ ∗ own_regstore γ ⊢ |={⊤}=> semWP s Q δ
          ∗ (mem_state_interp μ' ={⊤,∅}=∗ ⌜φ⌝)
    )%I -> φ.
  Proof.
    (* intros steps trips. *)
    intros [n steps]%steps_to_nsteps trips.
    refine (wp_strong_adequacy sailΣ (microsail_lang Γ σ) _ _ _ _ _ _ _ _ (fun _ => 0) _ steps).
    iIntros (Hinv) "".
    assert (eq := RegStore_to_map_Forall γ).
    assert (regsmapv := RegStore_to_map_valid γ).
    iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]";
        first by apply auth_both_valid.
    pose proof (memΣ_GpreS (Σ := sailΣ) _) as mGS.
    iMod (mem_init (mGS := mGS)) as (memG) "[Hmem Rmem]".
    pose (regsG := {| reg_inG := @reg_pre_inG sailΣ (@subG_sailGpreS sailΣ (subG_refl sailΣ)); reg_gv_name := spec_name |}).
    pose (sailG := SailGS Hinv regsG memG).
    iMod (trips sailΣ sailG with "[Rmem Hs2]") as "[trips Hφ]".
    { iFrame.
      unfold own_regstore.
      iApply (own_RegStore_to_map_reg_pointsTos (H := regsG) (γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2").
      eapply finite.NoDup_enum.
    }
    iModIntro.
    iExists (fun σ _ _ _ => regs_inv (srGS := (SailRegGS _ spec_name)) (σ.1) ∗ mem_state_interp (σ.2))%I.
    iExists [ fun v => Q _ sailG (valconf_val v) (valconf_store v) ]%list.
    iExists _.
    iExists _.
    iSplitR "trips Hφ".
    * iFrame.
      iExists (RegStore_to_map γ).
      now iFrame.
    * cbn. iFrame.
      iIntros (es' t2') "_ _ _ [Hregsinv Hmeminv] _ _".
      now iApply "Hφ".
  Qed.

End IrisAdequacy.

Module Type IrisInstance (GLOBAL : GlobalState) (SIG : Signature GLOBAL) (PROG : Program GLOBAL)
  (SEM : Semantics GLOBAL PROG) (IB : IrisBase GLOBAL PROG SEM) (IAP : IrisAdeqParameters GLOBAL IB) :=
  IrisPredicates GLOBAL SIG PROG SEM IB <+ IrisSignatureRules GLOBAL SIG PROG SEM IB <+ IrisAdequacy GLOBAL SIG PROG SEM IB IAP.

(*
 * The following module defines the parts of the Iris model that must depend on the Specification, not just on the Signature.
 * This is kept to a minimum (see comment for the IrisPredicates module).
 *)
Module IrisInstanceWithContracts
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import SPEC   : Specification GLOBAL SIG PROG)
  (Import IB     : IrisBase GLOBAL PROG SEM)
  (Import IAP    : IrisAdeqParameters GLOBAL IB)
  (Import II     : IrisInstance GLOBAL SIG PROG SEM IB IAP)
  (Import NS     : NewShallowExecOn GLOBAL SIG PROG SPEC).

  Section WithSailGS.
  Context {Σ} {sG : sailGS Σ}.

  Definition ForeignSem : Prop :=
    ∀ (Γ : PCtx) (Δ : PCtx) (τ : Ty) (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
      (POST : Val τ → CStore Γ → iProp Σ) (δΓ : CStore Γ),
      CPureSpecM.call_contract (CEnvEx f) (evals es δΓ) (fun v => POST v δΓ) -∗
      semWP (stm_foreign f es) POST δΓ.

  Definition LemmaSem : Prop :=
    forall (Δ : PCtx) (l : 𝑳 Δ),
      ValidLemma (LEnv l).

  Definition semCall [Δ τ] (f : 𝑭 Δ τ) (args : CStore Δ) (Q : Val τ -> iProp Σ) :
    iProp Σ := ▷ CHeapSpecM.exec_call_inline semWP f args Q.

  Definition semWP' [Γ τ] (s : Stm Γ τ) :
    (Val τ -> CStore Γ -> iProp Σ) -> CStore Γ -> iProp Σ :=
    CHeapSpecM.exec_open semWP semCall s.
  Arguments semWP' : simpl never.

  Definition ref {Γ1 Γ2 A}
    (F G : (A → CStore Γ2 → iProp Σ) → CStore Γ1 → iProp Σ) : iProp Σ :=
    ∀ (POST : A → CStore Γ2 → iProp Σ) (δ : CStore Γ1),
      F POST δ -∗ G POST δ.
  Notation "F ≼ G" := (ref F G).

  Lemma rule_val {Γ τ} (v : Val τ) :
    ⊢ semWP' (Γ := Γ) (stm_val τ v) ≼ semWP (stm_val τ v).
  Proof. iIntros (POST δ). rewrite semWP_val; auto. Qed.

  Lemma rule_exp {Γ τ} (e : Exp Γ τ) :
    ⊢ semWP' (stm_exp e) ≼ semWP (stm_exp e).
  Proof. iIntros (POST δ) "P". now iApply semWP_exp. Qed.

  Lemma rule_fail {Γ τ s} :
    ⊢ semWP' (Γ := Γ) (stm_fail τ s) ≼ semWP (stm_fail τ s).
  Proof. iIntros (POST δ) "_". rewrite semWP_fail; auto. Qed.

  Lemma rule_bind {Γ τ σ} (s : Stm Γ σ) (k : Val σ → Stm Γ τ) :
    ⊢ semWP' (stm_bind s k) ≼ semWP (stm_bind s k).
  Proof.
    iIntros (Q). iRevert (s). iLöb as "IH". iIntros (s δ) "WPs".
    rewrite (semWP_unfold (stm_bind s k)). unfold semWP'. cbn.
    iIntros (γ1 μ1) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2) "(%step & Hcred)". destruct (smallinvstep step); cbn.
    - rewrite ?semWP_val. do 3 iModIntro. iMod "Hclose". iMod "WPs". by iFrame.
    - rewrite ?semWP_fail. by iFrame.
    - rewrite (semWP_unfold s). rewrite (stm_val_stuck H).
      iSpecialize ("WPs" $! γ1 μ1 with "state_inv").
      iMod "Hclose". iMod "WPs".
      iSpecialize ("WPs" $! _ _ _ _ with "[$Hcred]"); first easy.
      iMod "WPs". iModIntro. iModIntro. iModIntro.
      iMod "WPs". iMod "WPs" as "[state_inv wps]".
      iModIntro. iFrame "state_inv". by iApply "IH".
  Qed.

  Lemma rule_block {Γ τ Δ} (δΔ : CStore Δ) (s : Stm (Γ ▻▻ Δ) τ) :
    ⊢ semWP' (stm_block δΔ s) ≼ semWP (stm_block δΔ s).
  Proof.
    iIntros (Q). iRevert (δΔ s). iLöb as "IH". iIntros (δΔ k δΓ) "WPk".
    rewrite (semWP_unfold (stm_block δΔ k)). unfold semWP'. cbn.
    iIntros (γ1 μ1) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2) "(%step & Hcred)". destruct (smallinvstep step); cbn.
    - rewrite ?semWP_val. rewrite env.drop_cat. by iFrame.
    - rewrite ?semWP_fail. by iFrame.
    - rewrite (semWP_unfold k). rewrite (stm_val_stuck H).
      iSpecialize ("WPk" $! γ1 μ1 with "state_inv").
      iMod "Hclose". iMod "WPk".
      iSpecialize ("WPk" $! _ _ _ _ with "[$Hcred]"); first easy.
      iMod "WPk". iModIntro. iModIntro. iModIntro.
      iMod "WPk". iMod "WPk" as "[state_inv wps]".
      iModIntro. iFrame "state_inv". by iApply "IH".
  Qed.

  Lemma rule_let {Γ τ x σ} (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ) :
    ⊢ semWP' (stm_let x σ s k) ≼ semWP (stm_let x σ s k).
  Proof.
    iIntros (Q δΓ) "WPs". rewrite <-(semWP_unfold_nolc (stm_let x σ s k)). cbn.
    iIntros (γ1 μ1) "state_inv". unfold semWP'. cbn.
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
    iApply semWP_bind. iApply (semWP_mono with "WPs"). iIntros (v δ) "wpk".
    iApply (semWP_block [env].[_∷_ ↦ v]). iApply (semWP_mono with "wpk").
    clear. iIntros (? δ) "HQ". by destruct (env.view δ).
  Qed.

  Lemma rule_assign {Γ τ x} (xInΓ : x∷τ ∈ Γ) (s : Stm Γ τ) :
    ⊢ semWP' (stm_assign x s) ≼ semWP (stm_assign x s).
  Proof.
    iIntros (Q). iRevert (s). iLöb as "IH". iIntros (s δ) "WPs".
    rewrite (semWP_unfold (stm_assign x s)). unfold semWP'. cbn.
    iIntros (γ1 μ1) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2) "(%step & Hcred)". destruct (smallinvstep step); cbn.
    - rewrite ?semWP_val. by iFrame.
    - rewrite ?semWP_fail. by iFrame.
    - rewrite (semWP_unfold s). rewrite (stm_val_stuck H).
      iSpecialize ("WPs" $! γ1 μ1 with "state_inv").
      iMod "Hclose". iMod "WPs".
      iSpecialize ("WPs" $! _ _ _ _ with "[$Hcred]"); first easy.
      iMod "WPs". iModIntro. iModIntro. iModIntro.
      iMod "WPs". iMod "WPs" as "[state_inv wps]".
      iModIntro. iFrame "state_inv". by iApply "IH".
  Qed.

  Lemma rule_call_frame {Γ τ Δ} (δΔ : CStore Δ) (s : Stm Δ τ) :
    ⊢ semWP' (Γ := Γ) (stm_call_frame δΔ s) ≼ semWP (stm_call_frame δΔ s).
  Proof.
    iIntros (Q δΓ). iRevert (δΔ s). iLöb as "IH". iIntros (δΔ s) "WPs".
    rewrite (semWP_unfold (stm_call_frame δΔ s)). unfold semWP'. cbn.
    iIntros (γ1 μ1) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2) "(%step & Hcred)". destruct (smallinvstep step); cbn.
    - rewrite ?semWP_val. by iFrame.
    - rewrite ?semWP_fail. by iFrame.
    - rewrite (semWP_unfold s). rewrite (stm_val_stuck H).
      iSpecialize ("WPs" $! γ1 μ1 with "state_inv").
      iMod "Hclose". iMod "WPs".
      iSpecialize ("WPs" $! _ _ _ _ with "[$Hcred]"); first easy.
      iMod "WPs". iModIntro. iModIntro. iModIntro.
      iMod "WPs". iMod "WPs" as "[state_inv wps]".
      iModIntro. iFrame "state_inv". by iApply "IH".
  Qed.

  Lemma semWP_call {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
    ⊢ ∀ (Q : Val τ → CStore Γ → iProp Σ) (δΓ : CStore Γ),
        ▷ semWP (FunDef f) (fun vτ _ => Q vτ δΓ) (evals es δΓ) -∗
        semWP (stm_call f es) Q δΓ.
  Proof.
    iIntros (Q δΓ) "wpbody". rewrite <-(semWP_unfold_nolc (stm_call f es)). cbn.
    iIntros (γ1 μ1) "state_inv".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
    iModIntro. iModIntro. iModIntro. iMod "Hclose" as "_". iModIntro.
    iFrame "state_inv". by iApply semWP_call_frame.
  Qed.

  Lemma rule_call {Γ τ Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
    ⊢ semWP' (stm_call f es) ≼ semWP (stm_call f es).
  Proof. iIntros (Q δΓ) "wpbody". by iApply semWP_call. Qed.

  Lemma rule_foreign {Γ τ Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
    ForeignSem ->
    ⊢ semWP' (stm_foreign f es) ≼ semWP (stm_foreign f es).
  Proof. iIntros (extSem POST δΓ) "WPs". by iApply extSem. Qed.

(*   Lemma equiv_call_lemma {Δ} (lem : Lemma Δ) (args : CStore Δ) POST : *)
(*     CPureSpecM.call_lemma lem args POST ⊣⊢ CPureSpecM.call_lemma' lem args POST. *)
(*   Proof. apply CPureSpecM.equiv_call_lemma. Qed. *)
(* c *)

  Lemma rule_lemma {Γ τ Δ} (L : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (s : Stm Γ τ) :
    LemmaSem ->
    ⊢ semWP' (stm_lemmak L es s) ≼ semWP (stm_lemmak L es s).
  Proof.
    iIntros (lemSem POST δ) "WPs". specialize (lemSem _ L).
    iApply semWP_lemmak.
    unfold semWP'; cbn.
    rewrite CPureSpecM.equiv_call_lemma.
    destruct LEnv as [Σe δΔ req ens]. cbn in lemSem |- *.
    iDestruct "WPs" as "[% [% [req ens]]]".
    iApply "ens". by iApply lemSem.
  Qed.

  Lemma rule_seq {Γ τ σ} (s : Stm Γ σ) (k : Stm Γ τ) :
    ⊢ semWP' (stm_seq s k) ≼ semWP (stm_seq s k).
  Proof.
    iIntros (Q δ) "WPs". rewrite <-(semWP_unfold_nolc (stm_seq s k)). cbn.
    iIntros (γ1 μ1) "state_inv". unfold semWP'. cbn.
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
    by iApply semWP_bind.
  Qed.

  Lemma rule_assertk {Γ τ} (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ) :
    ⊢ semWP' (stm_assertk e1 e2 k) ≼ semWP (stm_assertk e1 e2 k).
  Proof.
    iIntros (Q δ) "WPs". rewrite <-(semWP_unfold_nolc (stm_assertk e1 e2 k)). cbn.
    iIntros (γ1 μ1) "state_inv". unfold semWP'. cbn.
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
    destruct eval; [by iApply "WPs"|by iApply semWP_fail].
  Qed.

  Lemma rule_read_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) :
    ⊢ semWP' (Γ := Γ) (stm_read_register reg) ≼ semWP (stm_read_register reg).
  Proof.
    iIntros (Q δ) "[% [Hreg HP]]". rewrite <-semWP_unfold_nolc. cbn.
    iIntros (γ1 μ1) "[Hregs Hmem]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
    iDestruct (@reg_valid with "Hregs Hreg") as %->.
    iSpecialize ("HP" with "Hreg"). iFrame "Hregs Hmem". by iApply semWP_val.
  Qed.

  Lemma rule_write_register {Γ τ} (reg : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) :
    ⊢ semWP' (stm_write_register reg e) ≼ semWP (stm_write_register reg e).
  Proof.
    iIntros (Q δ) "[% [Hreg HP]]". rewrite <-semWP_unfold_nolc. cbn.
    iIntros (γ1 μ1) "[Hregs Hmem]".
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver.
    iMod (reg_update γ1 reg v (eval e δ) with "Hregs Hreg") as "[Hregs Hreg]".
    iModIntro. iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro.
    iSpecialize ("HP" with "Hreg"). iFrame "Hregs Hmem". by iApply semWP_val.
  Qed.

  Lemma rule_debug {Γ τ} (s : Stm Γ τ) :
    ⊢ semWP' (stm_debugk s) ≼ semWP (stm_debugk s).
  Proof. iIntros (POST δ) "WPs". now iApply semWP_debugk. Qed.

  Lemma rule_pattern_match {Γ τ σ} (s : Stm Γ σ) (pat : Pattern σ)
    (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
    ⊢ semWP' (stm_pattern_match s pat rhs) ≼ semWP (stm_pattern_match s pat rhs).
  Proof.
    iIntros (Q δΓ) "WPs". rewrite <-(semWP_unfold_nolc (stm_pattern_match s pat rhs)). cbn.
    iIntros (γ1 μ1) "state_inv". unfold semWP'. cbn.
    iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
    iIntros (s2 δ2 γ2 μ2 step). destruct (smallinvstep step); cbn.
    do 3 iModIntro. iMod "Hclose" as "_". iModIntro. iFrame "state_inv".
    iApply semWP_bind. iApply (semWP_mono with "WPs"). iIntros (v δ) "WPrhs".
    destruct pattern_match_val as [pc δpc]. by iApply (semWP_block δpc).
  Qed.

  Lemma sound_stm_open (extSem : ForeignSem) (lemSem : LemmaSem) :
    forall {Γ τ} (s : Stm Γ τ),
      ⊢ semWP' s ≼ semWP s.
  Proof.
    unfold ref.
    intros Γ τ [].
    - iIntros (Q δΓ). rewrite semWP_val. auto.
    - apply rule_exp.
    - apply rule_let.
    - apply rule_block.
    - apply rule_assign.
    - apply rule_call; auto.
    - apply rule_call_frame.
    - apply rule_foreign; auto.
    - apply rule_lemma; auto.
    - apply rule_seq.
    - apply rule_assertk.
    - apply rule_fail.
    - apply rule_pattern_match.
    - apply rule_read_register.
    - apply rule_write_register.
    - apply rule_bind.
    - apply rule_debug.
  Qed.

  Lemma sound_stm (extSem : ForeignSem) (lemSem : LemmaSem) :
    forall {Γ τ} (s : Stm Γ τ) (Q : Val τ → CStore Γ → iProp Σ) (δ : CStore Γ),
      CHeapSpecM.exec_aux semCall s Q δ ⊢ semWP s Q δ.
  Proof.
    intros.
    apply (CHeapSpecM.fold_exec_aux (ex := semWP) (ec := semCall)).
    - intros Γ' τ' f δ'.
      admit.
    - clear - extSem lemSem.
      intros Γ τ s.
      intros P Q PQ δ. cbn.
      iIntros "WP". iApply sound_stm_open; auto.
      unfold semWP'.
      iStopProof.
      iApply CHeapSpecM.exec_open_monotonic; auto.
      admit.
      admit.
    - unfold pointwise_relation. easy.
  Admitted.

  Lemma sound :
    ForeignSem -> LemmaSem -> Shallow.ValidContractCEnv ->
    ⊢ Shallow.ValidContractEnvSem semWP.
  Proof.
    intros extSem lemSem vcenv.
    iLöb as "IH".
    iIntros (σs σ f).
    specialize (vcenv σs σ f).
    destruct (CEnv f) as [[Σe δΔ req res ens]|];[|trivial].
    iIntros (ι) "PRE".
    specialize (vcenv _ eq_refl).
    cbn in vcenv.
    rewrite env.Forall_forall in vcenv.
    specialize (vcenv ι).
    rewrite CPureSpecM.wp_produce in vcenv.
    cbn in vcenv.
    iPoseProof (vcenv with "PRE") as "vcenv". clear vcenv.
    iApply (sound_stm extSem lemSem).
    iRevert "vcenv".
    iApply CHeapSpecM.exec_aux_monotonic.
  Abort.

  End WithSailGS.

End IrisInstanceWithContracts.
