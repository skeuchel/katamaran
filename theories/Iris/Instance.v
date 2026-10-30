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
     Prelude
     Semantics
     Sep.Hoare
     Sep.Logic
     Signature
     SmallStep.Step.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

(* A trivial type class for case studies that don't need additional
 * ghost state constraints in resGS.
 *)
Class trivGS (Σ : gFunctors) : Set := MkTrivGS {}.
#[export] Instance  trivTrivGS {Σ} : trivGS Σ := MkTrivGS _.

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
  (Import IPre   : IrisPrelims GLOBAL PROG SEM)
  (Import IB     : IrisBase GLOBAL PROG SEM IPre).

  (* Additional ghost state assumptions necessary for instantiating predicates. *)
  Parameter Inline resGS : gFunctors -> Set.
  Existing Class resGS.

  Parameter luser_inst : forall `{sRG : sailRegGS Σ} `{invGS Σ} {mG : memGS Σ} {rG : resGS Σ} (p : 𝑯) (ts : Env Val (𝑯_Ty p)), iProp Σ.
  Parameter lduplicate_inst : forall `{sRG : sailRegGS Σ} `{invGS Σ} {mG : memGS Σ} {rG : resGS Σ} (p : 𝑯) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true ->
      luser_inst ts ⊢ luser_inst ts ∗ luser_inst ts.

End IrisPredicates.

Module Type IrisSignatureRules
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import PLOG   : ProgramLogic GLOBAL SIG PROG)
  (Import IPre   : IrisPrelims GLOBAL PROG SEM)
  (Import IB     : IrisBase GLOBAL PROG SEM IPre)
  (Import IPred  : IrisPredicates GLOBAL SIG PROG SEM IPre IB).
Section Soundness.

  Import SmallStepNotations.

  Context `{sG : sailGS Σ, rG : resGS Σ}.

  #[export] Instance PredicateDefIProp : PredicateDef (iProp Σ) :=
    {| lptsreg σ r v        := reg_pointsTo r v;
       luser p ts           := luser_inst ts;
       lduplicate p ts Hdup := lduplicate_inst ts Hdup
    |}.

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

  Section PartialTriple.

    Context {SPEC : Specification}.

    (* semTriple currently wraps the given POST, if we end up with fail, we get
        True, otherwise we do POST v δ. *)
    Definition semTriple {Γ τ} (δ : CStore Γ)
                (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
        PRE -∗ semWP δ s (λ v δ, match v with
                            | inl v => POST v δ
                            | inr m => if fail_rule_pre then True%I else False%I
                            end).
    (* always modality needed? perhaps not because sail not higher-order? *)
    Global Arguments semTriple {Γ} {τ} δ PRE%_I s%_exp POST%_I.

    Lemma semTriple_consequence {Γ τ} {δ : CStore Γ} {PRE1 PRE2 : iProp Σ}
                                 {s : Stm Γ τ} {POST1 POST2 : Val τ -> CStore Γ -> iProp Σ} :
      semTriple δ PRE1 s POST1 -∗
      (PRE2 -∗ PRE1) -∗
      (∀ v δ, POST1 v δ -∗ POST2 v δ) -∗
      semTriple δ PRE2 s POST2.
    Proof.
      iIntros "H HPRE HPOST HPRE2".
      iSpecialize ("HPRE" with "HPRE2").
      iSpecialize ("H" with "HPRE").
      iApply (semWP_mono with "H").
      destruct fail_rule_pre; now iIntros ([] ?).
    Qed.

    Lemma iris_rule_consequence {Γ σ} {δ : CStore Γ}
            {P P'} {Q Q' : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
            (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
            semTriple δ P' s Q' -∗ semTriple δ P s Q.
    Proof.
        iIntros (PP QQ) "trips P".
        iApply (semWP_mono with "[trips P]").
        + iApply "trips".
        now iApply PP.
        + iIntros ([v|m] δ') "Qp"; last auto.
        now iApply QQ.
    Qed.

    Lemma iris_rule_frame {Γ σ} {δ : CStore Γ}
            (R P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
            (⊢ semTriple δ P s Q -∗ semTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
    Proof.
        iIntros "trips [HR HP]".
        iSpecialize ("trips" with "HP"). iApply (semWP_mono with "trips").
        iIntros ([v|m] ?) "HQ"; auto. iFrame "HR HQ".
    Qed.

    Lemma iris_rule_pull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
            (P : iProp Σ) (Q : Prop) (R : Val σ -> CStore Γ -> iProp Σ) :
            (⊢ (⌜ Q ⌝ -∗ semTriple δ P s R) -∗ semTriple δ (P ∧ bi_pure Q) s R).
    Proof.
        iIntros "QP [P %]".
        by iApply "QP".
    Qed.

    Lemma iris_rule_exist {σ Γ} (δ : CStore Γ)
            (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
            {Q :  Val σ -> CStore Γ -> iProp Σ} :
            ⊢ ((∀ x, semTriple δ (P x) s Q) -∗ semTriple δ (∃ x, P x) s Q).
    Proof.
        iIntros "trips [%x Px]".
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
        iApply (semWP_mono with "trips"). iIntros ([v|m] ?) "H".
        - now iSpecialize ("tripk" with "H").
        - simpl. now iApply semWP_fail.
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
            (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTriple δ P s1 Q -∗
                    (∀ v δ', semTriple δ' (Q v δ') s2 R) -∗
                    semTriple δ P (s1 ;; s2) R).
    Proof.
        iIntros "trips1 trips2 P".
        iSpecialize ("trips1" with "P").
        iApply semWP_seq.
        iApply (semWP_mono with "[$]"). iIntros ([v|m] ?) "H"; auto.
        - by iApply ("trips2" with "H").
        - by rewrite semWP_fail.
    Qed.

    Lemma iris_rule_stm_assertk {Γ τ} (δ : CStore Γ)
            (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (⌜ eval e1 δ = true ⌝ -∗ semTriple δ P k Q) -∗
          (if fail_rule_pre then True else ⌜eval e1 δ ≠ false⌝) -∗
        semTriple δ P (stm_assertk e1 e2 k) Q.
    Proof.
        iIntros "tripk Hf P".
        iApply (semWP_assertk with "[tripk P] [Hf]").
        - iIntros (->).
          by iApply "tripk".
        - iIntros (?).
          rewrite semWP_fail.
          destruct fail_rule_pre; auto.
          now iDestruct "Hf" as "%Hf".
    Qed.

    Lemma iris_rule_stm_fail {Γ} (δ : CStore Γ)
            (τ : Ty) (s : Val ty.string) :
            forall (Q : Val τ -> CStore Γ -> iProp Σ),
            ⊢ semTriple δ (if fail_rule_pre then True else False) (stm_fail τ s) Q.
    Proof.
        iIntros (Q) "H".
        destruct fail_rule_pre; auto.
        now iApply semWP_fail.
    Qed.

    Lemma iris_rule_stm_read_register {Γ} (δ : CStore Γ)
            {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
            ⊢ (semTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => ⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝ ∧ lptsreg r v)).
    Proof.
        iIntros "Hreg".
        iApply semWP_read_register.
        iExists v.
        iFrame.
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
        repeat iSplit; auto.
    Qed.

    Lemma iris_rule_stm_assign {Γ} (δ : CStore Γ)
            (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
            (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
            ⊢ (semTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
            semTriple δ P (stm_assign x s) R).
    Proof.
        iIntros "trips P".
        iSpecialize ("trips" with "P").
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
        iApply semWP_bind. iApply (semWP_mono with "trips"). iIntros ([v|m] ?) "H".
        - simpl. by iApply "tripk".
        - simpl. by iApply semWP_fail.
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
        iIntros (Hnv Hnoop) "HPQ HP".
        rewrite <-semWP_unfold_nolc. rewrite Hnv.
        iIntros (γ1 μ1) "state_inv".
        iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
        iIntros (s2 δ2 γ2 μ2) "%".
        destruct (Hnoop _ _ _ _ _ _ H) as (-> & -> & -> & [[v ->]|[msg ->]]).
        - do 3 iModIntro. iMod "Hclose" as "_".
        iFrame. iApply semWP_val. now iApply "HPQ".
        - do 3 iModIntro. iMod "Hclose" as "_".
        iFrame. iApply semWP_fail.
    Abort.

    Lemma iris_rule_stm_pattern_match {Γ τ σ} (δΓ : CStore Γ)
        (s : Stm Γ σ) (pat : Pattern σ)
        (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ)
        (P : iProp Σ) (Q : Val σ → CStore Γ → iProp Σ) (R : Val τ → CStore Γ → iProp Σ) :
        ⊢ semTriple δΓ P s Q -∗
        (∀ pc δpc δΓ1,
            semTriple (δΓ1 ►► δpc) (Q (pattern_match_val_reverse pat pc δpc) δΓ1) (rhs pc)
            (λ vτ (δ' : CStore (Γ ▻▻ PatternCaseCtx pc)), R vτ (env.drop (PatternCaseCtx pc) δ'))) -∗
        semTriple δΓ P (stm_pattern_match s pat rhs) R.
    Proof.
        iIntros "WPs WPrhs P".
        iSpecialize ("WPs" with "P").
        iApply semWP_pattern_match.
        iApply (semWP_mono with "WPs").
        iIntros ([vσ|m] δΓ') "Q"; auto.
        destruct pattern_match_val as [pc δpc] eqn:Heq.
        iApply "WPrhs".
        change (pattern_match_val_reverse pat pc δpc) with
        (pattern_match_val_reverse' pat (existT pc δpc)).
        rewrite <- Heq.
        now rewrite pattern_match_val_inverse_left.
    Qed.

    Definition ValidContractSemCurried {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
        match contract with
        | MkSepContract _ _ ctxΣ θΔ pre result post =>
        Sep.Logic.Forall (fun (ι : Valuation ctxΣ) =>
            semTriple (inst θΔ ι) (asn.interpret pre ι) body
                    (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v)))
        end.

    (* Uses projections rather than a match, so that using it for a concrete
       contract does not unfold the contract. *)
    Definition ValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
        ∀ (ι : Valuation (sep_contract_logic_variables contract)),
            semTriple (inst (sep_contract_localstore contract) ι)
                    (asn.interpret (sep_contract_precondition contract) ι) body
                    (fun v δ' => asn.interpret (sep_contract_postcondition contract)
                                   (env.snoc ι (sep_contract_result contract∷σ) v)).

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
  End PartialTriple.

  Section TotalTriple.

    Context {SPEC : Specification}.

    (* semTriple currently wraps the given POST, if we end up with fail, we get
        True, otherwise we do POST v δ. *)
    Definition semTTriple {Γ τ} (δ : CStore Γ)
                (PRE : iProp Σ) (s : Stm Γ τ) (POST : Val τ -> CStore Γ -> iProp Σ) : iProp Σ :=
        PRE -∗ semTWP δ s (λ v δ, match v with
                            | inl v => POST v δ
                            | inr m => if fail_rule_pre then True%I else False%I
                            end).
    (* always modality needed? perhaps not because sail not higher-order? *)
    Global Arguments semTTriple {Γ} {τ} δ PRE%_I s%_exp POST%_I.

    Lemma semTTriple_semTriple {Γ τ} {δ : CStore Γ} {PRE : iProp Σ}
                               {s : Stm Γ τ} {POST : Val τ -> CStore Γ -> iProp Σ} :
      semTTriple δ PRE s POST ⊢ semTriple δ PRE s POST.
    Proof.
      iIntros "Ht PRE". iSpecialize ("Ht" with "PRE"). by iApply semTWP_semWP.
    Qed.

    Lemma semTTriple_consequence {Γ τ} {δ : CStore Γ} {PRE1 PRE2 : iProp Σ}
                                 {s : Stm Γ τ} {POST1 POST2 : Val τ -> CStore Γ -> iProp Σ} :
      semTTriple δ PRE1 s POST1 -∗
      (PRE2 -∗ PRE1) -∗
      (∀ v δ, POST1 v δ -∗ POST2 v δ) -∗
      semTTriple δ PRE2 s POST2.
    Proof.
      iIntros "H HPRE HPOST HPRE2".
      iSpecialize ("HPRE" with "HPRE2").
      iSpecialize ("H" with "HPRE").
      iApply (semTWP_mono with "H").
      destruct fail_rule_pre; now iIntros ([] ?).
    Qed.

    Lemma iris_rule_tconsequence {Γ σ} {δ : CStore Γ}
            {P P'} {Q Q' : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
            (P ⊢ P') -> (forall v δ', Q' v δ' ⊢ Q v δ') ->
            semTTriple δ P' s Q' -∗ semTTriple δ P s Q.
    Proof.
        iIntros (PP QQ) "trips P".
        iApply (semTWP_mono with "[trips P]").
        + iApply "trips".
        now iApply PP.
        + iIntros ([v|m] δ') "Qp"; last auto.
        now iApply QQ.
    Qed.

    Lemma iris_rule_tframe {Γ σ} {δ : CStore Γ}
            (R P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) (s : Stm Γ σ) :
            (⊢ semTTriple δ P s Q -∗ semTTriple δ (R ∗ P) s (fun v δ' => R ∗ Q v δ'))%I.
    Proof.
        iIntros "trips [HR HP]".
        iSpecialize ("trips" with "HP"). iApply (semTWP_mono with "trips").
        iIntros ([v|m] ?) "HQ"; auto. iFrame "HR HQ".
    Qed.

    Lemma iris_rule_tpull {σ Γ} (δ : CStore Γ) (s : Stm Γ σ)
            (P : iProp Σ) (Q : Prop) (R : Val σ -> CStore Γ -> iProp Σ) :
            (⊢ (⌜ Q ⌝ -∗ semTTriple δ P s R) -∗ semTTriple δ (P ∧ bi_pure Q) s R).
    Proof.
        iIntros "QP [P %]".
        by iApply "QP".
    Qed.

    Lemma iris_rule_texist {σ Γ} (δ : CStore Γ)
            (s : Stm Γ σ) {A : Type} {P : A -> iProp Σ}
            {Q :  Val σ -> CStore Γ -> iProp Σ} :
            ⊢ ((∀ x, semTTriple δ (P x) s Q) -∗ semTTriple δ (∃ x, P x) s Q).
    Proof.
        iIntros "trips [%x Px]".
        by iApply "trips".
    Qed.

    Lemma iris_rule_tstm_val {Γ} (δ : CStore Γ)
            {τ : Ty} {v : Val τ}
            {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
            ⊢ ((P -∗ Q v δ)%I -∗ semTTriple δ P (stm_val τ v) Q).
    Proof.
        iIntros "PQ P".
        iApply semTWP_val.
        by iApply "PQ".
    Qed.

    Lemma iris_rule_tstm_exp {Γ} (δ : CStore Γ)
            {τ : Ty} {e : Exp Γ τ}
            {P : iProp Σ} {Q : Val τ -> CStore Γ -> iProp Σ} :
            ⊢ ((P -∗ Q (eval e δ) δ) -∗ semTTriple δ P (stm_exp e) Q).
    Proof.
        iIntros "PQ P".
        iApply semTWP_exp.
        now iApply "PQ".
    Qed.

    Lemma iris_rule_tstm_let {Γ} (δ : CStore Γ)
            (x : PVar) (σ τ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ)
            (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
            (R : Val τ -> CStore Γ -> iProp Σ) :
            ⊢ (semTTriple δ P s Q -∗
                        (∀ (v : Val σ) (δ' : CStore Γ),
                            semTTriple (env.snoc δ' (x∷σ) v) (Q v δ') k (fun v δ'' => R v (env.tail δ'')) ) -∗
                        semTTriple δ P (let: x := s in k) R).
    Proof.
        iIntros "trips tripk P".
        iApply semTWP_let.
        iSpecialize ("trips" with "P").
        iApply (semTWP_mono with "trips"). iIntros ([v|m] ?) "H".
        - now iSpecialize ("tripk" with "H").
        - simpl. now iApply semTWP_fail.
    Qed.

    Lemma iris_rule_tstm_block {Γ} (δ : CStore Γ)
            (Δ : PCtx) (δΔ : CStore Δ)
            (τ : Ty) (k : Stm (Γ ▻▻ Δ) τ)
            (P : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
            ⊢ (semTTriple (δ ►► δΔ) P k (fun v δ'' => R v (env.drop Δ δ'')) -∗
                    semTTriple δ P (stm_block δΔ k) R).
    Proof.
        iIntros "tripk P". iPoseProof ("tripk" with "P") as "wpk".
        by iApply semTWP_block.
    Qed.

    Lemma iris_rule_tstm_seq {Γ} (δ : CStore Γ)
            (τ : Ty) (s1 : Stm Γ τ) (σ : Ty) (s2 : Stm Γ σ)
            (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ (semTTriple δ P s1 Q -∗
                    (∀ v δ', semTTriple δ' (Q v δ') s2 R) -∗
                    semTTriple δ P (s1 ;; s2) R).
    Proof.
        iIntros "trips1 trips2 P".
        iSpecialize ("trips1" with "P").
        iApply semTWP_seq.
        iApply (semTWP_mono with "[$]"). iIntros ([v|m] ?) "H"; auto.
        - by iApply ("trips2" with "H").
        - by rewrite semTWP_fail.
    Qed.

    Lemma iris_rule_tstm_assertk {Γ τ} (δ : CStore Γ)
            (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ)
                        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (⌜ eval e1 δ = true ⌝ -∗ semTTriple δ P k Q) -∗
          (if fail_rule_pre then True else ⌜eval e1 δ ≠ false⌝) -∗
        semTTriple δ P (stm_assertk e1 e2 k) Q.
    Proof.
        iIntros "tripk Hf P".
        iApply (semTWP_assertk with "[tripk P] [Hf]").
        - iIntros (->).
          by iApply "tripk".
        - iIntros (?).
          rewrite semTWP_fail.
          destruct fail_rule_pre; auto.
          now iDestruct "Hf" as "%Hf".
    Qed.

    Lemma iris_rule_tstm_fail {Γ} (δ : CStore Γ)
            (τ : Ty) (s : Val ty.string) :
            forall (Q : Val τ -> CStore Γ -> iProp Σ),
            ⊢ semTTriple δ (if fail_rule_pre then True else False) (stm_fail τ s) Q.
    Proof.
        iIntros (Q) "H".
        destruct fail_rule_pre; auto.
        now iApply semTWP_fail.
    Qed.

    Lemma iris_rule_tstm_read_register {Γ} (δ : CStore Γ)
            {σ : Ty} (r : 𝑹𝑬𝑮 σ) (v : Val σ) :
            ⊢ (semTTriple δ (lptsreg r v) (stm_read_register r) (fun v' δ' => ⌜ δ' = δ ⌝ ∧ ⌜ v' = v ⌝ ∧ lptsreg r v)).
    Proof.
        iIntros "Hreg".
        iApply semTWP_read_register.
        iExists v.
        iFrame.
        repeat iSplit; auto.
    Qed.

    Lemma iris_rule_tstm_write_register {Γ} (δ : CStore Γ)
            {σ : Ty} (r : 𝑹𝑬𝑮 σ) (w : Exp Γ σ)
                                (Q : Val σ -> CStore Γ -> iProp Σ)
                                (v : Val σ) :
            ⊢ semTTriple δ (lptsreg r v) (stm_write_register r w)
                    (fun v' δ' => ⌜δ' = δ⌝ ∧ ⌜v' = eval w δ⌝ ∧ lptsreg r v').
    Proof.
        iIntros "Hreg".
        iApply semTWP_write_register.
        iExists v.
        iFrame.
        repeat iSplit; auto.
    Qed.

    Lemma iris_rule_tstm_assign {Γ} (δ : CStore Γ)
            (x : PVar) (σ : Ty) (xIn : x∷σ ∈ Γ) (s : Stm Γ σ)
            (P : iProp Σ) (R : Val σ -> CStore Γ -> iProp Σ) :
            ⊢ (semTTriple δ P s (fun v δ' => R v (@env.update _ _ _ δ' (x∷_) _ v)) -∗
            semTTriple δ P (stm_assign x s) R).
    Proof.
        iIntros "trips P".
        iSpecialize ("trips" with "P").
        by iApply semTWP_assign.
    Qed.

    Lemma iris_rule_tstm_bind {Γ} (δ : CStore Γ)
            {σ τ : Ty} (s : Stm Γ σ) (k : Val σ -> Stm Γ τ)
            (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ)
            (R : Val τ -> CStore Γ -> iProp Σ) :
            ⊢ (semTTriple δ P s Q -∗
            (∀ (v__σ : Val σ) (δ' : CStore Γ),
                semTTriple δ' (Q v__σ δ') (k v__σ) R) -∗
            semTTriple δ P (stm_bind s k) R).
    Proof.
        iIntros "trips tripk P".
        iSpecialize ("trips" with "P").
        iApply semTWP_bind. iApply (semTWP_mono with "trips"). iIntros ([v|m] ?) "H".
        - simpl. by iApply "tripk".
        - simpl. by iApply semTWP_fail.
    Qed.

    Lemma iris_rule_tstm_call_inline
        {Γ} (δΓ : CStore Γ)
        {Δ σ} (f : 𝑭 Δ σ) (es : NamedEnv (Exp Γ) Δ)
        (P : iProp Σ) (Q : Val σ -> CStore Γ -> iProp Σ) :
        ⊢ semTTriple (evals es δΓ) P (FunDef f) (fun v _ => Q v δΓ) -∗
        semTTriple δΓ P (stm_call f es) Q.
    Proof.
        iIntros "trips P". iSpecialize ("trips" with "P").
        now iApply semTWP_call_inline.
    Qed.

    Lemma iris_rule_tstm_debugk
        {Γ τ} (δ : CStore Γ) (k : Stm Γ τ)
        (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
        ⊢ (semTTriple δ P k Q -∗
        semTTriple δ P (stm_debugk k) Q).
    Proof. iIntros "tripk P". iApply semTWP_debugk. now iApply "tripk". Qed.

    Lemma iris_rule_tnoop {Γ σ} {δ : CStore Γ}
            {P} {Q : Val σ -> CStore Γ -> iProp Σ} {s : Stm Γ σ} :
        stm_to_val s = None ->
        (forall {s' γ γ' μ μ' δ'}, ⟨ γ, μ, δ, s ⟩ ---> ⟨ γ', μ', δ', s' ⟩ ->
                                (γ' = γ) /\ (μ' = μ) /\ (δ' = δ) /\
                                ((exists v, s' = stm_val _ v) \/ (exists msg, s' = stm_fail _ msg))) ->
        (∀ v, P ={⊤}=∗ Q v δ) -∗
                    semTTriple δ P s Q.
    Proof.
        iIntros (Hnv Hnoop) "HPQ HP".
        rewrite semTWP_unfold /semTWP_pre. rewrite Hnv.
        iIntros (γ1 μ1) "state_inv".
        iMod (fupd_mask_subseteq empty) as "Hclose"; first set_solver. iModIntro.
        iIntros (s2 δ2 γ2 μ2) "%".
        destruct (Hnoop _ _ _ _ _ _ H) as (-> & -> & -> & [[v ->]|[msg ->]]).
        - iModIntro. iMod "Hclose" as "_".
        iFrame. iApply semTWP_val. now iApply "HPQ".
        - iModIntro. iMod "Hclose" as "_".
        iFrame. iApply semTWP_fail.
    Abort.

    Lemma iris_rule_tstm_pattern_match {Γ τ σ} (δΓ : CStore Γ)
        (s : Stm Γ σ) (pat : Pattern σ)
        (rhs : ∀ pc : PatternCase pat, Stm (Γ ▻▻ PatternCaseCtx pc) τ)
        (P : iProp Σ) (Q : Val σ → CStore Γ → iProp Σ) (R : Val τ → CStore Γ → iProp Σ) :
        ⊢ semTTriple δΓ P s Q -∗
        (∀ pc δpc δΓ1,
            semTTriple (δΓ1 ►► δpc) (Q (pattern_match_val_reverse pat pc δpc) δΓ1) (rhs pc)
            (λ vτ (δ' : CStore (Γ ▻▻ PatternCaseCtx pc)), R vτ (env.drop (PatternCaseCtx pc) δ'))) -∗
        semTTriple δΓ P (stm_pattern_match s pat rhs) R.
    Proof.
        iIntros "WPs WPrhs P".
        iSpecialize ("WPs" with "P").
        iApply semTWP_pattern_match.
        iApply (semTWP_mono with "WPs").
        iIntros ([vσ|m] δΓ') "Q"; auto.
        destruct pattern_match_val as [pc δpc] eqn:Heq.
        iApply "WPrhs".
        change (pattern_match_val_reverse pat pc δpc) with
        (pattern_match_val_reverse' pat (existT pc δpc)).
        rewrite <- Heq.
        now rewrite pattern_match_val_inverse_left.
    Qed.

    Definition TValidContractSemCurried {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
        match contract with
        | MkSepContract _ _ ctxΣ θΔ pre result post =>
        Sep.Logic.Forall (fun (ι : Valuation ctxΣ) =>
            semTTriple (inst θΔ ι) (asn.interpret pre ι) body
                    (fun v δ' => asn.interpret post (env.snoc ι (result∷σ) v)))
        end.

    (* Uses projections, see [ValidContractSem]. *)
    Definition TValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) : iProp Σ :=
        ∀ (ι : Valuation (sep_contract_logic_variables contract)),
            semTTriple (inst (sep_contract_localstore contract) ι)
                    (asn.interpret (sep_contract_precondition contract) ι) body
                    (fun v δ' => asn.interpret (sep_contract_postcondition contract)
                                   (env.snoc ι (sep_contract_result contract∷σ) v)).

    Lemma TValidContractSem_ValidContractSem {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) :
      TValidContractSem body contract ⊢
      ValidContractSem body contract.
    Proof.
      rewrite /TValidContractSem /ValidContractSem. destruct contract.
      iIntros "H" (?). now iApply semTTriple_semTriple.
    Qed.

    Definition TValidContractForeign {Δ τ} (contract : SepContract Δ τ) (f : 𝑭𝑿 Δ τ) : Prop :=
        forall Γ (es : NamedEnv (Exp Γ) Δ) (δ : CStore Γ),
        match contract with
        | MkSepContract _ _ Σ' θΔ req result ens =>
            forall (ι : Valuation Σ'),
            evals es δ = inst θΔ ι ->
            ⊢ semTTriple δ (asn.interpret req ι) (stm_foreign f es)
            (fun v δ' => asn.interpret ens (env.snoc ι (result∷τ) v) ∗ bi_pure (δ' = δ))
        end.

    Lemma TValidContractForeign_ValidContractForeign {Δ τ}
      {contract : SepContract Δ τ} {f : 𝑭𝑿 Δ τ} :
      TValidContractForeign contract f -> ValidContractForeign contract f.
    Proof.
      rewrite /TValidContractForeign /ValidContractForeign. destruct contract.
      intros H ? ? ? ? Hevals. specialize (H _ _ _ _ Hevals).
      now iApply semTTriple_semTriple.
    Qed.

    Definition tvalid_contract_curry {Δ σ} (body : Stm Δ σ) (contract : SepContract Δ σ) :
        TValidContractSem body contract ⊣⊢ TValidContractSemCurried body contract.
    Proof.
        destruct contract as [lvars δ req res ens]; cbn.
        now rewrite Forall_forall.
    Qed.
  End TotalTriple.
End Soundness.
End IrisSignatureRules.

Module Type IrisAdeqParameters
  (Import GLOBAL : GlobalState)
  (Import IP     : IrisParameters GLOBAL).

  Parameter Inline memGpreS : gFunctors -> Set.
  Parameter memΣ : gFunctors.
  Parameter memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ.
  Parameter mem_res : forall `{mG : memGS Σ}, Memory -> iProp Σ.
  Parameter mem_init : forall `{mGS : memGpreS Σ} (μ : Memory),
                                         ⊢ |==> ∃ mG : memGS Σ, (mem_state_interp (mG := mG) μ ∗ mem_res (mG := mG) μ)%I.

End IrisAdeqParameters.

Module Type IrisAdequacy
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import PLOG   : ProgramLogic GLOBAL SIG PROG)
  (Import IPre   : IrisPrelims GLOBAL PROG SEM)
  (Import IB     : IrisBase GLOBAL PROG SEM IPre)
  (Import IAP    : IrisAdeqParameters GLOBAL IB)
  (Import IPred  : IrisPredicates GLOBAL SIG PROG SEM IPre IB)
  (Import IRules : IrisSignatureRules GLOBAL SIG PROG SEM PLOG IPre IB IPred).

  Import SmallStepNotations.

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

  #[local] Instance subG_sailGpreS {Σ} : subG sailΣ Σ -> sailGpreS Σ.
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

  Definition own_regstore `{sailGS Σ} (γ : RegStore) : iProp Σ :=
    [∗ list] _ ↦ x ∈ finite.enum (sigT 𝑹𝑬𝑮),
      match x with | existT _ r => reg_pointsTo r (read_register γ r) end.

  Lemma not_stuck_ever {Γ τ} :
    ∀ (e : expr (microsail_lang Γ τ)) σ,
      not_stuck e σ.
  Proof.
    intros [s δ] [γ μ]. unfold not_stuck. cbn. destruct (stm_to_val s) eqn:Es.
    - left. auto.
    - right. apply reducible_not_val. auto.
  Qed.

  Lemma adequacy {SPEC : Specification} {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'}
        {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : Val σ -> Prop} :
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ -> Final s' ->
    (forall `{sailGS Σ'}, ⊢ semTriple δ (mem_res μ ∗ own_regstore γ) s (fun v _ => ⌜ Q v ⌝)) ->
    ResultOrFail s' Q.
  Proof.
    intros steps fins trips.
    cut (adequate NotStuck (MkConf s δ) (γ,μ)
                  (λ v _, @ResultOrFail Γ _ (of_ival (valconf_val v)) Q)).
    - destruct s'; cbn in fins; destruct fins; last done.
      intros adeq.
      apply (adequate_result NotStuck (MkConf s δ) (γ , μ)
               (λ v _, ResultOrFail (of_ival (valconf_val v)) Q)
               adeq nil (γ' , μ') (MkValConf (inl v) δ')
               (steps_to_erased steps)).
    - constructor.
      + intros t2 σ2 [v2 δ2] eval.
        assert (regsmapv := RegStore_to_map_valid γ).
        pose proof (wp_adequacy sailΣ (microsail_lang Γ σ) NotStuck (MkConf s δ) (γ , μ) (λ v, @ResultOrFail Γ _ (of_ival (valconf_val v)) Q)) as adeq.
        refine (adequate_result _ _ _ _ (adeq _) _ _ _ eval); clear adeq.
        iIntros (Hinv κs) "".
        iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]";
          first by apply auth_both_valid.
        pose proof (memΣ_GpreS (Σ := sailΣ) _) as mGS.
        iMod (mem_init (mGS := mGS) μ) as (memG) "[Hmem Rmem]".
        iModIntro.
        iExists (fun σ _ => regs_inv (srGS := (SailRegGS _ spec_name)) (σ.1) ∗ mem_state_interp (σ.2))%I.
        iExists _.
        iSplitR "Hs2 Rmem".
        * iFrame "Hmem".
          now iApply own_RegStore_to_regs_inv.
        * iPoseProof (trips _ (SailGS Hinv (SailRegGS reg_pre_inG spec_name) memG) with "[$Rmem Hs2]") as "H".
          iApply (own_RegStore_to_map_reg_pointsTos (srGS := SailRegGS reg_pre_inG spec_name)(γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2").
          eapply finite.NoDup_enum.
          iApply (wp_mono with "H"). iIntros ([]) "H"; auto.
          simpl. now case_match.
      + intros. apply not_stuck_ever.
  Qed.

  Lemma adequacy_gen {Γ σ} (s : Stm Γ σ) {γ γ'} {μ μ'}
        {δ δ' : CStore Γ} {s' : Stm Γ σ} {Q : forall `{sailGS Σ}, IVal σ -> CStore Γ -> iProp Σ} (φ : Prop):
    ⟨ γ, μ, δ, s ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->
    (forall `{sailGS Σ', memGpreS Σ'},
        mem_res μ ∗ own_regstore γ ⊢ |={⊤}=> semWP δ s Q
          ∗ (mem_state_interp μ' ={⊤,∅}=∗ ⌜φ⌝)
    )%I -> φ.
  Proof.
    (* intros steps trips. *)
    intros [n steps]%steps_to_nsteps trips.
    refine (wp_strong_adequacy sailΣ (microsail_lang Γ σ) _ _ _ _ _ _ _ _ (fun _ => 0) _ steps).
    iIntros (Hinv) "".
    assert (regsmapv := RegStore_to_map_valid γ).
    iMod (own_alloc ((● RegStore_to_map γ ⋅ ◯ RegStore_to_map γ ) : regUR)) as (spec_name) "[Hs1 Hs2]";
        first by apply auth_both_valid.
    pose proof (memΣ_GpreS (Σ := sailΣ) _) as mGS.
    iMod (mem_init (mGS := mGS) μ) as (memG) "[Hmem Rmem]".
    pose (regsG := {| reg_inG := @reg_pre_inG sailΣ (@subG_sailGpreS sailΣ (subG_refl sailΣ)); reg_gv_name := spec_name |}).
    pose (sailG := SailGS Hinv regsG memG).
    iMod (trips sailΣ sailG mGS with "[$Rmem Hs2]") as "[trips Hφ]".
    {unfold own_regstore.
      iApply (own_RegStore_to_map_reg_pointsTos (srGS := regsG) (γ := γ) (l := finite.enum (sigT 𝑹𝑬𝑮)) with "Hs2").
      eapply finite.NoDup_enum.
    }
    iModIntro.
    iExists (fun σ _ _ _ => regs_inv (srGS := (SailRegGS _ spec_name)) (σ.1) ∗ mem_state_interp (σ.2))%I.
    iExists [ λ v, Q _ sailG (valconf_val v) (valconf_store v)]%list.
    iExists _.
    iExists _.
    iSplitR "trips Hφ".
    * iFrame "Hmem".
      now iApply own_RegStore_to_regs_inv.
    * cbn. iFrame.
      iIntros (es' t2') "_ _ _ [Hregsinv Hmeminv] _ _".
      now iApply "Hφ".
  Qed.

End IrisAdequacy.

Module Type IrisInstance (GLOBAL : GlobalState) (SIG : Signature GLOBAL) (PROG : Program GLOBAL) (SEM : Semantics GLOBAL PROG) (PLOG : ProgramLogic GLOBAL SIG PROG) (IPre : IrisPrelims GLOBAL PROG SEM) (IB : IrisBase GLOBAL PROG SEM IPre) :=
  IrisPredicates GLOBAL SIG PROG SEM IPre IB <+ IrisSignatureRules GLOBAL SIG PROG SEM PLOG IPre IB.

(*
 * The following module defines the parts of the Iris model that must depend on the Specification, not just on the Signature.
 * This is kept to a minimum (see comment for the IrisPredicates module).
 *)
Module IrisInstanceWithContracts
  (Import GLOBAL : GlobalState)
  (Import SIG    : Signature GLOBAL)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import PLOG   : ProgramLogic GLOBAL SIG PROG)
  (Import IPre   : IrisPrelims GLOBAL PROG SEM)
  (Import IB     : IrisBase GLOBAL PROG SEM IPre)
  (Import II     : IrisInstance GLOBAL SIG PROG SEM PLOG IPre IB).

  Section WithSailGS.
    Import ProgLog.
    Context {Σ} {sG : sailGS Σ} {rG : resGS Σ}.

    Section PartialTriple.
      Context {SPEC : Specification}.

        Definition ValidContractEnvSem (cenv : SepContractEnv) : iProp Σ :=
            (∀ σs σ (f : 𝑭 σs σ),
            match cenv σs σ f with
            | Some c => ValidContractSem (FunDef f) c
            | None => True
            end)%I.

        Definition ForeignSem :=
            ∀ (Δ : PCtx) (τ : Ty) (f : 𝑭𝑿 Δ τ),
            ValidContractForeign (CEnvEx f) f.

        Definition LemmaSem : Prop :=
            forall (Δ : PCtx) (l : 𝑳 Δ),
            ValidLemma (LEnv l).

        Lemma iris_rule_stm_call {Γ} (δ : CStore Γ)
            {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ)
            (P : iProp Σ)
            (Q : Val σ -> CStore Γ -> iProp Σ) :
            CEnv f = Some c ->
            CTriple P c (evals es δ) (fun v => Q v δ) ->
            ⊢ ▷ ValidContractEnvSem CEnv -∗
            semTriple δ P (stm_call f es) Q.
        Proof.
            iIntros (ceq ctrip) "cenv P".
            iApply semWP_call_inline_later.
            iModIntro.
            iSpecialize ("cenv" $! _ _ f).
            rewrite ceq. clear ceq.
            destruct c as [Σe δΔ req res ens]; cbn in *.
            iPoseProof (ctrip with "P") as (ι Heq) "[req consr]". clear ctrip.
            iPoseProof ("cenv" $! ι with "req") as "wpf0". rewrite Heq.
            iApply (semWP_mono with "wpf0").
            iIntros ([] _) "H"; auto. by iApply "consr".
        Qed.

        Lemma iris_rule_stm_call_frame {Γ} (δ : CStore Γ)
                (Δ : PCtx) (δΔ : CStore Δ) (τ : Ty) (s : Stm Δ τ)
                (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
                ⊢ (semTriple δΔ P s (fun v _ => Q v δ) -∗
                semTriple δ P (stm_call_frame δΔ s) Q).
        Proof.
            iIntros "trips P".
            iSpecialize ("trips" with "P").
            by iApply semWP_call_frame.
        Qed.

        Lemma iris_rule_stm_foreign
            {Γ} (δ : CStore Γ) {τ} {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
            (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
            ForeignSem ->
            CTriple P (CEnvEx f) (evals es δ) (λ v : Val τ, Q v δ) ->
            ⊢ semTriple δ P (stm_foreign f es) Q.
        Proof.
            iIntros (forSem ctrip) "P".
            specialize (forSem Δ τ f Γ es δ).
            destruct CEnvEx as [Σe δΔ req res ens]; cbn in *.
            iPoseProof (ctrip with "P") as "[%ι [%Heq [req consr]]]". clear ctrip.
            iPoseProof (forSem ι Heq with "req") as "WPf". clear forSem.
            iApply (semWP_mono with "WPf").
            iIntros ([v|m] δΓ'); auto; iIntros "[ens ->]".
            by iApply "consr".
        Qed.

        Lemma iris_rule_stm_lemmak
            {Γ} (δ : CStore Γ) {τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
            (P Q : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
            LemmaSem ->
            LTriple (evals es δ) P Q (LEnv l) ->
            ⊢ semTriple δ Q k R -∗
            semTriple δ P (stm_lemmak l es k) R.
        Proof.
            iIntros (lemSem ltrip) "tripk P". iApply semWP_lemmak. iApply "tripk".
            specialize (lemSem _ l). remember (LEnv l) as contractL.
            clear - lemSem ltrip.
            destruct ltrip as [Ψ' pats req ens ent]; cbn in lemSem.
            iPoseProof (ent with "P") as (ι Heq) "[req consr]".
            iApply "consr". by iApply lemSem.
        Qed.

        Lemma sound_stm
            {Γ} {τ} (s : Stm Γ τ) {δ : CStore Γ}:
            forall (PRE : iProp Σ) (POST : Val τ -> CStore Γ -> iProp Σ),
            ForeignSem ->
            LemmaSem ->
            ⦃ PRE ⦄ s ; δ ⦃ POST ⦄ ->
            ⊢ (□ ▷ ValidContractEnvSem CEnv -∗
                semTriple δ PRE s POST)%I.
        Proof.
            iIntros (PRE POST extSem lemSem triple) "#vcenv".
            iInduction triple as [x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x] "trips".
            - by iApply iris_rule_consequence.
            - by iApply iris_rule_frame.
            - by iApply iris_rule_pull.
            - by iApply iris_rule_exist.
            - iApply iris_rule_stm_val.
            by iApply H.
            - iApply iris_rule_stm_exp.
            by iApply H.
            - by iApply iris_rule_stm_let.
            - by iApply iris_rule_stm_block.
            - by iApply iris_rule_stm_seq.
            - iApply iris_rule_stm_assertk; auto.
              destruct fail_rule_pre; auto.
            - by iApply iris_rule_stm_fail.
            - by iApply iris_rule_stm_read_register.
            - by iApply iris_rule_stm_write_register.
            - by iApply iris_rule_stm_assign.
            - by iApply iris_rule_stm_call.
            - by iApply iris_rule_stm_call_inline.
            - by iApply iris_rule_stm_call_frame.
            - by iApply iris_rule_stm_foreign.
            - by iApply iris_rule_stm_lemmak.
            - by iApply iris_rule_stm_bind.
            - by iApply iris_rule_stm_debugk.
            - by iApply iris_rule_stm_pattern_match.
        Qed.

        Lemma sound :
            ForeignSem -> LemmaSem -> ValidContractCEnv ->
            ⊢ ValidContractEnvSem CEnv.
        Proof.
            intros extSem lemSem vcenv.
            iLöb as "IH".
            iIntros (σs σ f).
            specialize (vcenv σs σ f).
            destruct (CEnv f) as [[]|];[|trivial].
            iIntros (ι).
            specialize (vcenv _ eq_refl ι).
            now iApply (sound_stm extSem lemSem vcenv).
        Qed.
    End PartialTriple.

    Import callgraph.

    Section TotalTriple.

      Context {SPEC : Specification}.

      Definition HasValidContract (n : Node) : iProp Σ :=
        match CEnv (f n) with
        | Some c => TValidContractSem (FunDef (f n)) c
        | None => True
        end.

      Definition TValidContractEnvN (cenv : SepContractEnv) (n : Node) : iProp Σ :=
        ⌜ Accessible 𝑭_call_graph n ⌝ -∗ HasValidContract n.

      Definition TValidContractEnvSem (cenv : SepContractEnv) : iProp Σ :=
        ∀ (n : Node), TValidContractEnvN cenv n.

        Definition TForeignSem :=
          ∀ (Δ : PCtx) (τ : Ty) (f : 𝑭𝑿 Δ τ),
          TValidContractForeign (CEnvEx f) f.

        Lemma TForeignSem_ForeignSem :
          TForeignSem -> ForeignSem.
        Proof.
          rewrite /TForeignSem /ForeignSem. intros H ? ? f. specialize (H _ _ f).
          now apply TValidContractForeign_ValidContractForeign.
        Qed.

        Lemma iris_rule_tstm_call_one {Γ} (δ : CStore Γ)
          {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ)
          (P : iProp Σ)
          (Q : Val σ -> CStore Γ -> iProp Σ) :
          CEnv f = Some c ->
          CTriple P c (evals es δ) (fun v => Q v δ) ->
          ⊢ TValidContractSem (FunDef f) c -∗
          semTTriple δ P (stm_call f es) Q.
        Proof.
          iIntros (ceq ctrip) "cenv P".
          iApply semTWP_call_inline.
          destruct c as [Σe δΔ req res ens]; cbn in *.
          iPoseProof (ctrip with "P") as (ι Heq) "[req consr]". clear ctrip.
          iPoseProof ("cenv" $! ι with "req") as "wpf0". rewrite Heq.
          iApply (semTWP_mono with "wpf0").
          iIntros ([] _) "H"; auto. by iApply "consr".
        Qed.
        
        Lemma iris_rule_tstm_call {Γ} (δ : CStore Γ)
          {Δ σ} (f : 𝑭 Δ σ) (c : SepContract Δ σ) (es : NamedEnv (Exp Γ) Δ)
          (P : iProp Σ)
          (Q : Val σ -> CStore Γ -> iProp Σ) :
          CEnv f = Some c ->
          CTriple P c (evals es δ) (fun v => Q v δ) ->
          Accessible 𝑭_call_graph f ->
          ⊢ TValidContractEnvSem CEnv -∗
            semTTriple δ P (stm_call f es) Q.
        Proof.
          iIntros (ceq ctrip Hwff) "cenv".
          iApply iris_rule_tstm_call_one; eauto.
          iSpecialize ("cenv" $! _ Hwff).
          unfold HasValidContract.
          simpl.
          now rewrite ceq.
        Qed.

        Lemma iris_rule_tstm_call_frame {Γ} (δ : CStore Γ)
          (Δ : PCtx) (δΔ : CStore Δ) (τ : Ty) (s : Stm Δ τ)
          (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
          ⊢ (semTTriple δΔ P s (fun v _ => Q v δ) -∗
          semTTriple δ P (stm_call_frame δΔ s) Q).
        Proof.
          iIntros "trips P".
          iSpecialize ("trips" with "P").
          by iApply semTWP_call_frame.
        Qed.

        Lemma iris_rule_tstm_foreign
          {Γ} (δ : CStore Γ) {τ} {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ)
          (P : iProp Σ) (Q : Val τ -> CStore Γ -> iProp Σ) :
          TForeignSem ->
          CTriple P (CEnvEx f) (evals es δ) (λ v : Val τ, Q v δ) ->
          ⊢ semTTriple δ P (stm_foreign f es) Q.
        Proof.
          iIntros (forSem ctrip) "P".
          specialize (forSem Δ τ f Γ es δ).
          destruct CEnvEx as [Σe δΔ req res ens]; cbn in *.
          iPoseProof (ctrip with "P") as "[%ι [%Heq [req consr]]]". clear ctrip.
          iPoseProof (forSem ι Heq with "req") as "WPf". clear forSem.
          iApply (semTWP_mono with "WPf").
          iIntros ([v|m] δΓ'); auto; iIntros "[ens ->]".
          by iApply "consr".
        Qed.

        Lemma iris_rule_tstm_lemmak
          {Γ} (δ : CStore Γ) {τ} {Δ} (l : 𝑳 Δ) (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ)
          (P Q : iProp Σ) (R : Val τ -> CStore Γ -> iProp Σ) :
          LemmaSem ->
          LTriple (evals es δ) P Q (LEnv l) ->
          ⊢ semTTriple δ Q k R -∗
          semTTriple δ P (stm_lemmak l es k) R.
        Proof.
          iIntros (lemSem ltrip) "tripk P". iApply semTWP_lemmak. iApply "tripk".
          specialize (lemSem _ l). remember (LEnv l) as contractL.
          clear - lemSem ltrip.
          destruct ltrip as [Ψ' pats req ens ent]; cbn in lemSem.
          iPoseProof (ent with "P") as (ι Heq) "[req consr]".
          iApply "consr". by iApply lemSem.
        Qed.

        Lemma sound_tstm {Γ} {τ} (s : Stm Γ τ) (n : Node) {δ : CStore Γ} :
          forall (PRE : iProp Σ) (POST : Val τ -> CStore Γ -> iProp Σ),
            TForeignSem ->
            LemmaSem ->
            ⦃ PRE ⦄ s ; δ ⦃ POST ⦄ ->
            StmWellFormed (𝑭_call_graph n) s ->
            ⊢ □ (∀ x : Node, ⌜Relation_Operators.clos_trans Node (InvokedBy 𝑭_call_graph) x n⌝ -∗
                                HasValidContract x) -∗
              semTTriple δ PRE s POST.
        Proof.
          iIntros (PRE POST extSem lemSem triple Hwf) "#IH".
          iInduction triple as [x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x|x] "trips" forall (n Hwf) "IH".
          - iApply iris_rule_tconsequence; eauto.
            now iApply "trips".
          - iApply iris_rule_tframe.
            now iApply "trips".
          - iApply iris_rule_tpull.
            iIntros (HQ).
            now iApply "trips".
          - iApply iris_rule_texist.
            iIntros (HQ).
            now iApply "trips".
          - iApply iris_rule_tstm_val.
            by iApply H.
          - iApply iris_rule_tstm_exp.
            by iApply H.
          - iApply iris_rule_tstm_let.
            + iApply ("trips1" with "[%] IH").
              apply Hwf.
            + iIntros (v δ'). iApply ("trips" with "[%] IH").
              apply Hwf.
          - iApply iris_rule_tstm_block.
            iApply ("trips" with "[%] IH").
            apply Hwf.
          - iApply iris_rule_tstm_seq.
            + iApply ("trips1" with "[%] IH").
              apply Hwf.
            + iIntros (v δ'). iApply ("trips" with "[%] IH").
              apply Hwf.
          - iApply iris_rule_tstm_assertk.
            + iIntros (Heval).
              iApply ("trips" $! Heval with "[%] IH").
              apply Hwf.
            + destruct fail_rule_pre; auto.
          - iApply iris_rule_tstm_fail.
          - iApply iris_rule_tstm_read_register.
          - now iApply iris_rule_tstm_write_register.
          - iApply iris_rule_tstm_assign.
            iApply ("trips" with "[%] IH").
            apply Hwf.
          - iApply iris_rule_tstm_call_one; eauto.
            cbn in Hwf.
            unfold HasValidContract.
            iSpecialize ("IH" $! f0).
            cbn. rewrite H.
            iApply "IH". iPureIntro. constructor. apply Hwf.
          - iApply iris_rule_tstm_call_inline.
            iApply "trips".
            + iPureIntro.
              apply 𝑭_call_graph_wellformed.
            + iClear "trips".
              iIntros "!>" (n' Hrel).
              iApply "IH". iPureIntro.
              cbn [StmWellFormed] in Hwf.
              eapply clos_trans_stepr; eauto.
          - iApply iris_rule_tstm_call_frame.
            iApply ("trips" with "[%] IH").
            apply Hwf.
          - now iApply iris_rule_tstm_foreign.
          - iApply iris_rule_tstm_lemmak; eauto.
            iApply ("trips" with "[%] IH").
            apply Hwf.
          - iApply iris_rule_tstm_bind.
            + iApply ("trips1" with "[%] IH").
              apply Hwf.
            + iIntros (v__σ δ'). iApply ("trips" with "[%] IH").
              apply Hwf.
          - iApply iris_rule_tstm_debugk.
            iApply ("trips" with "[%] IH").
            apply Hwf.
          - iApply iris_rule_tstm_pattern_match.
            + iApply ("trips1" with "[%] IH").
              apply Hwf.
            + iIntros (pc δpc δΓ1). iApply ("trips" with "[%] IH").
              apply Hwf.
        Qed.

        Lemma tsound :
          TForeignSem -> LemmaSem -> TValidContractCEnv ->
          ⊢ TValidContractEnvSem CEnv.
        Proof.
          iIntros (extSem lemSem cenv n Hwf).
          apply Stdlib.Wellfounded.Transitive_Closure.Acc_clos_trans in Hwf.
          iInduction Hwf as [n _ IH].
          unfold HasValidContract at 2.
          destruct (CEnv _) as [c|] eqn:Ec; last trivial.
          specialize (cenv _ _ _ _ Ec).
          unfold TValidContract in cenv.
          generalize (𝑭_call_graph_wellformed _ _ (f n)).
          cbn in c, cenv. cbn.
          generalize cenv.
          generalize (FunDef (f n)).
          intros s cenv'.
          iIntros (Hwf).
          destruct c. iIntros (ι).
          specialize (cenv' ι). cbn in cenv'.
          destruct n. cbn.
          iApply sound_tstm; eauto.
        Qed.
    End TotalTriple.
  End WithSailGS.
End IrisInstanceWithContracts.
