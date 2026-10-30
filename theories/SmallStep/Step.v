(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel, Georgy Lukyanov                         *)
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
     ZArith.BinInt.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Notations
     Program
     Tactics.

Set Implicit Arguments.

Module Type SmallStepOn (Import GLOBAL : GlobalState) (Import P : Program GLOBAL).

  Import ctx.notations.
  Import env.notations.

  Inductive Step {Γ : PCtx} {τ : Ty} (γ : RegStore) (μ : Memory) (δ : CStore Γ) :
    forall (γ2 : RegStore) (μ2 : Memory) (δ2 : CStore Γ) (s1 s2 : Stm Γ τ), Prop :=

  | st_exp
      (e : Exp Γ τ) :
      ⟨ γ , μ , δ , (stm_exp e) ⟩ ---> ⟨ γ , μ , δ , stm_val τ (eval e δ) ⟩

  | st_let
      (x : PVar) (σ : Ty) (s : Stm Γ σ) (k : Stm (Γ ▻ x∷σ) τ) :
      ⟨ γ , μ , δ , stm_let x σ s k ⟩ --->
      ⟨ γ, μ , δ , stm_bind s (fun v => stm_block (env.snoc env.nil (x∷σ) v) k) ⟩

  | st_block_value
      (Δ : PCtx) (δΔ : CStore Δ) (v : Val τ) :
      ⟨ γ , μ , δ , stm_block δΔ (stm_val τ v) ⟩ ---> ⟨ γ , μ , δ , stm_val τ v ⟩
  | st_block_fail
      (Δ : PCtx) (δΔ : CStore Δ) (s : string) :
      ⟨ γ , μ , δ , stm_block δΔ (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | st_block_step
      (Δ : PCtx) (δΔ δΔ' : CStore Δ) (k k' : Stm (Γ ▻▻ Δ) τ)
      (γ' : RegStore) (μ' : Memory) (δ' : CStore Γ) :
      ⟨ γ , μ , δ ►► δΔ , k ⟩ ---> ⟨ γ', μ' , δ' ►► δΔ' , k' ⟩ ->
      ⟨ γ , μ , δ , stm_block δΔ k ⟩ ---> ⟨ γ' , μ' , δ' , stm_block δΔ' k' ⟩

  | st_seq
      (σ : Ty) (s : Stm Γ σ) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_seq s k ⟩ ---> ⟨ γ , μ , δ , stm_bind s (fun _ => k) ⟩

  | st_call
      {Δ} (f : 𝑭 Δ τ) (es : NamedEnv (Exp Γ) Δ) :
      ⟨ γ , μ , δ , stm_call f es ⟩ --->
      ⟨ γ , μ , δ , stm_call_frame (evals es δ) (FunDef f) ⟩
  | st_call_frame_value
      (Δ : PCtx) {δΔ : CStore Δ} (v : Val τ) :
      ⟨ γ , μ , δ , stm_call_frame δΔ (stm_val τ v) ⟩ ---> ⟨ γ , μ , δ , stm_val τ v ⟩
  | st_call_frame_fail
      (Δ : PCtx) {δΔ : CStore Δ} (s : string) :
      ⟨ γ , μ , δ , stm_call_frame δΔ (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | st_call_frame_step
      (Δ : PCtx) {δΔ δΔ' : CStore Δ} (s s' : Stm Δ τ)
      (γ' : RegStore) (μ' : Memory) :
      ⟨ γ , μ , δΔ , s ⟩ ---> ⟨ γ' , μ' , δΔ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_call_frame δΔ s ⟩ ---> ⟨ γ' , μ' , δ , stm_call_frame δΔ' s' ⟩
  | st_foreign
      {Δ} (f : 𝑭𝑿 Δ τ) (es : NamedEnv (Exp Γ) Δ) (res : string + Val τ)
      (γ' : RegStore) (μ' : Memory) :
      ForeignCall f (evals es δ) res γ γ' μ μ' ->
      ⟨ γ  , μ  , δ , stm_foreign f es ⟩ --->
      ⟨ γ' , μ' , δ , match res with
                      | inl msg => stm_fail τ msg
                      | inr v__σ  => stm_val τ v__σ
                      end ⟩
  | st_lemmak
      {Δ} {l : 𝑳 Δ} (es : NamedEnv (Exp Γ) Δ) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_lemmak l es k ⟩ --->
      ⟨ γ , μ , δ , k ⟩

  | st_assign_value
      (x : PVar) {xInΓ : x∷τ ∈ Γ} (v : Val τ) :
      ⟨ γ , μ , δ , stm_assign x (stm_val τ v) ⟩ ---> ⟨ γ , μ , δ ⟪ x ↦ v ⟫ , stm_val τ v ⟩
  | st_assign_fail
      (x : PVar) {xInΓ : x∷τ ∈ Γ} (s : string) :
      ⟨ γ , μ , δ , stm_assign x (stm_fail τ s) ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | st_assign_step
      (x : PVar) {xInΓ : x∷τ ∈ Γ} (s s' : Stm Γ τ)
      (γ' : RegStore) (μ' : Memory) (δ' : CStore Γ) :
      ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ' , μ' , δ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_assign x s ⟩ ---> ⟨ γ' , μ' , δ' , stm_assign x s' ⟩

  | st_assertk
      (e1 : Exp Γ ty.bool) (e2 : Exp Γ ty.string) (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_assertk e1 e2 k ⟩ --->
      ⟨ γ , μ , δ , if eval e1 δ then k else stm_fail τ (eval e2 δ) ⟩

  | st_read_register
      (r : 𝑹𝑬𝑮 τ) :
      ⟨ γ, μ , δ, stm_read_register r ⟩ ---> ⟨ γ, μ , δ, stm_val τ (read_register γ r) ⟩
  | st_write_register
      (r : 𝑹𝑬𝑮 τ) (e : Exp Γ τ) :
      let v := eval e δ in
      ⟨ γ , μ , δ, stm_write_register r e ⟩ ---> ⟨ write_register γ r v , μ , δ , stm_val τ v ⟩

  | st_bind_value
      (σ : Ty) (v : Val σ) (k : Val σ -> Stm Γ τ) :
      ⟨ γ , μ , δ , stm_bind (stm_val σ v) k ⟩ ---> ⟨ γ , μ , δ , k v ⟩
  | st_bind_fail
      (σ : Ty) (s : string) (k : Val σ -> Stm Γ τ) :
      ⟨ γ , μ , δ , stm_bind (stm_fail σ s) k ⟩ ---> ⟨ γ , μ , δ , stm_fail τ s ⟩
  | st_bind_step
      (σ : Ty) (s s' : Stm Γ σ) (k : Val σ -> Stm Γ τ)
      (γ' : RegStore) (μ' : Memory) (δ' : CStore Γ) :
      ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ', μ' , δ' , s' ⟩ ->
      ⟨ γ , μ , δ , stm_bind s k ⟩ ---> ⟨ γ', μ' , δ' , stm_bind s' k ⟩

  | st_debugk
      (k : Stm Γ τ) :
      ⟨ γ , μ , δ , stm_debugk k ⟩ ---> ⟨ γ , μ , δ , k ⟩

  | st_pattern_match
      {σ} (s : Stm Γ σ) (pat : Pattern σ)
      (rhs : forall (pc : PatternCase pat), Stm (Γ ▻▻ PatternCaseCtx pc) τ) :
      ⟨ γ , μ , δ , stm_pattern_match s pat rhs ⟩ --->
      ⟨ γ , μ , δ , stm_bind s (fun v => let (pc,δpc) := pattern_match_val pat v
                                         in stm_block δpc (rhs pc))
      ⟩

  where "⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩" :=
    (@Step _ _ γ1%env μ1%env δ1%env γ2%env μ2%env δ2%env s1%exp s2%exp).

  (* Implement small inversions for the operational semantics. This considers
     only the cases where the starting statement is constructed with exactly one
     level of constructors and all the other indices of the relation are
     variables. For details see the relevant literature:

     - Jean-François Monin (2022), "Small inversions for smaller inversions."
       TYPES'22.
       https://types22.inria.fr/files/2022/06/TYPES_2022_paper_25.pdf
       https://types22.inria.fr/files/2022/06/TYPES_2022_slides_25.pdf
     - Dominique Larchey-Wendling & Jean-François Monin (2022), "The Braga
       Method: Extracting Certified Algorithms from Complex Recursive Schemes
       in Coq." In "PROOF AND COMPUTATION II: From Proof Theory and Univalent
       Mathematics to Program Extraction and Verification" (pp. 305-386).
       https://doi.org/10.1142/9789811236488_0008
     - Jean-François Monin & Xiaomu Shi (2013), "Handcrafted Inversions Made
       Operational on Operational Semantics." ITP'13
       https://doi.org/10.1007/978-3-642-39634-2_25
   *)
  Section SmallInversions.
    Section WithParamaters.
      Context {Γ : PCtx} {τ : Ty} {γ : RegStore} {μ : Memory} {δ : CStore Γ}.

      Variant StVal {v : Val τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_val τ v ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=.
      Variant StExp {e : Exp Γ τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_exp e ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_exp : StExp (st_exp γ μ δ e).
      Variant StLet {x σ} {s : Stm Γ σ} {k : Stm (Γ ▻ x∷σ) τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_let x σ s k ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_let : StLet (st_let γ μ δ s k).
      Variant StBlock {Δ} {δΔ : CStore Δ} :
        forall {s : Stm (Γ ▻▻ Δ) τ} [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_block δΔ s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        | stc_block_value' v : StBlock (st_block_value γ μ δ δΔ v)
        | stc_block_fail' s : StBlock (st_block_fail γ μ δ δΔ s)
        | stc_block_step' k γ' μ' δ' δΔ' k'
            (H : ⟨ γ , μ , δ ►► δΔ , k ⟩ ---> ⟨ γ', μ' , δ' ►► δΔ' , k' ⟩) :
          StBlock (st_block_step _ _ _ _ H).
      Variant StSeq {σ} {s : Stm Γ σ} {k : Stm Γ τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_seq s k ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_seq : StSeq (st_seq γ μ δ s k).
      Variant StCall {Δ} {f : 𝑭 Δ τ} {es : NamedEnv (Exp Γ) Δ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_call f es ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_call : StCall (st_call γ μ δ f es).
      Variant StCallFrame {Δ} {δΔ : CStore Δ} :
        forall {s : Stm Δ τ} [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_call_frame δΔ s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        | stc_call_frame_value v : StCallFrame (st_call_frame_value γ μ δ v)
        | stc_call_frame_fail s : StCallFrame (st_call_frame_fail γ μ δ s)
        | stc_call_frame_step s γ' μ' δΔ' s'
            (H : ⟨ γ , μ , δΔ , s ⟩ ---> ⟨ γ' , μ' , δΔ' , s' ⟩) :
          StCallFrame (st_call_frame_step _ H).
      Variant StForeign {Δ} {f : 𝑭𝑿 Δ τ} {es : NamedEnv (Exp Γ) Δ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_foreign f es ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_foreign res γ' μ' (H : ForeignCall f (evals es δ) res γ γ' μ μ') :
          StForeign (st_foreign δ es H).
      Variant StLemmak {Δ} {l : 𝑳 Δ} {es : NamedEnv (Exp Γ) Δ} {k : Stm Γ τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_lemmak l es k ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_lemmak : StLemmak (st_lemmak γ μ δ es k).
      Variant StAssign {x} {xInΓ : x∷τ ∈ Γ}:
        forall {s} [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_assign x s ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        | stc_assign_value v : StAssign (st_assign_value γ μ δ v)
        | stc_assign_fail s : StAssign (st_assign_fail γ μ δ s)
        | stc_assign_step {s : Stm Γ τ} γ' μ' δ' s'
            (H : ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ' , μ' , δ' , s' ⟩) :
          StAssign (st_assign_step H).
      Variant StAssertk {e1 e2} {k : Stm Γ τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_assertk e1 e2 k ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_assertk : StAssertk (st_assertk γ μ δ e1 e2 k).
      Variant StReadRegister {r : 𝑹𝑬𝑮 τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_read_register r ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_read_register : StReadRegister (st_read_register γ μ δ r).
      Variant StWriteRegister {r : 𝑹𝑬𝑮 τ} {e : Exp Γ τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_write_register r e ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_write_register : StWriteRegister (st_write_register γ μ δ r e).
      Variant StBind {σ} {k : Val σ -> Stm Γ τ} :
        forall {s} [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_bind s k ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        | stc_bind_value v : StBind (st_bind_value γ μ δ σ v k)
        | stc_bind_fail s : StBind (st_bind_fail γ μ δ σ s k)
        | stc_bind_step s γ' μ' δ' s'
            (H : ⟨ γ , μ , δ , s ⟩ ---> ⟨ γ', μ' , δ' , s' ⟩) :
          StBind (st_bind_step k H).
      Variant StDebugk {k : Stm Γ τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_debugk k ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_debugk : StDebugk (st_debugk γ μ δ k).
      Variant StPatternMatch {σ} {s : Stm Γ σ} {pat : Pattern σ}
        {rhs : forall (pc : PatternCase pat), Stm (Γ ▻▻ PatternCaseCtx pc) τ} :
        forall [γ2 μ2 δ2 s2],
          ⟨ γ, μ, δ, stm_pattern_match s pat rhs ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
        stc_match : StPatternMatch (st_pattern_match γ μ δ s pat rhs).
    End WithParamaters.

    Definition smallinvdispatch {Γ τ γ μ δ} (s1 : Stm Γ τ) :
      forall γ2 μ2 δ2 s2, ⟨ γ, μ, δ, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> Prop :=
       match s1 with
       | stm_val _ _             => StVal
       | stm_exp _               => StExp
       | stm_let _ _ _ _         => StLet
       | stm_block _ s           => StBlock
       | stm_assign _ s          => StAssign
       | stm_call _ _            => StCall
       | stm_call_frame _ s      => StCallFrame
       | stm_foreign _ _         => StForeign
       | stm_lemmak _ _ _        => StLemmak
       | stm_seq _ _             => StSeq
       | stm_assertk _ _ _       => StAssertk
       | stm_fail _ _            => fun _ _ _ _ _ => False
       | stm_pattern_match _ _ _ => StPatternMatch
       | stm_read_register _     => StReadRegister
       | stm_write_register _ _  => StWriteRegister
       | stm_bind s k            => StBind
       | stm_debugk _            => StDebugk
       end.

    Definition smallinvstep {Γ τ γ1 γ2 μ1 μ2 δ1 δ2} {s1 s2 : Stm Γ τ}
      (st : ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩) : smallinvdispatch st.
    Proof. destruct st; now constructor. Qed.

  End SmallInversions.

  Inductive Steps {Γ : PCtx} {σ : Ty} (γ1 : RegStore) (μ1 : Memory) (δ1 : CStore Γ) (s1 : Stm Γ σ) : RegStore -> Memory -> CStore Γ -> Stm Γ σ -> Prop :=
  | step_refl : Steps γ1 μ1 δ1 s1 γ1 μ1 δ1 s1
  | step_trans {γ2 γ3 : RegStore} {μ2 μ3 : Memory} {δ2 δ3 : CStore Γ} {s2 s3 : Stm Γ σ} :
      Step γ1 μ1 δ1 γ2 μ2 δ2 s1 s2 -> Steps γ2 μ2 δ2 s2 γ3 μ3 δ3 s3 -> Steps γ1 μ1 δ1 s1 γ3 μ3 δ3 s3.

  Module Import SmallStepNotations.
    Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩" := (@Step _ _ γ1%env μ1%env δ1%env γ2%env μ2%env δ2%env s1%exp s2%exp).
    Notation "⟨ γ1 , μ1 , δ1 , s1 ⟩ --->* ⟨ γ2 , μ2 , δ2 , s2 ⟩" := (@Steps _ _ γ1 μ1 δ1 s1 γ2 μ2 δ2 s2).
  End SmallStepNotations.

  Lemma Steps_trans {Γ τ} :
    forall {γ1 γ2 γ3 μ1 μ2 μ3 δ1 δ2 δ3} {s1 s2 s3 : Stm Γ τ},
      ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, s2 ⟩ ->
      ⟨ γ2, μ2, δ2, s2 ⟩ --->* ⟨ γ3, μ3, δ3, s3 ⟩ ->
      ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ3, μ3, δ3, s3 ⟩.
  Proof.
    intros γ1 γ2 γ3 μ1 μ2 μ3 δ1 δ2 δ3 s1 s2 s3 Hs1s2 Hs2s3.
    induction Hs1s2; eauto using step_trans.
  Qed.

  Lemma Steps_bind {Γ σ τ} :
    forall {γ1 γ2 μ1 μ2 δ1 δ2} {s1 s2 : Stm Γ σ} {k : Val σ -> Stm Γ τ},
      ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, s2 ⟩ ->
      ⟨ γ1, μ1, δ1, stm_bind s1 k ⟩ --->* ⟨ γ2, μ2, δ2, stm_bind s2 k ⟩.
  Proof.
    intros γ1 γ2 μ1 μ2 δ1 δ2 s1 s2 k H.
    induction H; first apply step_refl.
    eapply step_trans; last apply IHSteps. constructor. auto.
  Qed.

  Lemma Steps_block {Γ τ} :
    forall {γ1 γ2 μ1 μ2 δ1 δ2 Δ δΔ1 δΔ2} {s1 s2 : Stm (Γ ▻▻ Δ) τ},
      ⟨ γ1, μ1, δ1 ►► δΔ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2 ►► δΔ2, s2 ⟩ ->
      ⟨ γ1, μ1, δ1, stm_block δΔ1 s1 ⟩ --->* ⟨ γ2, μ2, δ2, stm_block δΔ2 s2 ⟩.
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? H.
    remember (δ1 ►► δΔ1) as δ1' eqn:Eδ1'.
    remember (δ2 ►► δΔ2) as δ2' eqn:Eδ2'.
    revert δ1 δΔ1 Eδ1' δ2 Eδ2'.
    induction H;
      intros δ1' δΔ1 Eδ1' δ2' Eδ2'.
    - rewrite Eδ1' in Eδ2'.
      destruct (proj1 (env.inversion_eq_cat _ _ _ _) Eδ2') as (-> & ->).
      apply step_refl.
    - destruct (env.catView δ2). rewrite Eδ1' in H.
      eapply step_trans. apply st_block_step.
      apply H. apply IHSteps; auto.
  Qed.

  Lemma Steps_assign {Γ τ} :
    forall {γ1 γ2 μ1 μ2 δ1 δ2} {x : PVar} {xInΓ : x∷τ ∈ Γ} {s1 s2 : Stm Γ τ},
      ⟨ γ1, μ1, δ1, s1 ⟩ --->* ⟨ γ2, μ2, δ2, s2 ⟩ ->
      ⟨ γ1, μ1, δ1,  x <- s1 ⟩ --->* ⟨ γ2, μ2, δ2, x <- s2 ⟩.
  Proof.
    intros γ1 γ2 μ1 μ2 δ1 δ2 x ? s1 s2 H.
    induction H; first apply step_refl.
    eapply step_trans; last apply IHSteps. constructor. auto.
  Qed.

  Lemma Steps_call_frame {Γ τ} :
    forall {Δ} {γ1 γ2 μ1 μ2} {δ : CStore Γ} {δΔ1 δΔ2 : CStore Δ} {s1 s2 : Stm Δ τ},
      ⟨ γ1, μ1, δΔ1, s1 ⟩ --->* ⟨ γ2, μ2, δΔ2, s2 ⟩ ->
      ⟨ γ1, μ1, δ, stm_call_frame δΔ1 s1 ⟩ --->* ⟨ γ2, μ2, δ, stm_call_frame δΔ2 s2 ⟩.
  Proof.
    intros Δ γ1 γ2 μ1 μ2 δ δΔ1 δΔ2 s1 s2 H.
    induction H; first apply step_refl.
    eapply step_trans; last apply IHSteps. constructor. auto.
  Qed.

  (* Tests if a statement is a final one, i.e. a finished computation. *)
  Ltac microsail_stm_is_final s :=
    lazymatch s with
    | stm_val _ _  => idtac
    | stm_fail _ _ => idtac
    end.

  (* Tests if a statement has a primitive step, i.e. it can be reduced
     by an axiom rule of the step relation instead of a congruence rule. *)
  Ltac microsail_stm_primitive_step s :=
    first
      [ lazymatch s with
        | stm_call_frame _ ?s' => microsail_stm_is_final s'
        | stm_block _ ?s'      => microsail_stm_is_final s'
        | stm_assign _ ?s'     => microsail_stm_is_final s'
        | stm_bind ?s' _       => microsail_stm_is_final s'
        end
      | lazymatch head s with
        | @stm_val              => idtac
        | @stm_exp              => idtac
        | @stm_seq              => idtac
        | @stm_let              => idtac
        | @stm_call             => idtac
        | @stm_foreign          => idtac
        | @stm_lemmak           => idtac
        | @stm_assertk          => idtac
        | @stm_fail             => idtac
        | @stm_pattern_match    => idtac
        | @stm_read_register    => idtac
        | @stm_write_register   => idtac
        | @stm_debugk           => idtac
        end
      ].

  (* This 'Lemma' simply exists for testing that the above predicate on
     statements is complete with respect to the step relation. *)
  Lemma microsail_stm_primitive_step__complete {Γ σ γ1 γ2 μ1 μ2 δ1 δ2} {s1 s2 : Stm Γ σ} :
    ⟨ γ1 , μ1 , δ1 , s1 ⟩ ---> ⟨ γ2 , μ2 , δ2 , s2 ⟩ -> True.
    intro step. remember s1 as s1'.
    dependent elimination step;
      match goal with
      | [ H: ⟨ _,_,_,_ ⟩ ---> ⟨ _,_,_,_ ⟩ |- _ ] =>
        (* If there is a step hypothesis then this case represents a congruence
           rule, not an axiom rule. *)
        constructor
      | [ H: ?s1' = s1 |- _ ] =>
        (* Otherwise, it's an axiom rule and the microsail_stm_primitive_step
           tactic should recognize it. *)
        microsail_stm_primitive_step s1'; constructor
      end; fail.
    Abort.

  Definition Final {Γ σ} (s : Stm Γ σ) : Prop :=
    match s with
    | stm_val _ _   => True
    | stm_fail _ _ => True
    | _ => False
    end.

  Definition ResultOrFail {Γ σ} (s : Stm Γ σ) :
    forall (POST : Val σ -> Prop), Prop :=
    match s with
    | stm_val _ v => fun POST => POST v
    | stm_fail _ _ => fun _ => True
    | _ => fun _ => False
    end.

  Lemma result_or_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Val σ -> Prop) :
    ResultOrFail s POST -> (exists msg, s = stm_fail _ msg)
                        \/ (exists v, s = stm_val _ v /\ POST v).
  Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

  Lemma result_or_fail_mono {Γ σ} {s : Stm Γ σ} {P Q : Val σ -> Prop}:
    (forall v, P v -> Q v) ->
    ResultOrFail s P -> ResultOrFail s Q.
  Proof.
    intros HPQ HsP.
    destruct (result_or_fail_inversion _ _ HsP) as [[msg ->]|[v [-> *]]]; cbn; auto.
  Qed.

  (* This predicate encodes that the statement s is a finished computation and
     that the result is not a failure. This is a computational version that is
     better suited for the goal and the inversion below is better suited for
     a hypothesis. *)
  Definition ResultNoFail {Γ σ} (s : Stm Γ σ) :
    forall (POST : Val σ -> Prop), Prop :=
    match s with
    | stm_val _ v => fun POST => POST v
    | _ => fun _ => False
    end.

  Lemma result_no_fail_inversion {Γ σ} (s : Stm Γ σ) (POST : Val σ -> Prop) :
    ResultNoFail s POST -> exists v, s = stm_val _ v /\ POST v.
  Proof. destruct s; cbn in *; try contradiction; eauto. Qed.

End SmallStepOn.
