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
     Strings.String.
From MicroSail Require Import
     Syntax.

Set Implicit Arguments.

Module SmallStep
  (Import termkit : TermKit)
  (Import progKit : ProgramKit termkit).

  Import CtxNotations.

  Inductive Step : forall {σ : Set} (s1 s2 : Stm σ), Prop :=

  | step_stm_app
      {σs σ} {f : 𝑭 σs σ} (es : Env Lit σs) :
      stm_app f es --->
      apply (Pi f) es
  | step_stm_if
      (e : bool) (σ : Set) (s1 s2 : Stm σ) :
      stm_if e s1 s2 ---> if e then s1 else s2
  | step_stm_assert
      (e1 : bool) (e2 : string) :
      stm_assert e1 e2 --->
      if e1 then stm_lit true else stm_exit bool e2

  | step_stm_bind_step
      (σ τ : Set) `{Blastable σ} (s s' : Stm σ) (k : σ -> Stm τ) :
      s ---> s' ->
      stm_bind s k ---> stm_bind s' k
  | step_stm_bind_value
      (σ τ : Set) `{Blastable σ} (v : σ) (k : σ -> Stm τ) :
      stm_bind (stm_lit v) k ---> k v
  | step_stm_bind_exit
      (σ τ : Set)  `{Blastable σ} (s : string) (k : σ -> Stm τ) :
      stm_bind (stm_exit σ s) k ---> stm_exit τ s
  where "s1 '--->' s2" := (Step s1 s2).

  Inductive Steps {σ : Set} (s1 : Stm σ) : Stm σ -> Prop :=
  | step_refl : Steps s1 s1
  | step_trans {s2 s3 : Stm σ} :
      Step s1 s2 -> Steps s2 s3 -> Steps s1 s3.

  Notation "s1 ---> s2" := (Step s1 s2).
  Notation "s1 --->* s2" := (Steps s1 s2).

  (* Definition Triple {Γ τ} *)
  (*   (PRE : Pred (LocalStore Γ)) (s : Stm τ) *)
  (*   (POST : Lit τ -> Pred (LocalStore Γ)) : Prop := *)
  (*   forall (δ δ' : LocalStore Γ) (v : Lit τ), *)
  (*     ⟨ δ , s ⟩ --->* ⟨ δ' , stm_lit τ v ⟩ -> *)
  (*     PRE δ -> *)
  (*     POST v δ'. *)

  (* Definition TripleNoExit {Γ τ} *)
  (*   (PRE : Pred (LocalStore Γ)) (s : Stm τ) *)
  (*   (POST : Lit τ -> Pred (LocalStore Γ)) : Prop := *)
  (*   forall (δ δ' : LocalStore Γ) (s' : Stm τ), *)
  (*     ⟨ δ, s ⟩ --->* ⟨ δ', s' ⟩ -> *)
  (*     Final s' -> *)
  (*     PRE δ -> *)
  (*     IsLit δ' s' POST. *)

End SmallStep.
