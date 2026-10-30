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
     Prelude
     Semantics.

From iris Require Import
     program_logic.adequacy
     program_logic.total_weakestpre
     program_logic.weakestpre
     proofmode.proofmode.

From Katamaran Require Export
     Iris.Resources
     Iris.WeakestPre
     Iris.TotalWeakestPre.

(* TotalPartialWeakestPre adds some lemmas that involve both the twp and wp. *)
Module Type IrisTotalPartialWeakestPre
  (Import GLOBAL : GlobalState)
  (Import PROG   : Program GLOBAL)
  (Import SEM    : Semantics GLOBAL PROG)
  (Import IPre   : IrisPrelims GLOBAL PROG SEM)
  (Import IP     : IrisParameters GLOBAL)
  (Import IR     : IrisResources GLOBAL PROG SEM IPre IP)
  (Import IWP    : IrisWeakestPre GLOBAL PROG SEM IPre IP IR)
  (Import ITWP   : IrisTotalWeakestPre GLOBAL PROG SEM IPre IP IR).

  Section WithSailGS.
    Context `{sG : sailGS Σ}.

    Lemma semTWP_semWP {Γ τ} {s : Stm Γ τ} {δ Q} : 
      semTWP δ s Q ⊢ semWP δ s Q.
    Proof. iApply twp_wp. Qed.
  End WithSailGS.
End IrisTotalPartialWeakestPre.

Module Type IrisBase (GLOBAL : GlobalState) (PROG : Program GLOBAL) (SEM : Semantics GLOBAL PROG) (IPre : IrisPrelims GLOBAL PROG SEM) :=
  IrisParameters GLOBAL <+ IrisResources GLOBAL PROG SEM IPre <+ IrisWeakestPre GLOBAL PROG SEM IPre <+ IrisTotalWeakestPre GLOBAL PROG SEM IPre <+ IrisTotalPartialWeakestPre GLOBAL PROG SEM IPre.
