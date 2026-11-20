(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
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
  Classes.Morphisms
  Relations.Relation_Definitions.
From Katamaran Require Import
  Prelude.

Import SignatureNotations.

(* Monotonicity proofs use [Proper] and its automation for partial
   applications. The [monotonic] hints decompose the remaining goals: lambdas,
   matches and [::>]. They are kept out of [typeclass_instances]. *)
Create HintDb monotonic.
Ltac solve_monotonic := typeclasses eauto with typeclass_instances monotonic.

Lemma proper_eq_respectful_intro {A B} {MB : relation B} {f : A -> B} :
  (forall a, Proper MB (f a)) -> Proper (eq ==> MB) f.
Proof. intros pf ? ? <-. apply pf. Qed.

Lemma proper_pointwise_intro {A B} {MB : relation B} {f : A -> B} :
  (forall a, Proper MB (f a)) -> Proper (A ::> MB) f.
Proof. intros pf a. apply pf. Qed.
Lemma proper_pointwise_to_eq {A B} {MB : relation B} {f : A -> B} :
  Proper (A ::> MB) f -> Proper (eq ==> MB) f.
Proof. intros pf ? ? <-. apply pf. Qed.

#[export] Hint Extern 1 (Proper (eq ==> _) (fun _ => _)) =>
  class_apply @proper_eq_respectful_intro : monotonic.
#[export] Hint Extern 1 (Proper (_ ::> _) (fun _ => _)) =>
  class_apply @proper_pointwise_intro : monotonic.
(* Lets partial application use instances stated with [::>]. *)
#[export] Hint Resolve proper_pointwise_to_eq | 5 : monotonic.
#[export] Hint Extern 1 (Proper _ (match ?p with existT _ _ => _ end)) =>
  destruct p : monotonic.
#[export] Hint Extern 1 (Proper _ (match ?p with pair _ _ => _ end)) =>
  destruct p : monotonic.
#[export] Hint Extern 1 (Proper _ (match ?p with left _ => _ | right _ => _ end)) =>
  destruct p : monotonic.
