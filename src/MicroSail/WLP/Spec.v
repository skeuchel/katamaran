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
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     ZArith.ZArith.

From MicroSail Require Import
     SmallStep.Step
     Syntax.

Set Implicit Arguments.

Import CtxNotations.

Module WLP
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import contkit : ContractKit termkit progkit).

  Definition Cont (R A : Type) : Type := (A -> R) -> R.

  Definition DST (A : Type) : Type := Cont Prop A.
  Definition evalDST {A} (m : DST A) :
    Cont Prop A :=
    fun k => m (fun a => k a).

  Definition lift {A} (m : Cont Prop A) : DST A := m.
  Definition pure {A} (a : A) : DST A := fun k => k a.
  Definition ap {A B} (mf : DST (A -> B)) (ma : DST A) : DST B :=
    fun k => mf (fun f => ma (fun a => k (f a))).
  Definition abort {A} : DST A :=
    fun k => False.
  Definition assert (b : bool) : DST bool :=
    fun k => Bool.Is_true b /\ k b.
  Definition bind {A B} (ma : DST A) (f : A -> DST B) : DST B :=
    fun k => ma (fun a => f a k).
  Definition bindright {A B} (ma : DST A) (mb : DST B) : DST B :=
    bind ma (fun _ => mb).
  Definition bindleft {A B} (ma : DST A) (mb : DST B) : DST A :=
    bind ma (fun a => bind mb (fun _ => pure a)).
  Definition ifthenelse {A} (b : bool) (t e : DST A) : DST A :=
    fun k => (b = true -> t k) /\ (b = false -> e k).


  Arguments abort {_} / _.
  Arguments assert _ / _.
  Arguments bind {_ _} _ _ / _.
  Arguments bindleft {_ _} _ _ / _.
  Arguments bindright {_ _} _ _ / _.
  Arguments evalDST {_} _ / _.
  Arguments lift {_} _ / _.
  Arguments pure {_} _ / _.
  Arguments ifthenelse {_} _ _ _ / _.

  Notation "ma >>= f" := (bind ma f) (at level 50, left associativity).
  Notation "ma *> mb" := (bindright ma mb) (at level 50, left associativity).
  Notation "ma <* mb" := (bindleft ma mb) (at level 50, left associativity).

  Fixpoint WLP {τ} (s : Stm τ) : DST τ :=
    match s in Stm τ return (DST τ) with
    | stm_lit l => pure l
    | stm_assert b _  => assert b
    | stm_if b s1 s2 => ifthenelse b (WLP s1) (WLP s2)
    | stm_exit _ _  => abort

    | stm_app f δ =>
      match CEnv f with
      | ContractNone _ _ => abort (* NOT IMPLEMENTED *)
      | ContractWP _ _ pre post => abort (* NOT IMPLEMENTED *)
      | ContractWLP _ _ pre post => fun POST =>
                    apply pre δ
                    /\ (forall v, apply post δ v -> POST v)
      end
    | stm_bind s k =>
      WLP s >>= fun v POST => blast v (fun w => WLP (k w) POST)
    end.

End WLP.
