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

From Katamaran Require Import
  Prelude
  Base
  Syntax.Predicates
  Symbolic.Worlds.

Import ctx.notations.

Set Implicit Arguments.

(* Unused, but don't let it bitrot. *)
Module Type UnusedWorldInstance
  (Import GLOBAL : GlobalState)
  (Import P      : PredicateKit GLOBAL)
  (Import W      : WorldsMixin GLOBAL P).

  Import ModalNotations.
  Local Open Scope modal.

  Record WInstance (w : World) : Set :=
    MkWInstance
      { ιassign :> Valuation w;
        ιvalid  : instprop (wco w) ιassign;
      }.

  Program Definition winstance_formula {w} (ι : WInstance w) (fml : Formula w) (p : instprop fml ι) :
    WInstance (wformula w fml) :=
    {| ιassign := ι; |}.
  Next Obligation.
  Proof. intros. cbn. split; auto. apply ιvalid. Qed.

  Program Definition winstance_snoc {w} (ι : WInstance w) {b : LVar ∷ Ty} (v : Val (type b)) :
    WInstance (wsnoc w b) :=
    {| ιassign := env.snoc (ιassign ι) b v; |}.
  Next Obligation.
  Proof.
    intros. unfold wsnoc. cbn [wctx wco].
    rewrite instprop_subst, inst_sub_wk1.
    apply ιvalid.
  Qed.

  Program Definition winstance_subst {w} (ι : WInstance w) {x σ} {xIn : x∷σ ∈ w}
    (t : Term (w - x∷σ) σ) (p : inst t (env.remove (x∷σ) (ιassign ι) xIn) = env.lookup (ιassign ι) xIn) :
    WInstance (wsubst w x t) :=
    @MkWInstance (wsubst w x t) (env.remove _ (ιassign ι) xIn) _.
  Next Obligation.
    intros *. cbn. rewrite instprop_subst, <- inst_sub_shift in *.
    rewrite inst_sub_single_shift; auto using ιvalid.
  Qed.

  Program Definition instacc {w0 w1} (ω01 : w0 ⊒ w1) : WInstance w1 -> WInstance w0 :=
    match ω01 in (_ ⊒ w) return (WInstance w -> WInstance w0) with
    | acc_refl            => fun ι => ι
    | @acc_sub _ w1 ζ ent => fun ι1 => {| ιassign := inst ζ ι1; |}
    end.
  Next Obligation.
  Proof.
    intros. specialize (ent ι1).
    rewrite <- instprop_subst.
    apply ent.
    apply ιvalid.
  Qed.

End UnusedWorldInstance.
