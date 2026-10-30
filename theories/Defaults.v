(******************************************************************************)
(* Copyright (c) 2026 Steven Keuchel                                          *)
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
     Equations.
From Katamaran Require Import
     Base
     Syntax.Predicates
     Symbolic.Worlds.

(* Default kits for tests. They are kept out of the libraries that the case
   studies load, because functors and modules store full copies of their
   signatures. *)

#[local] Instance DefaultTypeDeclKit : TypeDeclKit :=
  {| enumi := Empty_set;
     unioni := Empty_set;
     recordi := Empty_set;
  |}.

#[local] Instance DefaultTypeDenoteKit : TypeDenoteKit DefaultTypeDeclKit :=
  {| enumt _ := Empty_set;
     uniont _ := Empty_set;
     recordt _ := Empty_set;
  |}.

#[local,refine] Instance DefaultTypeDefKit : TypeDefKit DefaultTypeDenoteKit :=
  {| unionk _            := Empty_set;
     unionk_ty _ _       := ty.unit;
     unionv_fold         := Empty_set_rec _;
     unionv_unfold       := Empty_set_rec _;
     recordf             := Empty_set;
     recordf_ty          := Empty_set_rec _;
     recordv_fold        := Empty_set_rec _;
     recordv_unfold      := Empty_set_rec _;
  |}.
Proof. all: abstract (intros []). Defined.

Module DefaultRegDeclKit (Import T : Types) <: RegDeclKit T.
  Definition 𝑹𝑬𝑮 : Ty -> Set := fun _ => Empty_set.
  #[export] Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT 𝑹𝑬𝑮) := sigma_eqdec _ _.

  Local Obligation Tactic :=
    finite_from_eqdec.

  #[export,program] Instance 𝑹𝑬𝑮_finite : finite.Finite (sigT 𝑹𝑬𝑮) :=
    {| finite.enum := nil |}.

End DefaultRegDeclKit.

Module DefaultPurePredicateKit (Import GLOBAL : GlobalState) <: PurePredicateKit GLOBAL.

  Definition 𝑷 := Empty_set.
  Definition 𝑷_Ty : 𝑷 -> Ctx Ty := fun p => match p with end.
  Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop := match p with end.
  #[export] Instance 𝑷_eq_dec : EqDec 𝑷 := fun p => match p with end.

End DefaultPurePredicateKit.

Module DefaultHeapPredicateKit (Import GLOBAL : GlobalState) <: HeapPredicateKit GLOBAL.

  Definition 𝑯 := Empty_set.
  Definition 𝑯_Ty : 𝑯 -> Ctx Ty := fun p => match p with end.
  #[export] Instance 𝑯_eq_dec : EqDec 𝑯 := fun p => match p with end.
  #[export] Instance 𝑯_is_dup : IsDuplicable 𝑯 := { is_duplicable := fun p => match p with end }.
  Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) := None.

End DefaultHeapPredicateKit.

Module DefaultPredicateKit (GLOBAL : GlobalState) :=
  DefaultPurePredicateKit GLOBAL <+ DefaultHeapPredicateKit GLOBAL.

Module DefaultBase <: Base.

  #[export] Instance typedeclkit : TypeDeclKit := DefaultTypeDeclKit.
  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit := DefaultTypeDenoteKit.
  #[export] Instance typedefkit : TypeDefKit typedenotekit := DefaultTypeDefKit.
  #[export] Instance varkit : VarKit := DefaultVarKit.

  Include BaseMixin.

End DefaultBase.

Module DefaultGlobalState <: GlobalState.
  Module BASE := DefaultBase.
  Include DefaultRegDeclKit BASE.
  Definition Memory : Set := unit.
End DefaultGlobalState.

Module DefaultSolverKit (GLOBAL : GlobalState) (P : PredicateKit GLOBAL)
  (Import W : WorldsMixin GLOBAL P) <: SolverKit GLOBAL P W.

  Definition solver : Solver := solver_null.
  Definition solver_spec : SolverSpec solver := solver_null_spec.

End DefaultSolverKit.
