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


From Stdlib Require Import
     Lists.List
     ZArith.BinInt.
From Katamaran Require Import
     Prelude
     Signature
     Verifier
     Hoare.
From Katamaran Require Export
     MicroSail.ShallowExecutor.

Import ctx.notations.
Import env.notations.

Set Implicit Arguments.

Module Type ShallowVCGenOn
  (Import B : Base)
  (Import SIG : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG)
  (Import V : Verifier B SIG)
  (Import EXEC : ShallowExecOn B SIG PROG PLOG).

  Definition vcgen {SPEC : Specification} (inline_fuel : nat) {Δ τ} (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
    CHeapSpec.run (exec_contract (M := CHeapSpec) (cexec inline_fuel) c body).

  Module Shallow.

    Definition ValidContractWithFuel {SPEC : Specification} {Δ τ} (fuel : nat)
      (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
      vcgen fuel c body.

    Definition ValidContract {SPEC : Specification} {Δ τ} (c : SepContract Δ τ)
      (body : Stm Δ τ) : Prop :=
      (* Use inline_fuel = 1 by default. *)
      ValidContractWithFuel 1 c body.

    Module Statistics.

      Ltac calc fnc :=
        let P := eval compute - [FALSE TRUE FINISH
                                 negb Z.mul Z.opp Z.compare Z.add Z.geb Z.eqb
                                 Z.leb Z.gtb Z.ltb Z.le Z.lt Z.gt Z.ge Z.of_nat
                                 List.app List.length rev rev_append
            ] in
                   (match CEnv fnc with
                    | Some c => Shallow.ValidContract c (FunDef fnc)
                    | None => False
                    end) in
        let s := eval compute in (CStatistics.stats P) in s.

    End Statistics.

  End Shallow.

End ShallowVCGenOn.

Module Type ShallowVCGen (B : Base) (SIG : Signature B) (PROG : Program B)
  (PLOG : ProgramLogic B SIG PROG) (V : Verifier B SIG) :=
  ShallowExecOn B SIG PROG PLOG <+ ShallowVCGenOn B SIG PROG PLOG V.

Module MakeShallowExecutor
  (Import B    : Base)
  (Import SIG  : Signature B)
  (Import PROG : Program B)
  (Import PLOG : ProgramLogic B SIG PROG)
  (Import V    : Verifier B SIG).

  Include ShallowVCGen B SIG PROG PLOG V.

End MakeShallowExecutor.
