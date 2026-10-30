(******************************************************************************)
(* Copyright (c) 2026 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
     MinimalCaps.Machine
     MinimalCaps.Sig
     Sep.Hoare
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.Soundness.

Module MinCapsProgramLogic :=
  MakeProgramLogic MinCapsGlobalState MinCapsSignature MinCapsProgram.

Module MinCapsExecutor :=
  MakeExecutor MinCapsGlobalState MinCapsSignature MinCapsProgram MinCapsProgramLogic.
Module MinCapsShallowExec :=
  MakeShallowExecutor MinCapsGlobalState MinCapsSignature MinCapsProgram MinCapsProgramLogic.

(* Import the soundness proofs for the shallow and symbolic executors. *)
Module MinCapsShallowSoundness :=
  MakeShallowSoundness MinCapsGlobalState MinCapsSignature MinCapsProgram
    MinCapsProgramLogic MinCapsShallowExec.
Module MinCapsSymbolicSoundness :=
  MakeSymbolicSoundness MinCapsGlobalState MinCapsSignature MinCapsProgram
    MinCapsProgramLogic MinCapsShallowExec MinCapsExecutor.
