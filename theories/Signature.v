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

From Katamaran Require Export
  Base
  Refinement.Monads
  Shallow.Monads
  Symbolic.Monads
  Symbolic.Propositions
  Symbolic.Solver
  Symbolic.UnifLogic
  Symbolic.Worlds
  Syntax.Assertions
  Syntax.Chunks
  Syntax.Predicates.

Module Type SignatureMixin
  (GLOBAL : GlobalState) (P : PredicateKit GLOBAL) (W : WorldsMixin GLOBAL P) (S : SolverKit GLOBAL P W) :=
  SymPropOn GLOBAL P W <+ UnifLogicOn GLOBAL P W <+ LogSymPropOn GLOBAL P W  <+
  AssertionsOn GLOBAL P W <+
    GenericSolverOn GLOBAL P W S <+ ShallowMonadsOn GLOBAL P W <+
    SymbolicMonadsOn GLOBAL P W S <+
    RefinementMonadsOn GLOBAL P W S.

Module Type Signature (GLOBAL : GlobalState) :=
  PredicateKit GLOBAL <+ WorldsMixin GLOBAL <+ SolverKit GLOBAL <+ SignatureMixin GLOBAL.
