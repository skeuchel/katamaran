(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
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

From stdpp Require Import base finite list.
From Katamaran Require Export
     Syntax.FunDecl
     Syntax.FunDef
     Syntax.Statements
     Base.

Module Type FunDeclMixin (GLOBAL : GlobalState) :=
  StatementsOn GLOBAL.

Module Type ProgramMixin (Import GLOBAL : GlobalState)
  (Import FDecl : FunDecl GLOBAL)
  (Import FDK : FunDefKit GLOBAL FDecl).

  (* We use callgraphs of Sail programs to define a very coarse termination
     metric on functions, e.g. all non-recursive functions or said differently
     all functions not on a loop in the call graph are terminating. This is used
     for reasoning about programs with the total weakest preconditions.

     The call graph however represents terminating and non-terminating
     functions. Terminating functions are then singled out using an
     accessibility predicate. *)
  Module Import callgraph.

    (* Each function is a node in the call graph. Note that functions
       parameterized at the meta-level are different nodes, i.e. one node
       for each possible instantiation of the meta-parameters. Call graphs
       are representation using an association lists per node.

       To instantiate the [Program] module the user has to provide a standalone
       definition of a call graph, i.e. that is a priori not linked to the
       function definitions. We then also ask the user to provide a proof
       that the two are consistent (well-formed). This setup ensures that we
       can support all of the source language features, including [stm_bind], in
       case we ever need it.

       The user provided call graph is not enforced to be precise, i.e. the
       adjacency list for a node may contain more functions than are called in
       reality. This is a sound overapproximation. Or in other words, the
       adjacency list defines an upper bound of functions that may be called. *)
    Record Node : Set := mkNode
      { Δ : PCtx
      ; τ : Ty
      ; f : 𝑭 Δ τ }.
    Arguments mkNode {Δ τ} f.

    #[global] Coercion mkNode : 𝑭 >-> Node.

    Abbreviation Nodes := (list Node).
    Definition CallGraph : Set := Node -> Nodes.

    Instance 𝑭_elem_of : forall {Δ τ}, ElemOf (𝑭 Δ τ) Nodes :=
      fun _ _ => @list_elem_of Node.

    (* We turn the edges in the callgraph into a relation. This says [f1] may
       be called by [f2]. *)
    Definition InvokedBy (g : CallGraph) (f1 f2 : Node) : Prop :=
      f1 ∈ g f2.

    (* Starting from node [f] the [InvokedBy] relation is Noetherian. *)
    Class Accessible (g : CallGraph) (f : Node) : Prop :=
      accessible : Acc (InvokedBy g) f.

    (* We can prove accessibility of a function from the accessibility of all
       of its adacent functions. *)
    Lemma accessible_intro (g : CallGraph) (f : Node) :
      List.Forall (Accessible g) (g f) -> Accessible g f.
    Proof. rewrite Forall_forall. now constructor. Qed.

    Section WithNodes.
      Context (fs : Nodes).

      (* This predicate denotes that a statement respects the upper bound [fs]
         for all of the function calls it contains. *)
      Fixpoint StmWellFormed {Δ τ} (s : Stm Δ τ) : Prop :=
        match s with
        | stm_val _ v => True
        | stm_exp e => True
        | stm_let x σ s1 s2 => StmWellFormed s1 /\ StmWellFormed s2
        | stm_block δ s => StmWellFormed s
        | stm_assign xInΓ s => StmWellFormed s
        | stm_call f2 es => f2 ∈ fs
        | stm_call_frame δ s => StmWellFormed s
        | stm_foreign f es => True
        | stm_lemmak l es k => StmWellFormed k
        | stm_seq s k => StmWellFormed s /\ StmWellFormed k
        | stm_assertk e1 e2 k => StmWellFormed k
        | stm_fail _ s => True
        | stm_pattern_match s pat rhs =>
            StmWellFormed s /\ (forall pc, StmWellFormed (rhs pc))
        | stm_read_register reg => True
        | stm_write_register reg e => True
        | @stm_bind _ _ σ s k => StmWellFormed s /\
                          (forall (v : Val σ), StmWellFormed (k v))
        | stm_debugk k => StmWellFormed k
        end.

    End WithNodes.

    (* This function calculates the list of functions called from a statement.
       This cannot look into [stm_bind], hence we use a dummy value. Duplicates
       are currently not removed, since that would require decidable equality
       of function names [𝑭], which would probably block on some meta-variable
       for polymorphic functions. Instead we allow duplicates, of which there
       are probably very few in practice.

       This function is used to generically calculate a (precise) call graph for
       a bindfree program below. *)
    Fixpoint InvokedByStmList {Γ τ} (s : Stm Γ τ) : Nodes :=
      match s with
      | stm_val _ v => []
      | stm_exp e => []
      | stm_let x σ s1 s2 => InvokedByStmList s1 ++ InvokedByStmList s2
      | stm_block δ s => InvokedByStmList s
      | stm_assign xInΓ s => InvokedByStmList s
      | stm_call f2 es => [mkNode f2]
      | stm_call_frame δ s => InvokedByStmList s
      | stm_foreign f es => []
      | stm_lemmak l es k => InvokedByStmList k
      | stm_seq s k => InvokedByStmList s ++ InvokedByStmList k
      | stm_assertk e1 e2 k => InvokedByStmList k
      | stm_fail _ s => []
      | stm_pattern_match s pat rhs =>
          InvokedByStmList s ++
            List.flat_map
            (fun pc => InvokedByStmList (rhs pc))
            (enum (PatternCase pat))
      | stm_read_register reg => []
      | stm_write_register reg e => []
      | stm_bind s k => [] (* dummy *)
      | stm_debugk k => InvokedByStmList k
      end%list.

    Lemma InvokedByStmList_WellFormed_aux {Γ τ} (s : Stm Γ τ) :
      stm_bindfree s ->
      forall (fs : Nodes),
        InvokedByStmList s ⊆ fs ->
        StmWellFormed fs s.
    Proof.
      rewrite Is_true_true.
      induction s; cbn; rewrite <- ?andb_lazy_alt; intros Hbindfree fs Hsub;
        try discriminate; (* bindfree *)
        repeat
          match goal with
          | H : ?a && ?b = true |- _ =>
              let H1 := fresh "Hbindfree" in
              let H2 := fresh "Hbindfree" in
              apply andb_true_iff in H; destruct H as [H1 H2]
          | H : ?fs1 ++ ?fs2 ⊆ ?fs |- _ =>
              let H1 := fresh "Hsub" in
              let H2 := fresh "Hsub" in
              apply list_subseteq_app_iff_l in H; destruct H as [H1 H2]
          | |- ?f ∈ cons ?f _ => constructor 1
          | H: ?ls ⊆ ?fs |- ?f ∈ ?fs =>
              match ls with
                context[f] => apply H; clear fs H
              end
          | |- _ ∧ _ => split
          end;
        eauto.
      - intros pc. apply H.
        + rewrite forallb_forall in Hbindfree1. apply Hbindfree1.
          apply list_elem_of_In, elem_of_enum.
        + intros h hIn. apply Hsub1, list_elem_of_In, in_flat_map.
          exists pc. split; apply list_elem_of_In; auto.
          apply elem_of_enum.
    Qed.

    (* For bindfree statements, the [InvokedByStmList] function correctly
       calculates an upper bound of the calls appearing in a statement. *)
    Lemma InvokedByStmList_WellFormed {Γ τ} (s : Stm Γ τ) :
      stm_bindfree s -> StmWellFormed (InvokedByStmList s) s.
    Proof. intros; now apply InvokedByStmList_WellFormed_aux. Qed.

    (* Finally, this predicate enforces compatibility of the call graph with
       the function definitions in [funDef], i.e. the call graph correctly
       stipulates upper bounds for each defined function. *)
    Definition CallGraphWellFormed (g : CallGraph) : Prop :=
      forall Δ τ (f : 𝑭 Δ τ),
        StmWellFormed (g f) (FunDef f).

  End callgraph.

  (* A generic definition of a call graph calculation that can be used for
     bind-free programs. *)
  Definition generic_call_graph : CallGraph :=
    fun '(mkNode f) => InvokedByStmList (FunDef f).

  (* For bind-free programs the generic computation is correct. *)
  Lemma generic_call_graph_wellformed
    (H: forall Δ τ (f : 𝑭 Δ τ), stm_bindfree (FunDef f)) :
    CallGraphWellFormed generic_call_graph.
  Proof. intros Δ τ f. now apply InvokedByStmList_WellFormed. Qed.

  Module AccessibleTactics.
    Ltac accessible_proof :=
      apply callgraph.accessible_intro;
      repeat
        (try typeclasses eauto;
         match goal with
         | |- Forall ?P [] => constructor
         | |- Forall ?P (_ :: _) => constructor
         | |- Forall ?P ?xs =>
             (* Do not expand typelevel computations like Nat.mul *)
             let xs' := eval compute - [Nat.mul] in xs in
               change (Forall P xs')
         end).
  End AccessibleTactics.
End ProgramMixin.

Module Type WellFoundedKit (GLOBAL : GlobalState) (Import FDecl : FunDecl GLOBAL)
  (Import FDK : FunDefKit GLOBAL FDecl)
  (Import PM : ProgramMixin GLOBAL FDecl FDK).

  Import callgraph.

  (* The user-provided call graph and the proof of well-formedness w.r.t the
     function definitions. *)
  Parameter 𝑭_call_graph : CallGraph.
  Parameter 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.

  (* The user can single out a subset of the functions to be available for
     total weakest pre reasoning, in which case the user also has to provide
     evidence for termination in form of a coarse accessibility witness
     of the funcition in the call graph. *)
  Parameter 𝑭_accessible :
    forall Δ τ (f : 𝑭 Δ τ),
      option (Accessible 𝑭_call_graph f).

End WellFoundedKit.

Module Type Program (GLOBAL : GlobalState) :=
  FunDeclKit GLOBAL <+ FunDeclMixin GLOBAL <+ FunDefKit GLOBAL <+ ProgramMixin GLOBAL <+ WellFoundedKit GLOBAL.
