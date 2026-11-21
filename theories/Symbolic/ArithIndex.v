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

From Stdlib Require Import
     Bool.Bool
     Lists.List
     Logic.FunctionalExtensionality
     MSets.MSetPositive
     PArith.BinPos
     ZArith.BinInt
     Lia.
From Stdlib Require
     micromega.EnvRing
     micromega.RingMicromega
     micromega.Tauto
     micromega.ZMicromega.
From Katamaran Require Import
     Base
     Bitvector
     Prelude
     Syntax.Formulas
     Syntax.Predicates.
From Katamaran Require
     Symbolic.LiaSimplex.

Import ctx.notations.
Import ListNotations.

Local Set Implicit Arguments.

(* An index of the arithmetic formulas of a path condition, reified once for
   LiaSimplex. Int terms that are not arithmetic, and the unsigned values of
   bitvectors, are its atoms. An entry holds normalised hypotheses over atom
   ids. Its meaning is part of the world's, so entries need no invariant. An
   id is a position from the oldest atom, so adding atoms keeps ids. *)
Module Type ArithIndexOn
  (Import B : Base)
  (Import P : PredicateKit B)
  (Import F : FormulasOn B P).

  Import option.notations.

  Section Atoms.
    Context {Σ : LCtx}.

    (* Newest first. *)
    Definition Atoms : Type := list (Term Σ ty.int).

    Fixpoint atom_find (t : Term Σ ty.int) (l : Atoms) : option positive :=
      match l with
      | nil => None
      | cons u l => if Term_eqb t u then Some (Pos.of_succ_nat (length l)) else atom_find t l
      end.

    (* Ids past the table are given by ext. *)
    Fixpoint atom_env (ι : Valuation Σ) (l : Atoms) (ext : positive -> Z) (x : positive) : Z :=
      match l with
      | nil => ext x
      | cons u l =>
          if Pos.eqb x (Pos.of_succ_nat (length l))
          then inst (A := Val ty.int) u ι
          else atom_env ι l ext x
      end.

    Definition term_is_unsigned (t : Term Σ ty.int) : bool :=
      Term_int_case (fun _ => bool)
        (fun _ _ => false) (fun _ => false) (fun _ _ => false) (fun _ _ => false)
        (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun _ _ => false)
        (fun _ _ => true) t.

    (* The state of a reification: the atoms it added, the whole table, the
       ids it met, and facts about the new atoms. *)
    Record RState : Type :=
      MkRState
        { rs_new   : Atoms;
          rs_tbl   : Atoms;
          rs_ids   : PositiveSet.t;
          rs_facts : list (RingMicromega.NFormula Z);
        }.

    (* Unsigned values are nonnegative. No upper bound: the width may be
       symbolic. *)
    Definition nonneg (x : positive) : list (RingMicromega.NFormula Z) :=
      LiaSimplex.ZHyp
        (RingMicromega.Build_Formula (EnvRing.PEc 0%Z) RingMicromega.OpLe (EnvRing.PEX x)).

    Definition intern (t : Term Σ ty.int) (s : RState) : EnvRing.PExpr Z * RState :=
      let '(MkRState new tbl ids facts) := s in
      match atom_find t tbl with
      | Some x => (EnvRing.PEX x, MkRState new tbl (PositiveSet.add x ids) facts)
      | None =>
          let x := Pos.of_succ_nat (length tbl) in
          (EnvRing.PEX x,
            MkRState (cons t new) (cons t tbl) (PositiveSet.add x ids)
              (if term_is_unsigned t then nonneg x ++ facts else facts))
      end.

    Definition reify_int : Term Σ ty.int -> RState -> EnvRing.PExpr Z * RState :=
      Term_int_rect (fun _ => RState -> EnvRing.PExpr Z * RState)
        (fun x xIn => intern (term_var_in xIn))
        (fun i s => (EnvRing.PEc i, s))
        (fun _ _ r1 r2 s => let '(e1, s) := r1 s in
                            let '(e2, s) := r2 s in (EnvRing.PEadd e1 e2, s))
        (fun _ _ r1 r2 s => let '(e1, s) := r1 s in
                            let '(e2, s) := r2 s in (EnvRing.PEsub e1 e2, s))
        (fun _ _ r1 r2 s => let '(e1, s) := r1 s in
                            let '(e2, s) := r2 s in (EnvRing.PEmul e1 e2, s))
        (fun t1 t2 _ _ => intern (term_binop bop.land t1 t2))
        (fun _ r s => let '(e, s) := r s in (EnvRing.PEopp e, s))
        (fun n t => intern (term_unop uop.signed t))
        (fun n t => intern (term_unsigned t)).

    (* A bitvector stands for its unsigned value. *)
    Definition reify_bv {n} (t : Term Σ (ty.bvec n)) (s : RState) : EnvRing.PExpr Z * RState :=
      match term_get_val t with
      | Some v => (EnvRing.PEc (bv.unsigned v), s)
      | None => intern (term_unsigned t) s
      end.

    Definition reify_term {σ} : option (Term Σ σ -> RState -> EnvRing.PExpr Z * RState) :=
      match σ with
      | ty.int => Some reify_int
      | ty.bvec n => Some reify_bv
      | _ => None
      end.

    Definition relop_op {σ} (op : RelOp σ) : option RingMicromega.Op2 :=
      match op with
      | bop.eq => Some RingMicromega.OpEq
      | bop.neq => Some RingMicromega.OpNEq
      | bop.le | bop.bvule => Some RingMicromega.OpLe
      | bop.lt | bop.bvult => Some RingMicromega.OpLt
      | _ => None
      end.

  End Atoms.
  #[global] Arguments Atoms : clear implicits.
  #[global] Arguments RState : clear implicits.

  Section Index.

    (* An entry adds atoms to the table, and hypotheses over the table as it is
       then. Its ids only select relevant entries. *)
    Record Entry (Σ : LCtx) : Type :=
      MkEntry
        { e_atoms : Atoms Σ;
          e_ids   : PositiveSet.t;
          e_nfs   : list (RingMicromega.NFormula Z);
        }.

    (* Newest first. *)
    Definition ArithIndex (Σ : LCtx) : Type := list (Entry Σ).

    Definition ai_empty {Σ} : ArithIndex Σ := nil.

    Fixpoint ai_table {Σ} (idx : ArithIndex Σ) : Atoms Σ :=
      match idx with
      | nil => nil
      | cons e idx => e_atoms e ++ ai_table idx
      end.

    Definition subst_entry {Σ} (e : Entry Σ) {Σ'} (ζ : Sub Σ Σ') : Entry Σ' :=
      MkEntry (List.map (fun t => subst t ζ) (e_atoms e)) (e_ids e) (e_nfs e).

    #[export] Instance subst_arithindex : Subst ArithIndex :=
      fun Σ idx Σ' ζ => List.map (fun e => subst_entry e ζ) idx.

    #[export] Instance substlaws_arithindex : SubstLaws ArithIndex.
    Proof.
      constructor.
      - intros Σ idx. unfold subst, subst_arithindex, subst_entry.
        induction idx as [|[ats ids nfs] idx IH]; cbn; [easy|]. rewrite IH.
        f_equal. f_equal. induction ats; cbn; f_equal; auto. apply subst_sub_id.
      - intros Σ0 Σ1 Σ2 ζ1 ζ2 idx. unfold subst, subst_arithindex, subst_entry.
        induction idx as [|[ats ids nfs] idx IH]; cbn; [easy|]. rewrite IH.
        f_equal. f_equal. rewrite List.map_map.
        apply List.map_ext. intros t. apply (subst_sub_comp (T := fun Σ => Term Σ ty.int)).
    Qed.

    #[export] Instance instprop_arithindex : InstProp ArithIndex :=
      fix holds {Σ} (idx : ArithIndex Σ) (ι : Valuation Σ) : Prop :=
        match idx with
        | nil => True
        | cons e idx' =>
            holds idx' ι /\
            forall ext, List.Forall
                          (ZMicromega.eval_nformula (atom_env ι (ai_table idx) ext))
                          (e_nfs e)
        end.

    Context {Σ : LCtx}.

    (* The table is only computed for arithmetic relations. *)
    Definition reify_relop {σ} (op : RelOp σ) (t1 t2 : Term Σ σ) (idx : ArithIndex Σ) :
      option (RingMicromega.Formula Z * RState Σ) :=
      match relop_op op, reify_term with
      | Some o, Some r =>
          let '(e1, s) := r t1 (MkRState nil (ai_table idx) PositiveSet.empty nil) in
          let '(e2, s) := r t2 s in
          Some (RingMicromega.Build_Formula e1 o e2, s)
      | _, _ => None
      end.

    Definition mk_entry (f : RingMicromega.Formula Z) (s : RState Σ) : Entry Σ :=
      MkEntry (rs_new s) (rs_ids s) (rs_facts s ++ LiaSimplex.ZHyp f).

    (* Index an assumed formula. *)
    Definition ai_assume (F : Formula Σ) (idx : ArithIndex Σ) : ArithIndex Σ :=
      match F with
      | formula_relop op t1 t2 =>
          match reify_relop op t1 t2 idx with
          | Some (f, s) => cons (mk_entry f s) idx
          | None => idx
          end
      | _ => idx
      end.

    Definition ai_assume_pc (C : PathCondition Σ) (idx : ArithIndex Σ) : ArithIndex Σ :=
      ctx.Ctx_rect (fun _ => ArithIndex Σ) idx (fun _ idx F => ai_assume F idx) C.

    Definition ids_meet (s1 s2 : PositiveSet.t) : bool :=
      negb (PositiveSet.is_empty (PositiveSet.inter s1 s2)).

    (* sel and the entries of cands that share atoms with seed, directly or
       through other entries. *)
    Fixpoint relevant (fuel : nat) (seed : PositiveSet.t) (cands sel : ArithIndex Σ) :
      ArithIndex Σ :=
      match fuel with
      | O => sel
      | S fuel =>
          match List.partition (fun e => ids_meet (e_ids e) seed) cands with
          | (nil, _) => sel
          | (hit, miss) =>
              relevant fuel
                (List.fold_left (fun s e => PositiveSet.union (e_ids e) s) hit
                   PositiveSet.empty)
                miss (hit ++ sel)
          end
      end.

    Variant Verdict : Set := entailed | contradicted | unknown.

    (* A verdict on F against idx, and the entry that indexes F. Entailment is
       only looked for if drop is set. *)
    Definition ai_decide (drop : bool) (idx : ArithIndex Σ) (F : Formula Σ) :
      option (Verdict * Entry Σ) :=
      match F with
      | formula_relop op t1 t2 =>
          '(f, s) <- reify_relop op t1 t2 idx ;;
          let sel := relevant (length idx) (rs_ids s) idx nil in
          let nfs := rs_facts s ++ List.concat (List.map (@e_nfs _) sel) in
          let v := if (if drop then LiaSimplex.ZContradicts nfs (LiaSimplex.ZNeg f) else false)
                   then entailed
                   else if LiaSimplex.ZContradicts nfs f then contradicted
                   else unknown in
          Some (v, mk_entry f s)
      | _ => None
      end.

  End Index.
  #[global] Arguments ai_empty {Σ}.

  (* After t is substituted for x, the formulas that mentioned x are indexed
     again, over atoms of the new context. The old entries stay. *)
  Fixpoint ai_reassume {Σ x σ} (xIn : (x∷σ ∈ Σ)%katamaran) (C : PathCondition Σ)
    (C' : PathCondition (Σ - x∷σ)) (idx : ArithIndex (Σ - x∷σ)) : ArithIndex (Σ - x∷σ) :=
    match C, C' with
    | C ▻ F, C' ▻ F' =>
        let idx := ai_reassume xIn C C' idx in
        match occurs_check xIn F with
        | Some _ => idx
        | None => ai_assume F' idx
        end
    | _, _ => idx
    end.

  Section Sound.

    Lemma atom_env_subst {Σ Σ'} (ζ : Sub Σ Σ') (ι : Valuation Σ') l ext x :
      atom_env ι (List.map (fun t => subst t ζ) l) ext x = atom_env (inst ζ ι) l ext x.
    Proof.
      induction l as [|u l IH]; cbn; [easy|].
      rewrite List.length_map, IH. now rewrite inst_subst.
    Qed.

    Lemma ai_table_subst {Σ Σ'} (ζ : Sub Σ Σ') (idx : ArithIndex Σ) :
      ai_table (subst idx ζ) = List.map (fun t => subst t ζ) (ai_table idx).
    Proof.
      induction idx as [|e idx IH]; cbn; [easy|].
      rewrite List.map_app. f_equal. exact IH.
    Qed.

    #[export] Instance instpropsubst_arithindex : InstPropSubst ArithIndex.
    Proof.
      intros Σ Σ' ζ ι idx. induction idx as [|e idx IH]; cbn; [easy|].
      apply Morphisms_Prop.and_iff_morphism; [exact IH|].
      change (map (fun e0 : Entry Σ => subst_entry e0 ζ) idx) with (subst idx ζ).
      rewrite ai_table_subst, <- List.map_app.
      enough (E : forall ext, atom_env ι (List.map (fun t => subst t ζ) (e_atoms e ++ ai_table idx)) ext =
                              atom_env (inst ζ ι) (e_atoms e ++ ai_table idx) ext)
        by (now setoid_rewrite E).
      intros ext. apply functional_extensionality. intros x. apply atom_env_subst.
    Qed.

    Context {Σ : LCtx} (ι : Valuation Σ).

    Definition in_table (l : Atoms Σ) (x : positive) : Prop :=
      (Pos.to_nat x <= length l)%nat.

    Lemma atom_env_out l ext x :
      ~ in_table l x -> atom_env ι l ext x = ext x.
    Proof.
      unfold in_table. induction l as [|u l IH]; cbn; [easy|]. intros Hx.
      destruct (Pos.eqb_spec x (Pos.of_succ_nat (length l))) as [->|_].
      - rewrite SuccNat2Pos.id_succ in Hx. lia.
      - apply IH. lia.
    Qed.

    Lemma atom_env_app pre l ext ext' x :
      in_table l x -> atom_env ι (pre ++ l) ext x = atom_env ι l ext' x.
    Proof.
      unfold in_table. intros Hx. induction pre as [|u pre IH]; cbn.
      - induction l as [|u l IH]; cbn in *; [lia|].
        destruct (Pos.eqb_spec x (Pos.of_succ_nat (length l))) as [|Hne]; [easy|]. apply IH.
        assert (Pos.to_nat x <> S (length l)).
        { intros E. apply Hne. apply Pos2Nat.inj. now rewrite SuccNat2Pos.id_succ. }
        lia.
      - destruct (Pos.eqb_spec x (Pos.of_succ_nat (length (pre ++ l)))) as [->|_]; [|easy].
        rewrite SuccNat2Pos.id_succ, List.length_app in Hx. lia.
    Qed.

    (* An env over a table is one over a shorter table, with the other atoms
       given past it. *)
    Lemma atom_env_layer pre l ext :
      atom_env ι l (atom_env ι (pre ++ l) ext) = atom_env ι (pre ++ l) ext.
    Proof.
      apply functional_extensionality. intros x.
      destruct (Compare_dec.le_dec (Pos.to_nat x) (length l)) as [H|H].
      - symmetry. now apply atom_env_app.
      - now apply atom_env_out.
    Qed.

    Lemma atom_env_new pre t l ext :
      atom_env ι (pre ++ t :: l) ext (Pos.of_succ_nat (length l)) = inst (A := Val ty.int) t ι.
    Proof.
      rewrite (atom_env_app _ _ ext); cbn.
      - now rewrite Pos.eqb_refl.
      - unfold in_table. cbn. rewrite SuccNat2Pos.id_succ. lia.
    Qed.

    Lemma atom_find_spec t l x :
      atom_find t l = Some x ->
      forall pre ext, atom_env ι (pre ++ l) ext x = inst (A := Val ty.int) t ι.
    Proof.
      induction l as [|u l IH]; cbn; [discriminate|].
      destruct (Term_eqb_spec t u) as [->|_].
      - intros [= <-] pre ext. apply atom_env_new.
      - intros Hf pre ext. change (pre ++ u :: l) with (pre ++ (cons u nil) ++ l).
        rewrite List.app_assoc. now apply IH.
    Qed.

    Lemma term_is_unsigned_spec (t : Term Σ ty.int) :
      term_is_unsigned t = true -> (0 <= inst (A := Val ty.int) t ι)%Z.
    Proof.
      destruct t using Term_int_case; cbn; try discriminate.
      intros _. apply bv.unsigned_bounds.
    Qed.

    (* What a reification keeps: the facts hold over any longer table. *)
    Definition rs_ok (s : RState Σ) : Prop :=
      forall pre ext, List.Forall (ZMicromega.eval_nformula (atom_env ι (pre ++ rs_tbl s) ext))
                        (rs_facts s).

    (* The table grows by the new atoms. *)
    Definition grows (s s' : RState Σ) : Prop :=
      exists pre, rs_tbl s' = pre ++ rs_tbl s /\ rs_new s' = pre ++ rs_new s.

    Lemma grows_trans s1 s2 s3 : grows s1 s2 -> grows s2 s3 -> grows s1 s3.
    Proof.
      intros (p1 & E1 & N1) (p2 & E2 & N2). exists (p2 ++ p1).
      rewrite E2, N2, E1, N1. now rewrite <- !List.app_assoc.
    Qed.

    Lemma grows_refl s : grows s s.
    Proof. now exists nil. Qed.

    (* The expression of a reifier evaluates to the term over any table that
       the final one is a suffix of. *)
    Definition reifies {σ} (val : Val σ -> Z) (t : Term Σ σ)
      (r : RState Σ -> EnvRing.PExpr Z * RState Σ) : Prop :=
      forall s, rs_ok s ->
        rs_ok (snd (r s)) /\ grows s (snd (r s)) /\
        (forall pre ext, ZMicromega.Zeval_expr (atom_env ι (pre ++ rs_tbl (snd (r s))) ext)
                           (fst (r s)) = val (inst t ι)).

    Lemma intern_spec t : reifies (σ := ty.int) id t (intern t).
    Proof.
      intros [new tbl ids facts] Hs. unfold intern.
      destruct atom_find as [x|] eqn:Ef; cbn [fst snd rs_tbl rs_new rs_facts].
      - split; [exact Hs|]. split; [now exists nil|].
        intros pre ext. now apply atom_find_spec.
      - split; [|split].
        + intros pre ext. cbn [rs_tbl rs_facts].
          assert (Hf : List.Forall (ZMicromega.eval_nformula
                                      (atom_env ι (pre ++ t :: tbl) ext)) facts).
          { change (pre ++ t :: tbl) with (pre ++ (cons t nil) ++ tbl).
            rewrite List.app_assoc. apply Hs. }
          destruct term_is_unsigned eqn:Eu; [|exact Hf].
          apply List.Forall_app. split; [|exact Hf].
          apply LiaSimplex.ZHyp_sound. cbn.
          rewrite atom_env_new. now apply term_is_unsigned_spec.
        + now exists (cons t nil).
        + intros pre ext. cbn. now rewrite atom_env_new.
    Qed.

    Lemma reifies_bin {σ τ} (val : Val σ -> Z) (val' : Val τ -> Z) op (f : Z -> Z -> Z)
      (t1 t2 : Term Σ σ) r1 r2 (t : Term Σ τ) :
      reifies val t1 r1 -> reifies val t2 r2 ->
      (forall env e1 e2, ZMicromega.Zeval_expr env (op e1 e2) =
                           f (ZMicromega.Zeval_expr env e1) (ZMicromega.Zeval_expr env e2)) ->
      val' (inst t ι) = f (val (inst t1 ι)) (val (inst t2 ι)) ->
      reifies val' t (fun s => let '(e1, s) := r1 s in
                               let '(e2, s) := r2 s in (op e1 e2, s)).
    Proof.
      intros H1 H2 Hop Ht s Hs.
      specialize (H1 s Hs). destruct (r1 s) as [e1 s1]. cbn in H1.
      destruct H1 as (Hs1 & G1 & E1).
      specialize (H2 s1 Hs1). destruct (r2 s1) as [e2 s2]. cbn in H2 |- *.
      destruct H2 as (Hs2 & G2 & E2).
      split; [exact Hs2|]. split; [eapply grows_trans; eassumption|].
      intros pre ext. rewrite Hop, Ht, E2. f_equal.
      destruct G2 as (p & -> & _). rewrite List.app_assoc. apply E1.
    Qed.

    Lemma reifies_un {σ} (val : Val σ -> Z) op (f : Z -> Z) (t1 : Term Σ σ) r1
      (t : Term Σ ty.int) :
      reifies val t1 r1 ->
      (forall env e1, ZMicromega.Zeval_expr env (op e1) = f (ZMicromega.Zeval_expr env e1)) ->
      inst (A := Val ty.int) t ι = f (val (inst t1 ι)) ->
      reifies (σ := ty.int) id t (fun s => let '(e, s) := r1 s in (op e, s)).
    Proof.
      intros H1 Hop Ht s Hs.
      specialize (H1 s Hs). destruct (r1 s) as [e1 s1]. cbn in H1 |- *.
      destruct H1 as (Hs1 & G1 & E1).
      split; [exact Hs1|]. split; [exact G1|].
      intros pre ext. rewrite Hop, E1. symmetry. exact Ht.
    Qed.

    Lemma reify_int_spec (t : Term Σ ty.int) : reifies (σ := ty.int) id t (reify_int t).
    Proof.
      induction t using Term_int_rect; cbn [reify_int Term_int_rect].
      - apply intern_spec.
      - intros s Hs. split; [exact Hs|]. split; [apply grows_refl|]. easy.
      - eapply reifies_bin; [exact IHt1|exact IHt2|reflexivity|reflexivity].
      - eapply reifies_bin; [exact IHt1|exact IHt2|reflexivity|reflexivity].
      - eapply reifies_bin; [exact IHt1|exact IHt2|reflexivity|reflexivity].
      - apply intern_spec.
      - eapply reifies_un; [exact IHt|reflexivity|reflexivity].
      - apply intern_spec.
      - apply intern_spec.
    Qed.

    Lemma reify_bv_spec {n} (t : Term Σ (ty.bvec n)) :
      reifies (σ := ty.bvec n) (@bv.unsigned n) t (reify_bv t).
    Proof.
      unfold reify_bv. destruct (term_get_val_spec t) as [v|]; subst.
      - intros s Hs. split; [exact Hs|]. split; [apply grows_refl|]. easy.
      - apply (intern_spec (term_unsigned t)).
    Qed.

    Lemma reify_pair_spec {σ} (val : Val σ -> Z)
      (r : Term Σ σ -> RState Σ -> EnvRing.PExpr Z * RState Σ) o (t1 t2 : Term Σ σ) s0 f s :
      rs_ok s0 -> reifies val t1 (r t1) -> reifies val t2 (r t2) ->
      (let '(e1, s) := r t1 s0 in
       let '(e2, s) := r t2 s in
       Some (RingMicromega.Build_Formula e1 o e2, s)) = Some (f, s) ->
      rs_ok s /\ grows s0 s /\
      exists e1 e2, f = RingMicromega.Build_Formula e1 o e2 /\
        forall pre ext,
          ZMicromega.Zeval_expr (atom_env ι (pre ++ rs_tbl s) ext) e1 = val (inst t1 ι) /\
          ZMicromega.Zeval_expr (atom_env ι (pre ++ rs_tbl s) ext) e2 = val (inst t2 ι).
    Proof.
      intros Hs0 H1 H2 E.
      specialize (H1 s0 Hs0). destruct (r t1 s0) as [e1 s1]. cbn in H1.
      destruct H1 as (Hs1 & G1 & E1).
      specialize (H2 s1 Hs1). destruct (r t2 s1) as [e2 s2]. cbn in H2.
      destruct H2 as (Hs2 & G2 & E2).
      injection E as <- <-. split; [exact Hs2|]. split; [eapply grows_trans; eassumption|].
      exists e1, e2. split; [reflexivity|]. intros pre ext. split; [|apply E2].
      destruct G2 as (p & -> & _). rewrite List.app_assoc. apply E1.
    Qed.

    Lemma reify_relop_spec {σ} (op : RelOp σ) (t1 t2 : Term Σ σ) idx f s :
      reify_relop op t1 t2 idx = Some (f, s) ->
      rs_ok s /\ rs_tbl s = rs_new s ++ ai_table idx /\
      forall pre ext,
        instprop (formula_relop op t1 t2) ι <->
        ZMicromega.Zeval_formula (atom_env ι (pre ++ rs_tbl s) ext) Tauto.isProp f.
    Proof.
      assert (Hs0 : rs_ok (MkRState nil (ai_table idx) PositiveSet.empty nil))
        by (intros pre ext; constructor).
      unfold reify_relop.
      destruct op; cbn [relop_op]; try discriminate.
      all: try (destruct σ; cbn [reify_term]; try discriminate).
      all: cbn [reify_term]; intros E.
      all: first
             [ destruct (@reify_pair_spec ty.int id reify_int _ t1 t2 _ f s Hs0
                           (reify_int_spec t1) (reify_int_spec t2) E)
                 as (Hs & (pre0 & Et & En) & e1 & e2 & -> & He)
             | match goal with
               | n : nat |- _ =>
                   destruct (@reify_pair_spec (ty.bvec n) (@bv.unsigned n) (@reify_bv Σ n)
                               _ t1 t2 _ f s Hs0 (reify_bv_spec t1) (reify_bv_spec t2) E)
                     as (Hs & (pre0 & Et & En) & e1 & e2 & -> & He)
               end ].
      all: cbn in Et, En; rewrite List.app_nil_r in En; subst pre0.
      all: split; [exact Hs|]; split; [exact Et|].
      all: intros pre ext; destruct (He pre ext) as [H1 H2]; unfold ZMicromega.Zeval_formula;
           cbn [RingMicromega.Flhs RingMicromega.Fop RingMicromega.Frhs]; rewrite H1, H2; cbn.
      all: try reflexivity.
      - split; [now intros ->|apply bv.unsigned_inj].
      - split; intros Hn Heq; apply Hn; [now apply bv.unsigned_inj|now f_equal].
      - apply bv.ule_iff_unsigned_le.
      - apply bv.ult_iff_unsigned_lt.
    Qed.

    (* All entries of an index hold over any longer table. *)
    Lemma ai_holds_in (idx : ArithIndex Σ) :
      instprop idx ι ->
      forall e pre ext, List.In e idx ->
        List.Forall (ZMicromega.eval_nformula (atom_env ι (pre ++ ai_table idx) ext)) (e_nfs e).
    Proof.
      induction idx as [|e' idx IH]; cbn; [easy|]. intros [Hidx He'] e pre ext [<-|Hin].
      - specialize (He' (atom_env ι (pre ++ e_atoms e' ++ ai_table idx) ext)).
        now rewrite atom_env_layer in He'.
      - rewrite List.app_assoc. now apply IH.
    Qed.

    Lemma mk_entry_spec {σ} (op : RelOp σ) t1 t2 (idx : ArithIndex Σ) f s :
      reify_relop op t1 t2 idx = Some (f, s) ->
      instprop (formula_relop op t1 t2) ι -> instprop idx ι ->
      instprop (cons (mk_entry f s) idx) ι.
    Proof.
      intros (Hs & Et & HF)%reify_relop_spec HFt Hidx. split; [exact Hidx|].
      intros ext. cbn. rewrite <- Et.
      apply List.Forall_app. split; [apply (Hs nil)|].
      apply LiaSimplex.ZHyp_sound, (HF nil), HFt.
    Qed.

    Lemma ai_assume_spec (F : Formula Σ) (idx : ArithIndex Σ) :
      (instprop (ai_assume F idx) ι -> instprop idx ι) /\
      (instprop F ι -> instprop idx ι -> instprop (ai_assume F idx) ι).
    Proof.
      unfold ai_assume. destruct F; try easy.
      destruct reify_relop as [[f s]|] eqn:E; [|easy].
      split; [now intros []|]. now apply mk_entry_spec.
    Qed.

    Lemma ai_assume_pc_spec (C : PathCondition Σ) (idx : ArithIndex Σ) :
      (instprop (ai_assume_pc C idx) ι -> instprop idx ι) /\
      (instprop C ι -> instprop idx ι -> instprop (ai_assume_pc C idx) ι).
    Proof.
      induction C as [|C IH F]; cbn; [easy|].
      destruct IH as [IH1 IH2]. destruct (ai_assume_spec F (ai_assume_pc C idx)) as [H1 H2].
      split; [intuition|]. intros [HC HF] Hidx. now apply H2, IH2.
    Qed.

    Lemma relevant_spec (P : Entry Σ -> Prop) fuel :
      forall seed cands sel,
        List.Forall P cands -> List.Forall P sel ->
        List.Forall P (relevant fuel seed cands sel).
    Proof.
      induction fuel as [|fuel IH]; cbn; intros seed cands sel Hc Hs; [assumption|].
      destruct List.partition as [hit miss] eqn:E.
      pose proof (List.elements_in_partition _ _ E) as Hin.
      destruct hit as [|h hit]; [assumption|].
      apply IH.
      - apply List.Forall_forall. intros x Hx.
        eapply List.Forall_forall; [exact Hc|]. apply Hin. now right.
      - apply List.Forall_app. split; [|assumption].
        apply List.Forall_forall. intros x Hx.
        eapply List.Forall_forall; [exact Hc|]. apply Hin. now left.
    Qed.

    Lemma ai_decide_spec drop (idx : ArithIndex Σ) F :
      instprop idx ι ->
      match ai_decide drop idx F with
      | Some (v, e) =>
          match v with
          | entailed => instprop F ι
          | contradicted => ~ instprop F ι
          | unknown => True
          end /\
          (instprop F ι -> instprop (cons e idx) ι)
      | None => True
      end.
    Proof.
      intros Hidx. unfold ai_decide. destruct F; try exact I.
      destruct reify_relop as [[f s]|] eqn:E; cbn; [|exact I].
      split; [|intros HFt; now apply (mk_entry_spec _ _ _ _ E)].
      destruct (reify_relop_spec _ _ _ _ E) as (Hs & Et & HF).
      set (sel := relevant _ _ _ _).
      set (env := atom_env ι (rs_tbl s) (fun _ => 0%Z)).
      assert (Hn : List.Forall (ZMicromega.eval_nformula env)
                     (rs_facts s ++ List.concat (List.map (@e_nfs _) sel))).
      { apply List.Forall_app. split; [apply (Hs nil)|].
        apply List.Forall_concat, List.Forall_map.
        assert (Hsel : List.Forall (fun e => List.In e idx) sel).
        { apply relevant_spec; [now apply List.Forall_forall|constructor]. }
        eapply List.Forall_impl; [|exact Hsel]. intros e He.
        unfold env. rewrite Et. now apply ai_holds_in. }
      specialize (HF nil (fun _ => 0%Z)). fold env in HF.
      destruct (if drop then _ else false) eqn:E1.
      - destruct drop; [|discriminate].
        apply HF, LiaSimplex.ZNeg_complete. intros Hneg.
        exact (LiaSimplex.ZContradicts_sound _ _ E1 _ Hn Hneg).
      - destruct (LiaSimplex.ZContradicts _ f) eqn:E2; [|exact I].
        intros HFt%HF. exact (LiaSimplex.ZContradicts_sound _ _ E2 _ Hn HFt).
    Qed.

  End Sound.

  Lemma ai_reassume_spec {Σ x σ} (xIn : (x∷σ ∈ Σ)%katamaran) C C'
    (idx : ArithIndex (Σ - x∷σ)) (ι : Valuation (Σ - x∷σ)) :
    (instprop (ai_reassume xIn C C' idx) ι -> instprop idx ι) /\
    (instprop C' ι -> instprop idx ι -> instprop (ai_reassume xIn C C' idx) ι).
  Proof.
    revert C'. induction C as [|C IH F]; intros C'; [cbn; tauto|].
    destruct C' as [|C' F']; [cbn; tauto|]. cbn.
    destruct (IH C') as [IH1 IH2].
    destruct occurs_check; [tauto|].
    destruct (ai_assume_spec ι F' (ai_reassume xIn C C' idx)) as [H1 H2].
    split; [intuition|]. intros [HC HF] Hidx. now apply H2, IH2.
  Qed.

  #[global] Arguments ai_assume : simpl never.
  #[global] Arguments ai_assume_pc : simpl never.
  #[global] Arguments ai_decide : simpl never.
  #[global] Arguments ai_reassume : simpl never.

End ArithIndexOn.
