(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
     Strings.String
     ZArith.ZArith.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Program
     Semantics.Registers
     Syntax.BinOps.
From Katamaran Require Export
     MinimalCaps.Base.

From stdpp Require Import finite decidable.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.

(*** Program ***)

Import MinCapsBase.
Module Export MinCapsProgram <: Program MinCapsGlobalState.

Section FunDeclKit.
  Inductive Fun : PCtx -> Ty -> Set :=
  | read_reg           : Fun ["rs" :: ty.enum regname] ty.word
  | read_reg_cap       : Fun ["cs" :: ty.enum regname] ty.cap
  | read_reg_num       : Fun ["rs" :: ty.enum regname] ty.int
  | write_reg          : Fun ["rd" :: ty.enum regname; "w" :: ty.word] ty.unit
  | next_pc            : Fun [] ty.cap
  | update_pc          : Fun [] ty.unit
  | update_pc_perm     : Fun ["c" :: ty.cap] ty.cap
  | is_perm            : Fun ["p" :: ty.perm; "p'" :: ty.perm] ty.bool
  | is_correct_pc      : Fun ["c" :: ty.cap] ty.bool
  | add_pc             : Fun ["offset" :: ty.int] ty.unit
  | within_bounds      : Fun ["c" :: ty.cap] ty.bool
  | read_mem           : Fun ["c" :: ty.cap] ty.memval
  | write_mem          : Fun ["c" :: ty.cap; "v" :: ty.memval] ty.unit
  | is_sub_perm        : Fun ["p" :: ty.perm; "p'" :: ty.perm] ty.bool
  | read_allowed       : Fun ["p" :: ty.perm] ty.bool
  | write_allowed      : Fun ["p" :: ty.perm] ty.bool
  | perm_to_bits       : Fun ["p" :: ty.perm] ty.int
  | perm_from_bits     : Fun ["i" :: ty.int] ty.perm
  | and_perm           : Fun ["p1" :: ty.perm; "p2" :: ty.perm] ty.perm
  | is_within_range    : Fun ["b'" :: ty.addr; "e'" :: ty.addr; "b" :: ty.addr; "e" :: ty.addr] ty.bool
  | abs                : Fun ["i" :: ty.int] ty.int
  | is_not_zero        : Fun ["i" :: ty.int] ty.bool
  | can_incr_cursor    : Fun ["c" :: ty.cap; "imm" :: ty.int] ty.bool
  | exec_cjalr         : Fun ["cd"  :: ty.dst; "cs"  :: ty.src; "imm" :: ty.int] ty.bool
  | exec_jalr_cap      : Fun ["cd"  :: ty.dst; "cs"  :: ty.src] ty.bool
  | exec_cjal          : Fun ["cd"  :: ty.dst; "imm" :: ty.int] ty.bool
  | exec_bne           : Fun ["rs1" :: ty.src; "rs2" :: ty.src; "imm" :: ty.int] ty.bool
  | exec_ld            : Fun ["cd"  :: ty.dst; "cs"  :: ty.src; "imm" :: ty.int] ty.bool
  | exec_sd            : Fun ["rs1" :: ty.src; "rs2" :: ty.src; "imm" :: ty.int] ty.bool
  | exec_addi          : Fun ["rd"  :: ty.dst; "rs"  :: ty.src; "imm" :: ty.int] ty.bool
  | exec_add           : Fun ["rd"  :: ty.dst; "rs1" :: ty.src; "rs2" :: ty.src] ty.bool
  | exec_sub           : Fun ["rd"  :: ty.dst; "rs1" :: ty.src; "rs2" :: ty.src] ty.bool
  | exec_slt           : Fun ["rd"  :: ty.dst; "rs1" :: ty.src; "rs2" :: ty.src] ty.bool
  | exec_slti          : Fun ["rd"  :: ty.dst; "rs"  :: ty.src; "imm" :: ty.int] ty.bool
  | exec_sltu          : Fun ["rd"  :: ty.dst; "rs1" :: ty.src; "rs2" :: ty.src] ty.bool
  | exec_sltiu         : Fun ["rd"  :: ty.dst; "rs"  :: ty.src; "imm" :: ty.int] ty.bool
  | exec_cmove         : Fun ["cd"  :: ty.dst; "cs"  :: ty.src ] ty.bool
  | exec_cincoffset    : Fun ["cd"  :: ty.dst; "cs"  :: ty.src; "rs"  :: ty.src] ty.bool
  | exec_candperm      : Fun ["cd"  :: ty.dst; "cs"  :: ty.src; "rs"  :: ty.src] ty.bool
  | exec_csetbounds    : Fun ["cd"  :: ty.dst; "cs"  :: ty.src; "rs"  :: ty.src] ty.bool
  | exec_csetboundsimm : Fun ["cd"  :: ty.dst; "cs"  :: ty.src; "imm" :: ty.int] ty.bool
  | exec_cgettag       : Fun ["rd"  :: ty.dst; "cs"  :: ty.src] ty.bool
  | exec_cgetperm      : Fun ["rd"  :: ty.dst; "cs"  :: ty.src] ty.bool
  | exec_cgetbase      : Fun ["rd"  :: ty.dst; "cs"  :: ty.src] ty.bool
  | exec_cgetlen       : Fun ["rd"  :: ty.dst; "cs"  :: ty.src] ty.bool
  | exec_cgetaddr      : Fun ["rd"  :: ty.dst; "cs"  :: ty.src] ty.bool
  | exec_fail          : Fun [] ty.bool
  | exec_ret           : Fun [] ty.bool
  | exec_instr         : Fun ["i" :: ty.instr] ty.bool
  | exec               : Fun [] ty.bool
  | step               : Fun [] ty.unit
  | loop               : Fun [] ty.unit
  .

  Inductive FunX : PCtx -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" :: ty.int] ty.memval
  (* write memory *)
  | wM    : FunX ["address" :: ty.int; "new_value" :: ty.memval] ty.unit
  | dI    : FunX ["code" :: ty.int] ty.instr
  .

  Inductive Lem : PCtx -> Set :=
  | open_gprs                  : Lem []
  | close_gprs                 : Lem []
  | safe_move_cursor           : Lem ["c'" :: ty.cap; "c" :: ty.cap]
  | safe_sub_perm              : Lem ["c'" :: ty.cap; "c" :: ty.cap]
  | safe_within_range          : Lem ["c'" :: ty.cap; "c" :: ty.cap]
  | int_safe                   : Lem ["i" :: ty.int]
  | correctPC_subperm_R        : Lem ["c" :: ty.cap]
  | subperm_not_E              : Lem ["p" :: ty.perm; "p'" :: ty.perm]
  | safe_to_execute            : Lem ["c" :: ty.cap]
  .

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.
End FunDeclKit.

Include FunDeclMixin MinCapsGlobalState.

Section FunDefKit.

  Local Coercion stm_exp : Exp >-> Stm.

  Local Notation "'a'"  := (@exp_var _ "a" _ _) : exp_scope.
  Local Notation "'c'"  := (@exp_var _ "c" _ _) : exp_scope.
  Local Notation "'e'"  := (@exp_var _ "e" _ _) : exp_scope.
  Local Notation "'i'"  := (@exp_var _ "i" _ _) : exp_scope.
  Local Notation "'n'"  := (@exp_var _ "n" _ _) : exp_scope.
  Local Notation "'p'"  := (@exp_var _ "p" _ _) : exp_scope.
  Local Notation "'p1'" := (@exp_var _ "p1" _ _) : exp_scope.
  Local Notation "'p2'" := (@exp_var _ "p2" _ _) : exp_scope.
  Local Notation "'q'"  := (@exp_var _ "q" _ _) : exp_scope.
  Local Notation "'r'"  := (@exp_var _ "r" _ _) : exp_scope.
  Local Notation "'w'"  := (@exp_var _ "w" _ _) : exp_scope.
  Local Notation "'x'"  := (@exp_var _ "x" _ _) : exp_scope.
  Local Notation "'immediate'" := (@exp_var _ "immediate" _ _) : exp_scope.
  Local Notation "'offset'" := (@exp_var _ "offset" _ _) : exp_scope.

  Local Notation "'c'"  := "c" : string_scope.
  Local Notation "'e'"  := "e" : string_scope.
  Local Notation "'hv'" := "hv" : string_scope.
  Local Notation "'rv'" := "rv" : string_scope.
  Local Notation "'i'"  := "i" : string_scope.
  Local Notation "'n'"  := "n" : string_scope.
  Local Notation "'p'"  := "p" : string_scope.
  Local Notation "'q'"  := "q" : string_scope.
  Local Notation "'r'"  := "r" : string_scope.
  Local Notation "'w'"  := "w" : string_scope.
  Local Notation "'immediate'" := "immediate" : string_scope.
  Local Notation "'offset'" := "offset" : string_scope.

  Notation "'use' 'lemma' f args" := (stm_lemma f args%env) (at level 10, f at next level) : exp_scope.
  Notation "'use' 'lemma' f" := (stm_lemma f env.nil) (at level 10, f at next level) : exp_scope.

  (* NOTE: need to wrap s around parentheses when using this notation (not a real let binding!) *)
  Notation "'let*:' '[' perm ',' beg ',' en ',' cur ']' ':=' cap 'in' s" :=
    (stm_match_record capability cap
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "cap_permission" perm)
       "cap_begin" beg)
       "cap_end" en)
       "cap_cursor" cur)
    s) (at level 200) : exp_scope.

  Definition lemma_correctPC_not_E {Γ} (cap : Stm Γ ty.cap) : Stm Γ ty.unit :=
    let: "c" := cap in
    use lemma correctPC_subperm_R [exp_var "c"] ;;
    let*: ["perm" , "beg" , "end" , "cur"] := (exp_var "c") in
    (let: "tmp" := exp_val ty.perm R in
     use lemma subperm_not_E [exp_var "tmp"; exp_var "perm"]).

  Definition fun_read_reg : Stm ["rs" :: ty.enum regname] ty.word :=
    use lemma open_gprs ;;
    let: "x" := match: exp_var "rs" in regname with
                | R0 =>
                    use lemma int_safe [exp_val ty.int 0%Z] ;;
                    exp_inl (exp_val ty.int 0%Z)
                | R1 => stm_read_register reg1
                | R2 => stm_read_register reg2
                | R3 => stm_read_register reg3
                end in
    use lemma close_gprs ;;
    stm_exp x.

  Definition fun_read_reg_cap : Stm ["cs" :: ty.enum regname] ty.cap :=
    let: w := call read_reg (exp_var "cs") in
    match: w with
    | inl i => fail "Err [read_reg_cap]: expect register to hold a capability"
    | inr c =>
        let*: ["p", "b", "e", "a"] := exp_var "c" in (* force record *)
        (exp_var "c")
    end.

  Definition fun_read_reg_num : Stm ["rs" :: ty.enum regname ] ty.int :=
    let: w := call read_reg (exp_var "rs") in
    match: w with
    | inl i => stm_exp i
    | inr c => fail "Err [read_reg_num]: expect register to hold a number"
    end.

  Definition fun_write_reg : Stm ["rd" :: ty.enum regname; "w" :: ty.word] ty.unit :=
    use lemma open_gprs ;;
    match: exp_var "rd" in regname with
    | R0 => stm_val ty.unit tt
    | R1 => stm_write_register reg1 (exp_var "w") ;; stm_val ty.unit tt
    | R2 => stm_write_register reg2 (exp_var "w") ;; stm_val ty.unit tt
    | R3 => stm_write_register reg3 (exp_var "w") ;; stm_val ty.unit tt
    end ;;
    use lemma close_gprs.

  Definition fun_next_pc : Stm [] ty.cap :=
    let: "c" := stm_read_register pc in
    let*: ["perm" , "beg" , "end" , "cur"] := (exp_var "c") in
      (exp_record capability
         [ exp_var "perm";
           exp_var "beg";
           exp_var "end";
           exp_var "cur" + exp_int 1 ]).

  Definition fun_update_pc : Stm [] ty.unit :=
    let: "opc" := stm_read_register pc in
    let: "npc" := call next_pc in
    lemma_correctPC_not_E (exp_var "opc") ;;
    use lemma safe_move_cursor [exp_var "npc"; exp_var "opc"] ;;
    stm_write_register pc (exp_var "npc") ;;
    stm_val ty.unit tt.

  Definition fun_update_pc_perm : Stm ["c" :: ty.cap] ty.cap :=
    let*: ["p" , "b" , "e" , "a"] := (exp_var "c") in
    (match: exp_var "p" in permission with
     | E => let: "p" := exp_val ty.perm R in
            use lemma safe_to_execute [exp_var "c"] ;;
            exp_record capability
                       [ exp_var "p" ;
                         exp_var "b" ;
                         exp_var "e" ;
                         exp_var "a" ]
     | _ => exp_var "c"
     end).

  Definition fun_is_correct_pc : Stm ["c" :: ty.cap] ty.bool :=
    let*: ["perm" , "beg" , "end" , "cur"] := (exp_var "c") in
    (let: "tmp1" := call is_perm (exp_var "perm") (exp_val ty.perm R) in
     let: "tmp2" := call is_perm (exp_var "perm") (exp_val ty.perm RW) in
     if: (exp_var "beg" <= exp_var "cur") && (exp_var "cur" < exp_var "end")
          && (exp_var "tmp1" || exp_var "tmp2")
     then stm_val ty.bool true
     else stm_val ty.bool false).

  Definition fun_is_perm : Stm ["p" :: ty.perm; "p'" :: ty.perm] ty.bool :=
    stm_match_enum permission (exp_var "p") (fun _ => stm_val ty.unit tt) ;;
    stm_match_enum permission (exp_var "p'") (fun _ => stm_val ty.unit tt) ;;
    exp_var "p" = exp_var "p'".

  Definition fun_add_pc : Stm ["offset" :: ty.int] ty.unit :=
    let: "opc" := stm_read_register pc in
    let*: ["perm", "beg", "end", "cur"] := (exp_var "opc") in
    (let: "npc" := (exp_record capability
                               [ exp_var "perm";
                                 exp_var "beg";
                                 exp_var "end";
                                 exp_var "cur" + exp_var "offset" ]) in
     lemma_correctPC_not_E (exp_var "opc") ;;
     use lemma safe_move_cursor [exp_var "npc"; exp_var "opc"] ;;
     stm_write_register pc (exp_var "npc") ;;
     stm_val ty.unit tt).

  Definition fun_read_allowed : Stm ["p" :: ty.perm] ty.bool :=
    call is_sub_perm (exp_val (ty.enum permission) R) (exp_var "p").

  Definition fun_write_allowed : Stm ["p" :: ty.perm] ty.bool :=
    call is_sub_perm (exp_val (ty.enum permission) RW) (exp_var "p").

  Definition fun_within_bounds : Stm ["c" :: ty.cap] ty.bool :=
    let*: ["p", "b", "e", "a"] := (exp_var "c") in
    ((exp_var "b" <= exp_var "a") && (exp_var "a" <= exp_var "e")).

  Section ExecStore.

    Local Notation "'perm'"   := "cap_permission" : string_scope.
    Local Notation "'cursor'" := "cap_cursor" : string_scope.

    Let cap : Ty := ty.cap.
    Let bool : Ty := ty.bool.
    Let int : Ty := ty.int.
    Let word : Ty := ty.word.

    Definition fun_exec_sd : Stm ["rs1" :: ty.src; "rs2" :: ty.src; "imm" :: ty.int] ty.bool :=
      let: "base_cap" :: cap  := call read_reg_cap (exp_var "rs1") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (let: "c" :: cap := exp_record capability
                                     [ exp_var "perm";
                                       exp_var "beg";
                                       exp_var "end";
                                       exp_var "cursor" + exp_var "imm"
                                     ] in
       let: p :: bool := call write_allowed (exp_var "perm") in
       stm_assert p (exp_string "Err: [store] no write permission") ;;
       let: w :: ty.word := call read_reg (exp_var "rs2") in
       let: "tmp" := exp_val ty.perm RW in
       use lemma subperm_not_E [exp_var "tmp"; exp_var "perm"] ;;
       use lemma safe_move_cursor [exp_var "c"; exp_var "base_cap"] ;;
       call write_mem c w ;;
       call update_pc ;;
       stm_val ty.bool true).

    Definition fun_exec_ld : Stm ["cd" :: ty.dst; "cs" :: ty.src; "imm" :: ty.int] ty.bool :=
      let: "base_cap" :: cap  := call read_reg_cap (exp_var "cs") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (let: "c" :: cap := exp_record capability
                                     [ exp_var "perm";
                                       exp_var "beg";
                                       exp_var "end";
                                       exp_var "cursor" + exp_var "imm"
                                     ] in
       let: p :: bool := call read_allowed (exp_var "perm") in
       stm_assert p (exp_string "Err: [load] no read permission") ;;                 
       let: "tmp" := exp_val ty.perm R in
       use lemma subperm_not_E [exp_var "tmp"; exp_var "perm"] ;;
       use lemma safe_move_cursor [exp_var "c"; exp_var "base_cap"] ;;
       let: n :: ty.memval := call read_mem c in
       call write_reg (exp_var "cd") n ;;
       call update_pc ;;
       stm_val ty.bool true).

    Definition fun_exec_cincoffset : Stm ["cd" :: ty.dst; "cs" :: ty.src; "rs" :: ty.src] ty.bool :=
      let: "base_cap" :: cap  := call read_reg_cap (exp_var "cs") in
      let: "offset" :: ty.int := call read_reg_num (exp_var "rs") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (match: exp_var "perm" in permission with
       | E => fail "Err: [cincoffset] not permitted on enter capability"
       | _ =>
           let: "c" :: cap := exp_record capability
                                         [ exp_var "perm";
                                           exp_var "beg";
                                           exp_var "end";
                                           exp_var "cursor" + exp_var "offset"
                                         ] in
           use lemma safe_move_cursor [exp_var "c"; exp_var "base_cap"] ;;
           call write_reg (exp_var "cd") (exp_inr (exp_var "c")) ;;
           call update_pc ;;
           stm_val ty.bool true
       end).

    Definition fun_exec_candperm : Stm ["cd" :: ty.dst; "cs" :: ty.src; "rs" :: ty.src] ty.bool :=
      let: "cs_val" := call read_reg_cap (exp_var "cs") in
      let: "rs_val" := call read_reg_num (exp_var "rs") in
      let*: ["p", "b", "e", "a"] := exp_var "cs_val" in
      let: "p'" := call perm_from_bits (exp_var "rs_val") in
      let: "new_p"  := call and_perm (exp_var "p") (exp_var "p'") in
      let: "new_cap" :: cap := exp_record capability
                                          [ exp_var "new_p";
                                            exp_var "b";
                                            exp_var "e";
                                            exp_var "a"
                                          ] in
      use lemma safe_sub_perm [exp_var "new_cap"; exp_var "cs_val"] ;;
      call write_reg (exp_var "cd") (exp_inr (exp_var "new_cap")) ;;
      stm_val ty.bool true.

    Definition fun_exec_addi : Stm ["rd" :: ty.dst; "rs" :: ty.src; "imm" :: ty.int] ty.bool :=
      let: "v" :: ty.int := call read_reg_num (exp_var "rs") in
      let: "res" :: ty.int := stm_exp (exp_var "v" + exp_var "imm") in
      use lemma int_safe [exp_var "res"] ;;
      call write_reg (exp_var "rd") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_add : Stm ["rd" :: ty.dst; "rs1" :: ty.src; "rs2" :: ty.src] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "rs1") in
      let: "v2" :: int := call read_reg_num (exp_var "rs2") in
      let: "res" :: int := stm_exp (exp_var "v1" + exp_var "v2") in
      use lemma int_safe [exp_var "res"] ;;
      call write_reg (exp_var "rd") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_sub : Stm ["rd" :: ty.dst; "rs1" :: ty.src; "rs2" :: ty.src] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "rs1") in
      let: "v2" :: int := call read_reg_num (exp_var "rs2") in
      let: "res" :: int := stm_exp (exp_var "v1" - exp_var "v2") in
      use lemma int_safe [exp_var "res"] ;;
      call write_reg (exp_var "rd") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_abs : Stm ["i" :: ty.int] ty.int :=
      if: exp_var "i" < (exp_val ty.int 0%Z)
      then exp_var "i" * (exp_val ty.int (-1)%Z)
      else exp_var "i".

    Definition fun_is_not_zero : Stm ["i" :: ty.int] ty.bool :=
      if: exp_var "i" = exp_val ty.int 0%Z
      then stm_val ty.bool false
      else stm_val ty.bool true.

    Definition fun_can_incr_cursor : Stm ["c" :: ty.cap; "imm" :: ty.int] ty.bool :=
      let*: ["p", "b", "e", "a"] := exp_var "c" in
      let: "tmp1" := call is_perm (exp_var "p") (exp_val ty.perm E) in
      if: exp_var "tmp1"
      then
        let: "tmp2" := call is_not_zero (exp_var "imm") in
        if: exp_var "tmp2"
        then stm_val ty.bool false
        else
          stm_val ty.bool true
      else stm_val ty.bool true.

    Definition fun_exec_slt : Stm ["rd" :: ty.dst; "rs1" :: ty.src; "rs2" :: ty.src] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "rs1") in
      let: "v2" :: int := call read_reg_num (exp_var "rs2") in
      (if: exp_var "v1" < exp_var "v2"
       then
         use lemma int_safe [exp_val ty.int 1%Z] ;;
         call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 1%Z))
       else
         use lemma int_safe [exp_val ty.int 0%Z] ;;
         call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 0%Z))) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_slti : Stm ["rd" :: ty.dst; "rs" :: ty.src; "imm" :: ty.int] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "rs") in
      let: "v2" :: int := exp_var "imm" in
      (if: exp_var "v1" < exp_var "v2"
       then
         use lemma int_safe [exp_val ty.int 1%Z] ;;
         call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 1%Z))
       else
         use lemma int_safe [exp_val ty.int 0%Z] ;;
         call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 0%Z))) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_sltu : Stm ["rd" :: ty.dst; "rs1" :: ty.src; "rs2" :: ty.src] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "rs1") in
      let: "uv1" :: int := call abs (exp_var "v1") in
      let: "v2" :: int := call read_reg_num (exp_var "rs2") in
      let: "uv2" :: int := call abs (exp_var "v2") in
      (if: exp_var "uv1" < exp_var "uv2"
       then
         use lemma int_safe [exp_val ty.int 1%Z] ;;
         call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 1%Z))
       else
         use lemma int_safe [exp_val ty.int 0%Z] ;;
         call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 0%Z))) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_sltiu : Stm ["rd" :: ty.dst; "rs" :: ty.src; "imm" :: ty.int] ty.bool :=
      let: "v1" :: int := call read_reg_num (exp_var "rs") in
      let: "uv1" :: int := call abs (exp_var "v1") in
      let: "v2" :: int := exp_var "imm" in
      let: "uv2" :: int := call abs (exp_var "v2") in
      (if: exp_var "uv1" < exp_var "uv2"
       then
         use lemma int_safe [exp_val ty.int 1%Z] ;;
         call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 1%Z))
       else
         use lemma int_safe [exp_val ty.int 0%Z] ;;
         call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 0%Z))) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_perm_to_bits : Stm ["p" :: ty.perm] ty.int :=
      match: exp_var "p" in permission with
      | O  => stm_val ty.int 0%Z
      | R  => stm_val ty.int 1%Z
      | RW => stm_val ty.int 2%Z
      | E  => stm_val ty.int 3%Z
      end.

    Definition fun_perm_from_bits : Stm ["i" :: ty.int] ty.perm :=
      if: exp_var "i" = exp_val ty.int 1%Z
      then exp_val ty.perm R
      else if: exp_var "i" = exp_val ty.int 2%Z
           then exp_val ty.perm RW
           else if: exp_var "i" = exp_val ty.int 3%Z
                then exp_val ty.perm E
                else exp_val ty.perm O.

    Definition fun_and_perm : Stm ["p1" :: ty.perm; "p2" :: ty.perm] ty.perm :=
      match: exp_var "p1" in permission with
      | O  => exp_val ty.perm O
      | R  => match: exp_var "p2" in permission with
              | R  => exp_val ty.perm R
              | RW => exp_val ty.perm R
              | _  => exp_val ty.perm O
              end
      | RW => match: exp_var "p2" in permission with
              | R  => exp_val ty.perm R
              | RW => exp_val ty.perm RW
              | _  => exp_val ty.perm O
              end
      | E  => match: exp_var "p2" in permission with
              | E => exp_val ty.perm E
              | _ => exp_val ty.perm O
              end
      end.

    Definition fun_is_sub_perm : Stm ["p" :: ty.perm; "p'" :: ty.perm] ty.bool :=
      match: exp_var "p" in permission with
      | O =>
        stm_val ty.bool true
      | E => match: exp_var "p'" in permission with
             | O => stm_val ty.bool false
             | _ => stm_val ty.bool true
             end
      | R => match: exp_var "p'" in permission with
            | O => stm_val ty.bool false
            | E => stm_val ty.bool false
            | _ =>
              stm_val ty.bool true
            end
      | RW => match: exp_var "p'" in permission with
             | RW =>
               stm_val ty.bool true
            | _ => stm_val ty.bool false
            end
      end.

    Definition fun_is_within_range : Stm ["b'" :: ty.addr; "e'" :: ty.addr;
                                          "b" :: ty.addr; "e" :: ty.addr] ty.bool :=
      (exp_var "b" <= exp_var "b'") && (exp_var "e'" <= exp_var "e").

    Definition fun_exec_csetbounds : Stm ["cd" :: ty.dst; "cs" :: ty.src; "rs" :: ty.src] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "cs") in
      let*: ["p", "b", "e", "a"] := exp_var "c" in
      let: "new_begin" :: ty.int :=  exp_var "a" in
      let: "rs_val" :: ty.int := call read_reg_num (exp_var "rs") in
      let: "new_end" :: ty.int := (exp_var "new_begin") + (exp_var "rs_val") in
      match: exp_var "p" in permission with
       | E => fail "Err: [csetbounds] not permitted on enter capability"
       | _ =>
           let: "b" :: ty.bool :=
             call is_within_range (exp_var "new_begin") (exp_var "new_end")
                                  (exp_var "b")         (exp_var "e") in
           stm_assert (exp_var "b") (exp_string "Err: [csetbounds] tried to increase range of authority") ;;
           let: "c'" :: cap := exp_record capability
                                          [ exp_var "p";
                                            exp_var "new_begin";
                                            exp_var "new_end";
                                            exp_var "a"
                                          ] in
           use lemma safe_within_range [exp_var "c'"; exp_var "c"] ;;
           call write_reg (exp_var "cd") (exp_inr (exp_var "c'")) ;;
           call update_pc ;;
           stm_val ty.bool true
       end.

    Definition fun_exec_csetboundsimm : Stm ["cd" :: ty.dst; "cs" :: ty.src; "imm" :: ty.int] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "cs") in
      let*: ["p", "b", "e", "a"] := exp_var "c" in
      let: "new_begin" :: ty.int :=  exp_var "a" in
      let: "new_end" :: ty.int := (exp_var "new_begin") + (exp_var "imm") in
      match: exp_var "p" in permission with
       | E => fail "Err: [csetboundsimm] not permitted on enter capability"
       | _ =>
           let: "b" :: ty.bool :=
             call is_within_range (exp_var "new_begin") (exp_var "new_end")
                                  (exp_var "b")         (exp_var "e") in
           stm_assert (exp_var "b") (exp_string "Err: [csetboundsimm] tried to increase range of authority") ;;
           let: "c'" :: cap := exp_record capability
                                          [ exp_var "p";
                                            exp_var "new_begin";
                                            exp_var "new_end";
                                            exp_var "a"
                                          ] in
           use lemma safe_within_range [exp_var "c'"; exp_var "c"] ;;
           call write_reg (exp_var "cd") (exp_inr (exp_var "c'")) ;;
           call update_pc ;;
           stm_val ty.bool true
       end.

    Definition fun_exec_cgettag : Stm ["rd" :: ty.dst; "cs" :: ty.src] ty.bool :=
      let: w :: ty.word := call read_reg (exp_var "cs") in
      match: w with
      | inl i =>
        use lemma int_safe [exp_val ty.int 0%Z] ;;
        call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 0%Z))
      | inr c =>
        use lemma int_safe [exp_val ty.int 1%Z] ;;
        call write_reg (exp_var "rd") (exp_inl (exp_val ty.int 1%Z))
      end ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_cgetperm : Stm ["rd" :: ty.dst; "cs" :: ty.src] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "cs") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      let: "i" :: ty.int := call perm_to_bits (exp_var "perm") in
      use lemma int_safe [exp_var "i"] ;;
      call write_reg (exp_var "rd") (exp_inl (exp_var "i")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_cgetbase : Stm ["rd" :: ty.dst; "cs" :: ty.src] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "cs") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      use lemma int_safe [exp_var "beg"] ;;
      call write_reg (exp_var "rd") (exp_inl (exp_var "beg")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_cgetlen : Stm ["rd" :: ty.dst; "cs" :: ty.src] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "cs") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      let: "res" := (exp_var "end") - (exp_var "beg") in
      use lemma int_safe [exp_var "res"] ;;
      call write_reg (exp_var "rd") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_cgetaddr : Stm ["rd" :: ty.dst; "cs" :: ty.src] ty.bool :=
      let: c :: cap := call read_reg_cap (exp_var "cs") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      use lemma int_safe [exp_var "cursor"] ;;
      call write_reg (exp_var "rd") (exp_inl (exp_var "cursor")) ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_fail : Stm [] ty.bool :=
      fail "machine failed".

    Definition fun_exec_ret : Stm [] ty.bool :=
      stm_exp exp_false.

    Definition fun_exec_cmove : Stm ["cd" :: ty.dst; "cs" :: ty.src] ty.bool :=
      let: w :: word := call read_reg (exp_var "cs") in
      call write_reg (exp_var "cd") w ;;
      call update_pc ;;
      stm_val ty.bool true.

    Definition fun_exec_jalr_cap : Stm ["cd" :: ty.dst; "cs" :: ty.src] ty.bool :=
      call exec_cjalr (exp_var "cd") (exp_var "cs") (exp_val ty.int 0%Z).

    Definition fun_exec_cjalr : Stm ["cd" :: ty.dst; "cs" :: ty.src; "imm" :: ty.int] ty.bool :=
      let: "opc" := stm_read_register pc in
      let: "npc" := call next_pc in
      lemma_correctPC_not_E (exp_var "opc") ;;
      use lemma safe_move_cursor [exp_var "npc"; exp_var "opc"] ;;
      call write_reg (exp_var "cd") (exp_inr (exp_var "npc")) ;;
      let: "c" :: ty.cap := call read_reg_cap (exp_var "cs") in
      let*: ["p", "b", "e", "a"] := exp_var "c" in
      let: "tmp" := call can_incr_cursor (exp_var "c") (exp_var "imm") in
      if: exp_not (exp_var "tmp")
      then fail "Err: [cjalr] cannot increment cursor of enter capability"
      else
        let: "c'" := (exp_record capability
                                 [ exp_var "p";
                                   exp_var "b";
                                   exp_var "e";
                                   exp_var "a" + exp_var "imm"]) in
        use lemma safe_move_cursor [exp_var "c'"; exp_var "c"] ;;
        let: "c'" := call update_pc_perm (exp_var "c'") in
        stm_write_register pc (exp_var "c'") ;;
        stm_val ty.bool true.

    Definition fun_exec_cjal : Stm ["cd" :: ty.dst; "imm" :: ty.int] ty.bool :=
      let: "opc" := stm_read_register pc in
      let: "npc" := call next_pc in
      lemma_correctPC_not_E (exp_var "opc") ;;
      use lemma safe_move_cursor [exp_var "npc"; exp_var "opc"] ;;
      call write_reg (exp_var "cd") (exp_inr (exp_var "npc")) ;;
      call add_pc (exp_binop bop.times (exp_var "imm") (exp_int 2)) ;;
      stm_val ty.bool true.

    Definition fun_exec_bne : Stm ["rs1" :: ty.src; "rs2" :: ty.src; "imm" :: ty.int] ty.bool :=
      let: "a" :: ty.int := call read_reg_num (exp_var "rs1") in
      let: "b" :: ty.int := call read_reg_num (exp_var "rs2") in
      stm_if (exp_var "a" = exp_var "b")
             (call update_pc ;; stm_val ty.bool true)
             (call add_pc (exp_var "imm") ;; stm_val ty.bool true).

    Definition fun_exec_instr : Stm [i :: ty.instr] ty.bool :=
      stm_match_union_alt
        instruction (exp_var i)
        (fun K =>
           match K with
           | kjalr_cap      => MkAlt (pat_pair "cd" "cs")
                                     (call exec_jalr_cap (exp_var "cd") (exp_var "cs"))%exp
           | kcjalr         => MkAlt (pat_tuple ("cd" , "cs" , "imm"))
                                     (call exec_cjalr (exp_var "cd") (exp_var "cs") (exp_var "imm"))%exp
           | kcjal          => MkAlt (pat_pair "cd" "imm")
                                     (call exec_cjal (exp_var "cd") (exp_var "imm"))%exp
           | kbne           => MkAlt (pat_tuple ("rs1" , "rs2" , "imm"))
                                     (call exec_bne (exp_var "rs1") (exp_var "rs2") (exp_var "imm"))%exp
           | kcmove         => MkAlt (pat_pair "cd" "cs")
                                     (call exec_cmove (exp_var "cd") (exp_var "cs"))%exp
           | kld            => MkAlt (pat_tuple ("cd" , "cs" , "imm"))
                                     (call exec_ld (exp_var "cd") (exp_var "cs") (exp_var "imm"))%exp
           | ksd            => MkAlt (pat_tuple ("rs1" , "rs2" , "imm"))
                                     (call exec_sd (exp_var "rs1") (exp_var "rs2") (exp_var "imm"))%exp
           | kcincoffset    => MkAlt (pat_tuple ("cd" , "cs" , "rs"))
                                     (call exec_cincoffset (exp_var "cd") (exp_var "cs") (exp_var "rs"))%exp
           | kcandperm      => MkAlt (pat_tuple ("cd" , "cs" , "rs"))
                                     (call exec_candperm (exp_var "cd") (exp_var "cs") (exp_var "rs"))%exp
           | kcsetbounds    => MkAlt (pat_tuple ("cd" , "cs" , "rs"))
                                     (call exec_csetbounds (exp_var "cd") (exp_var "cs") (exp_var "rs"))%exp
           | kcsetboundsimm => MkAlt (pat_tuple ("cd" , "cs" , "imm"))
                                     (call exec_csetboundsimm (exp_var "cd") (exp_var "cs") (exp_var "imm"))%exp
           | kaddi          => MkAlt (pat_tuple ("rd" , "rs" , "imm"))
                                     (call exec_addi (exp_var "rd") (exp_var "rs") (exp_var "imm"))%exp
           | kadd           => MkAlt (pat_tuple ("rd" , "rs1" , "rs2"))
                                     (call exec_add (exp_var "rd") (exp_var "rs1") (exp_var "rs2"))%exp
           | ksub           => MkAlt (pat_tuple ("rd" , "rs1" , "rs2"))
                                     (call exec_sub (exp_var "rd") (exp_var "rs1") (exp_var "rs2"))%exp
           | kslt           => MkAlt (pat_tuple ("rd" , "rs1" , "rs2"))
                                     (call exec_slt (exp_var "rd") (exp_var "rs1") (exp_var "rs2"))%exp
           | kslti          => MkAlt (pat_tuple ("rd" , "rs" , "imm"))
                                     (call exec_slti (exp_var "rd") (exp_var "rs") (exp_var "imm"))%exp
           | ksltu          => MkAlt (pat_tuple ("rd" , "rs1" , "rs2"))
                                     (call exec_sltu (exp_var "rd") (exp_var "rs1") (exp_var "rs2"))%exp
           | ksltiu         => MkAlt (pat_tuple ("rd" , "rs" , "imm"))
                                     (call exec_sltiu (exp_var "rd") (exp_var "rs") (exp_var "imm"))%exp
           | kcgettag       => MkAlt (pat_pair "rd" "cs")
                                     (call exec_cgettag (exp_var "rd") (exp_var "cs"))%exp
           | kcgetperm      => MkAlt (pat_pair "rd" "cs")
                                     (call exec_cgetperm (exp_var "rd") (exp_var "cs"))%exp
           | kcgetbase      => MkAlt (pat_pair "rd" "cs")
                                     (call exec_cgetbase (exp_var "rd") (exp_var "cs"))%exp
           | kcgetlen       => MkAlt (pat_pair "rd" "cs")
                                     (call exec_cgetlen (exp_var "rd") (exp_var "cs"))%exp
           | kcgetaddr      => MkAlt (pat_pair "rd" "cs")
                                     (call exec_cgetaddr (exp_var "rd") (exp_var "cs"))%exp
           | kfail          => MkAlt pat_unit
                                     (call exec_fail)%exp
           | kret           => MkAlt pat_unit
                                     (call exec_ret)%exp
           end).

    Definition fun_read_mem : Stm ["c" ∷ ty.cap] ty.memval :=
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (let: q :: bool := call within_bounds c in
       stm_assert q (exp_string "Err: [read_mem] out of bounds") ;;
       foreign rM (exp_var "cursor")).

    Definition fun_write_mem : Stm ["c" ∷ ty.cap; "v" ∷ ty.memval] ty.unit :=
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (let: q :: bool := call within_bounds c in
       stm_assert q (exp_string "Err: [write_mem] out of bounds") ;;
       foreign wM (exp_var "cursor") (exp_var "v")).

    Definition fun_exec : Stm [] ty.bool :=
      let: "c" := stm_read_register pc in
      (let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
       use lemma correctPC_subperm_R [exp_var "c"] ;;
       let: n :: ty.memval := call read_mem c in
       match: n with
       | inl n => 
           let: i :: ty.instr := foreign dI n in
           call exec_instr i
       | inr c => fail "Err [exec]: instructions cannot be capabilities"
       end).

    Definition fun_step : Stm [] ty.unit :=
      let: "tmp1" := stm_read_register pc in
      let: "tmp2" := call is_correct_pc (exp_var "tmp1") in
      if: exp_var "tmp2"
      then
        call exec ;;
        stm_val ty.unit tt
      else
        fail "Err [step]: incorrect PC".

    Definition fun_loop : Stm [] ty.unit :=
      call step ;; call loop.

  End ExecStore.

  Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | read_reg           => fun_read_reg
    | read_reg_cap       => fun_read_reg_cap
    | read_reg_num       => fun_read_reg_num
    | write_reg          => fun_write_reg
    | next_pc            => fun_next_pc
    | update_pc          => fun_update_pc
    | update_pc_perm     => fun_update_pc_perm
    | is_correct_pc      => fun_is_correct_pc
    | is_perm            => fun_is_perm
    | add_pc             => fun_add_pc
    | read_mem           => fun_read_mem
    | write_mem          => fun_write_mem
    | read_allowed       => fun_read_allowed
    | write_allowed      => fun_write_allowed
    | within_bounds      => fun_within_bounds
    | perm_to_bits       => fun_perm_to_bits
    | perm_from_bits     => fun_perm_from_bits
    | and_perm           => fun_and_perm
    | is_sub_perm        => fun_is_sub_perm
    | is_within_range    => fun_is_within_range
    | abs                => fun_abs
    | is_not_zero        => fun_is_not_zero
    | can_incr_cursor    => fun_can_incr_cursor
    | exec_jalr_cap      => fun_exec_jalr_cap
    | exec_cjalr         => fun_exec_cjalr
    | exec_cjal          => fun_exec_cjal
    | exec_bne           => fun_exec_bne
    | exec_cmove         => fun_exec_cmove
    | exec_ld            => fun_exec_ld
    | exec_sd            => fun_exec_sd
    | exec_cincoffset    => fun_exec_cincoffset
    | exec_candperm      => fun_exec_candperm
    | exec_csetbounds    => fun_exec_csetbounds
    | exec_csetboundsimm => fun_exec_csetboundsimm
    | exec_addi          => fun_exec_addi
    | exec_add           => fun_exec_add
    | exec_sub           => fun_exec_sub
    | exec_slt           => fun_exec_slt
    | exec_slti          => fun_exec_slti
    | exec_sltu          => fun_exec_sltu
    | exec_sltiu         => fun_exec_sltiu
    | exec_cgettag       => fun_exec_cgettag
    | exec_cgetperm      => fun_exec_cgetperm
    | exec_cgetbase      => fun_exec_cgetbase
    | exec_cgetlen       => fun_exec_cgetlen
    | exec_cgetaddr      => fun_exec_cgetaddr
    | exec_fail          => fun_exec_fail
    | exec_ret           => fun_exec_ret
    | exec_instr         => fun_exec_instr
    | exec               => fun_exec
    | step               => fun_step
    | loop               => fun_loop
    end.

End FunDefKit.

Include DefaultRegStoreKit MinCapsGlobalState.

Section ForeignKit.
  Definition fun_rM (μ : Memory) (addr : Val ty.int) : Val ty.memval :=
    μ addr.

  Definition fun_wM (μ : Memory) (addr : Val ty.int) (val : Val ty.memval) : Memory :=
    fun addr' => if Z.eqb addr addr' then val else μ addr'.

  (* We postulate a pure decode function and assume that that's what the decode primitive implements. *)
  (* Similarly for *_{from,to}_bits functions, ideally we would move to actual bitvectors for values... *)
  Axiom pure_decode : Z -> string + Instruction.

  #[derive(equations=no)]
  Equations ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop :=
    ForeignCall rM [addr] res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , μ , inr (fun_rM μ addr));
    ForeignCall wM [addr; val] res γ γ' μ μ' =>
      (γ' , μ' , res) = (γ , fun_wM μ addr val , inr tt);
    ForeignCall dI [code] res γ γ' μ μ' :=
      (γ' , μ' , res) = (γ , μ , pure_decode code).

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof. destruct f; env.destroy args; repeat econstructor. Qed.
End ForeignKit.

Include ProgramMixin MinCapsGlobalState.

  Import callgraph.

  Lemma fundef_bindfree (Δ : PCtx) (τ : Ty) (f : Fun Δ τ) :
    stm_bindfree (FunDef f).
  Proof. destruct f; now vm_compute. Qed.

  Definition 𝑭_call_graph := generic_call_graph.
  Lemma 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.
  Proof. apply generic_call_graph_wellformed, fundef_bindfree. Qed.

  Abbreviation AccessibleFun f := (Accessible 𝑭_call_graph f).

  Module Import WithAccessibleTactics.
    Import AccessibleTactics.

    Instance accessible_read_reg : AccessibleFun read_reg.
    Proof. accessible_proof. Qed.
    Instance accessible_read_reg_cap : AccessibleFun read_reg_cap.
    Proof. accessible_proof. Qed.
    Instance accessible_read_reg_num : AccessibleFun read_reg_num.
    Proof. accessible_proof. Qed.
    Instance accessible_write_reg : AccessibleFun write_reg.
    Proof. accessible_proof. Qed.
    Instance accessible_next_pc : AccessibleFun next_pc.
    Proof. accessible_proof. Qed.
    Instance accessible_update_pc : AccessibleFun update_pc.
    Proof. accessible_proof. Qed.
    Instance accessible_update_pc_perm : AccessibleFun update_pc_perm.
    Proof. accessible_proof. Qed.
    Instance accessible_is_perm : AccessibleFun is_perm.
    Proof. accessible_proof. Qed.
    Instance accessible_is_correct_pc : AccessibleFun is_correct_pc.
    Proof. accessible_proof. Qed.
    Instance accessible_add_pc : AccessibleFun add_pc.
    Proof. accessible_proof. Qed.
    Instance accessible_within_bounds : AccessibleFun within_bounds.
    Proof. accessible_proof. Qed.
    Instance accessible_is_sub_perm : AccessibleFun is_sub_perm.
    Proof. accessible_proof. Qed.
    Instance accessible_write_allowed : AccessibleFun write_allowed.
    Proof. accessible_proof. Qed.
    Instance accessible_perm_to_bits : AccessibleFun perm_to_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_perm_from_bits : AccessibleFun perm_from_bits.
    Proof. accessible_proof. Qed.
    Instance accessible_and_perm : AccessibleFun and_perm.
    Proof. accessible_proof. Qed.
    Instance accessible_is_within_range : AccessibleFun is_within_range.
    Proof. accessible_proof. Qed.
    Instance accessible_abs : AccessibleFun abs.
    Proof. accessible_proof. Qed.
    Instance accessible_read_mem : AccessibleFun read_mem.
    Proof. accessible_proof. Qed.
    Instance accessible_write_mem : AccessibleFun write_mem.
    Proof. accessible_proof. Qed.
    Instance accessible_read_allowed : AccessibleFun read_allowed.
    Proof. accessible_proof. Qed.
    Instance accessible_is_not_zero : AccessibleFun is_not_zero.
    Proof. accessible_proof. Qed.
    Instance accessible_can_incr_cursor : AccessibleFun can_incr_cursor.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cjalr : AccessibleFun exec_cjalr.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_jalr_cap : AccessibleFun exec_jalr_cap.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cjal : AccessibleFun exec_cjal.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_bne : AccessibleFun exec_bne.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_ld : AccessibleFun exec_ld.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_sd : AccessibleFun exec_sd.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_addi : AccessibleFun exec_addi.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_add : AccessibleFun exec_add.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_sub : AccessibleFun exec_sub.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_slt : AccessibleFun exec_slt.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_slti : AccessibleFun exec_slti.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_sltu : AccessibleFun exec_sltu.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_sltiu : AccessibleFun exec_sltiu.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cmove : AccessibleFun exec_cmove.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cincoffset : AccessibleFun exec_cincoffset.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_candperm : AccessibleFun exec_candperm.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_csetbounds : AccessibleFun exec_csetbounds.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_csetboundsimm : AccessibleFun exec_csetboundsimm.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cgettag : AccessibleFun exec_cgettag.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cgetperm : AccessibleFun exec_cgetperm.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cgetbase : AccessibleFun exec_cgetbase.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cgetlen : AccessibleFun exec_cgetlen.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_cgetaddr : AccessibleFun exec_cgetaddr.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_fail : AccessibleFun exec_fail.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_ret : AccessibleFun exec_ret.
    Proof. accessible_proof. Qed.
    Instance accessible_exec_instr : AccessibleFun exec_instr.
    Proof. accessible_proof. Qed.
    Instance accessible_exec : AccessibleFun exec.
    Proof. accessible_proof. Qed.
    Instance accessible_step : AccessibleFun step.
    Proof. accessible_proof. Qed.
  End WithAccessibleTactics.

  Definition 𝑭_accessible {Δ τ} (f : 𝑭 Δ τ) : option (AccessibleFun f) :=
    match f with
    | loop => None
    | _    => Some _
    end.

End MinCapsProgram.
