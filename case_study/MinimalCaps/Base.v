(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Sander Huyghebaert                      *)
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
     Classes.EquivDec
     Strings.String.
From stdpp Require
     finite.
From Equations Require Import
     Equations.
Require Export Katamaran.Base.

(*** TYPES ***)

Inductive RegName : Set :=
  R0 | R1 | R2 | R3.

Definition Dst : Set := RegName.
Definition Src : Set := RegName.
Definition Imm : Set := Z.

Inductive Instruction : Set :=
| jalr_cap      (cd  : Dst) (cs  : Src)
| cjalr         (cd  : Dst) (cs  : Src) (imm : Imm)
| cjal          (cd  : Dst) (imm : Imm)
| bne           (rs1 : Src) (rs2 : Src) (imm : Imm)
| ld            (cd  : Dst) (cs  : Src) (imm : Imm)
| sd            (rs1 : Src) (rs2 : Src) (imm : Imm)
| addi          (rd  : Dst) (rs  : Src) (imm : Imm)
| add           (rd  : Dst) (rs1 : Src) (rs2 : Src)
| sub           (rd  : Dst) (rs1 : Src) (rs2 : Src)
| slt           (rd  : Dst) (rs1 : Src) (rs2 : Src)
| slti          (rd  : Dst) (rs  : Src) (imm : Imm)
| sltu          (rd  : Dst) (rs1 : Src) (rs2 : Src)
| sltiu         (rd  : Dst) (rs  : Src) (imm : Imm)
| cmove         (cd  : Dst) (cs  : Src)
| cincoffset    (cd  : Dst) (cs  : Src) (rs : Src)
| candperm      (cd  : Dst) (cs  : Src) (rs : Src)
| csetbounds    (cd  : Dst) (cs  : Src) (rs : Src)
| csetboundsimm (cd  : Dst) (cs  : Src) (imm : Imm)
| cgettag       (rd  : Dst) (cd  : Src)
| cgetperm      (rd  : Dst) (cs  : Src)
| cgetbase      (rd  : Dst) (cs  : Src)
| cgetlen       (rd  : Dst) (cs  : Src)
| cgetaddr      (rd  : Dst) (cs  : Src)
| fail
| ret.

Inductive InstructionConstructor : Set :=
| kjalr_cap
| kcjalr
| kcjal
| kbne
| kcmove
| kld
| ksd
| kaddi
| kadd
| ksub
| kslt
| kslti
| ksltu
| ksltiu
| kcincoffset
| kcandperm
| kcsetbounds
| kcsetboundsimm
| kcgettag
| kcgetperm
| kcgetbase
| kcgetlen
| kcgetaddr
| kfail
| kret.

Inductive Permission : Set :=
  O | R | RW | E.

Definition Addr : Set := Z.

Record Capability : Set :=
  MkCap
    { cap_permission : Permission;
      cap_begin      : Addr;
      cap_end        : Addr;
      cap_cursor     : Addr;
    }.

(** Enums **)
Inductive Enums : Set :=
| permission
| regname.

(** Unions **)
Inductive Unions : Set :=
| instruction.

(** Records **)
Inductive Records : Set :=
| capability.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Capability.
  Derive NoConfusion for Permission.
  Derive NoConfusion for RegName.
  Derive NoConfusion for Enums.
  Derive NoConfusion for Unions.
  Derive NoConfusion for Records.
  Derive NoConfusion for Instruction.
  Derive NoConfusion for InstructionConstructor.

End TransparentObligations.

Derive EqDec for Permission.
Definition is_perm := @equiv_decb _ _ _ Permission_eqdec.
Lemma is_perm_iff : forall p p',
    is_perm p p' = true <-> p = p'.
Proof.
  unfold is_perm.
  intros; split.
  - destruct p, p'; cbn; intros ?; auto; try discriminate.
  - intros; subst; destruct p'; auto.
Qed.

Derive EqDec for Capability.
Derive EqDec for RegName.

Derive EqDec for Enums.
Derive EqDec for Unions.
Derive EqDec for Records.
Derive EqDec for Instruction.
Derive EqDec for InstructionConstructor.

Section Finite.

  Import stdpp.finite.

  Local Obligation Tactic :=
    finite_from_eqdec.

  #[export,program] Instance Permission_finite : Finite Permission :=
    {| enum := [O;R;RW;E] |}.

  #[export,program] Instance RegName_finite : Finite RegName :=
    {| enum := [R0;R1;R2;R3] |}.

  #[export,program] Instance InstructionConstructor_finite :
    Finite InstructionConstructor :=
    {| enum := [kjalr_cap;kcjalr;kcjal;kbne;kcmove;kld;ksd;kcincoffset;kcandperm;kcsetbounds;kcsetboundsimm;kcgettag;kaddi;kadd;ksub;kslt;kslti;ksltu;ksltiu;kcgetperm;kcgetbase;kcgetlen;kcgetaddr;kfail;kret] |}.

End Finite.

Module Export MinCapsBase <: Base.
  Import ctx.notations.
  Import ctx.resolution.
  Import env.notations.
  Import stdpp.finite.

  Local Open Scope string_scope.

  #[export] Instance typedeclkit : TypeDeclKit :=
    {| enumi := Enums;
       unioni := Unions;
       recordi := Records;
    |}.

  Notation "ty.dst" := (ty.enum regname).
  Notation "ty.src" := (ty.enum regname).
  Notation "ty.cap" := (ty.record capability).
  Notation "ty.word" := (ty.sum ty.int ty.cap).
  Notation "ty.memval" := (ty.word).
  Notation "ty.addr" := (ty.int).
  Notation "ty.perm" := (ty.enum permission).
  Notation "ty.instr" := (ty.union instruction).

  Definition enum_denote (e : Enums) : Set :=
    match e with
    | permission => Permission
    | regname    => RegName
    end.

  Definition union_denote (U : Unions) : Set :=
    match U with
    | instruction => Instruction
    end.

  Definition record_denote (R : Records) : Set :=
    match R with
    | capability => Capability
    end.

  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit :=
    {| enumt := enum_denote;
       uniont := union_denote;
       recordt := record_denote;
    |}.

  Definition union_constructor (U : Unions) : Set :=
    match U with
    | instruction => InstructionConstructor
    end.

  Definition union_constructor_type (U : Unions) : union_constructor U -> Ty :=
    match U with
    | instruction => fun K =>
      match K with
      | kjalr_cap      => ty.prod ty.dst ty.src
      | kcjalr         => ty.tuple [ty.dst; ty.src; ty.int]
      | kcjal          => ty.prod ty.dst ty.int
      | kbne           => ty.tuple [ty.src; ty.src; ty.int]
      | kld            => ty.tuple [ty.dst; ty.src; ty.int]
      | ksd            => ty.tuple [ty.src; ty.src; ty.int]
      | kaddi          => ty.tuple [ty.dst; ty.src; ty.int]
      | kadd           => ty.tuple [ty.dst; ty.src; ty.src]
      | ksub           => ty.tuple [ty.dst; ty.src; ty.src]
      | kslt           => ty.tuple [ty.dst; ty.src; ty.src]
      | kslti          => ty.tuple [ty.dst; ty.src; ty.int]
      | ksltu          => ty.tuple [ty.dst; ty.src; ty.src]
      | ksltiu         => ty.tuple [ty.dst; ty.src; ty.int]
      | kcmove         => ty.prod ty.dst ty.src
      | kcincoffset    => ty.tuple [ty.dst; ty.src; ty.src]
      | kcandperm      => ty.tuple [ty.dst; ty.src; ty.src]
      | kcsetbounds    => ty.tuple [ty.dst; ty.src; ty.src]
      | kcsetboundsimm => ty.tuple [ty.dst; ty.src; ty.int]
      | kcgettag       => ty.prod ty.dst ty.src
      | kcgetperm      => ty.prod ty.dst ty.src
      | kcgetbase      => ty.prod ty.dst ty.src
      | kcgetlen       => ty.prod ty.dst ty.src
      | kcgetaddr      => ty.prod ty.dst ty.src
      | kfail          => ty.unit
      | kret           => ty.unit
      end
    end.

  #[export] Instance eqdec_enum_denote E : EqDec (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance finite_enum_denote E : finite.Finite (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance eqdec_union_denote U : EqDec (union_denote U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_union_constructor U : EqDec (union_constructor U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance finite_union_constructor U : finite.Finite (union_constructor U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_record_denote R : EqDec (record_denote R) :=
    ltac:(destruct R; auto with typeclass_instances).

  Definition union_fold (U : unioni) : { K & Val (union_constructor_type U K) } -> uniont U :=
    match U with
    | instruction => fun Kv =>
      match Kv with
      | existT kjalr_cap      (cd , cs)              => jalr_cap      cd  cs
      | existT kcjalr         (tt , cd , cs , imm)   => cjalr         cd  cs  imm
      | existT kcjal          (cd , imm)             => cjal          cd  imm
      | existT kbne           (tt , rs1 , rs2 , imm) => bne           rs1 rs2 imm
      | existT kld            (tt , cd , cs , imm)   => ld            cd  cs  imm
      | existT ksd            (tt , rs1 , rs2, imm)  => sd            rs1 rs2 imm
      | existT kaddi          (tt , rd , rs , imm)   => addi          rd  rs  imm
      | existT kadd           (tt , rd , rs1 , rs2)  => add           rd  rs1 rs2
      | existT ksub           (tt , rd , rs1 , rs2)  => sub           rd  rs1 rs2
      | existT kslt           (tt , rd , rs1 , rs2)  => slt           rd  rs1 rs2
      | existT kslti          (tt , rd , rs , imm)   => slti          rd  rs  imm
      | existT ksltu          (tt , rd , rs1 , rs2)  => sltu          rd  rs1 rs2
      | existT ksltiu         (tt , rd , rs , imm)   => sltiu         rd  rs  imm
      | existT kcmove         (cd , cs)              => cmove         cd  cs
      | existT kcincoffset    (tt , cd , cs , rs)    => cincoffset    cd  cs  rs
      | existT kcandperm      (tt , cd , cs , rs)    => candperm      cd  cs  rs
      | existT kcsetbounds    (tt , cd , cs , rs)    => csetbounds    cd  cs  rs
      | existT kcsetboundsimm (tt , cd , cs , imm)   => csetboundsimm cd  cs  imm
      | existT kcgettag       (rd , cs)              => cgettag       rd  cs
      | existT kcgetperm      (rd , cs)              => cgetperm      rd  cs
      | existT kcgetbase      (rd , cs)              => cgetbase      rd  cs
      | existT kcgetlen       (rd , cs)              => cgetlen       rd  cs
      | existT kcgetaddr      (rd , cs)              => cgetaddr      rd  cs
      | existT kfail          tt                     => fail
      | existT kret           tt                     => ret
      end
    end.

  Definition union_unfold (U : unioni) : uniont U -> { K & Val (union_constructor_type U K) } :=
    match U with
    | instruction => fun Kv =>
      match Kv with
      | jalr_cap      cd  cs      => existT kjalr_cap      (cd , cs)
      | cjalr         cd  cs  imm => existT kcjalr         (tt , cd , cs , imm)
      | cjal          cd  imm     => existT kcjal          (cd , imm)
      | bne           rs1 rs2 imm => existT kbne           (tt , rs1 , rs2 , imm)
      | ld            cd  cs  imm => existT kld            (tt , cd , cs , imm)
      | sd            rs1 rs2 imm => existT ksd            (tt , rs1 , rs2 , imm)
      | addi          rd  rs  imm => existT kaddi          (tt , rd , rs , imm)
      | add           rd  rs1 rs2 => existT kadd           (tt , rd , rs1 , rs2)
      | sub           rd  rs1 rs2 => existT ksub           (tt , rd , rs1 , rs2)
      | slt           rd  rs1 rs2 => existT kslt           (tt , rd , rs1 , rs2)
      | slti          rd  rs  imm => existT kslti          (tt , rd , rs , imm)
      | sltu          rd  rs1 rs2 => existT ksltu          (tt , rd , rs1 , rs2)
      | sltiu         rd  rs  imm => existT ksltiu         (tt , rd , rs , imm)
      | cmove         cd  cs      => existT kcmove         (cd , cs)
      | cincoffset    cd  cs  rs  => existT kcincoffset    (tt , cd , cs , rs)
      | candperm      cd  cs  rs  => existT kcandperm      (tt , cd , cs , rs)
      | csetbounds    cd  cs  rs  => existT kcsetbounds    (tt, cd , cs , rs)
      | csetboundsimm cd  cs  imm => existT kcsetboundsimm (tt, cd , cs , imm)
      | cgettag       rd  cs      => existT kcgettag       (rd , cs)
      | cgetperm      rd  cs      => existT kcgetperm      (rd , cs)
      | cgetbase      rd  cs      => existT kcgetbase      (rd , cs)
      | cgetlen       rd  cs      => existT kcgetlen       (rd , cs)
      | cgetaddr      rd  cs      => existT kcgetaddr      (rd , cs)
      | fail                      => existT kfail          tt
      | ret                       => existT kret           tt
      end
    end.

  Definition record_field_type (R : recordi) : NCtx string Ty :=
    match R with
    | capability => [ "cap_permission" ∷ ty.perm;
                      "cap_begin"      ∷ ty.addr;
                      "cap_end"        ∷ ty.addr;
                      "cap_cursor"     ∷ ty.addr
                    ]
    end.

  Definition record_fold (R : recordi) : NamedEnv Val (record_field_type R) -> recordt R :=
    match R with
    | capability =>
      fun fields =>
        MkCap
          fields.[??"cap_permission"]
          fields.[??"cap_begin"]
          fields.[??"cap_end"]
          fields.[??"cap_cursor"]
    end%exp.

  Definition record_unfold (R : recordi) : recordt R -> NamedEnv Val (record_field_type R) :=
    match R  with
    | capability =>
      fun c=>
        env.nil
          ► ("cap_permission" ∷ ty.perm ↦ cap_permission c)
          ► ("cap_begin"      ∷ ty.addr ↦ cap_begin c)
          ► ("cap_end"        ∷ ty.addr ↦ cap_end c)
          ► ("cap_cursor"     ∷ ty.addr ↦ cap_cursor c)
    end%env.

  #[export,refine] Instance typedefkit : TypeDefKit typedenotekit :=
    {| unionk           := union_constructor;
       unionk_ty        := union_constructor_type;
       recordf          := string;
       recordf_ty       := record_field_type;
       unionv_fold      := union_fold;
       unionv_unfold    := union_unfold;
       recordv_fold     := record_fold;
       recordv_unfold   := record_unfold;
    |}.
  Proof.
    - abstract (now intros [] []).
    - abstract (intros [] [[] x]; cbn in x;
                repeat
                  match goal with
                  | x: unit     |- _ => destruct x
                  | x: prod _ _ |- _ => destruct x
                  end; auto).
    - abstract (now intros [] []).
    - abstract (intros []; now apply env.Forall_forall).
  Defined.

  Canonical typedeclkit.
  Canonical typedenotekit.
  Canonical typedefkit.

  #[export] Instance varkit : VarKit := DefaultVarKit.

  Include BaseMixin.

End MinCapsBase.

Module Export MinCapsGlobalState <: GlobalState.
  Module BASE := MinCapsBase.

  Import ctx.notations.
  Import ctx.resolution.
  Import env.notations.
  Import stdpp.finite.

  #[local] Open Scope string_scope.

  Section RegDeclKit.

    Inductive Reg : Ty -> Set :=
    | pc   : Reg ty.cap
    | reg1 : Reg ty.word
    | reg2 : Reg ty.word
    | reg3 : Reg ty.word.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive Signature NoConfusion for Reg.
    End TransparentObligations.

    Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.

    #[export,refine] Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg) :=
      fun '(existT σ x) '(existT τ y) =>
        match x , y with
        | pc            , pc            => left eq_refl
        | reg1          , reg1          => left eq_refl
        | reg2          , reg2          => left eq_refl
        | reg3          , reg3          => left eq_refl
        | _             , _             => right _
        end.
    Proof. all: transparent_abstract (intros H; depelim H). Defined.

    Local Obligation Tactic :=
      finite_from_eqdec.

    #[export,program] Instance 𝑹𝑬𝑮_finite : Finite (sigT Reg) :=
      {| enum := [ existT _ pc; existT _ reg1; existT _ reg2; existT _ reg3 ] |}.

  End RegDeclKit.

  Section MemoryModel.
    Definition Memory := Addr -> (Z + Capability).
  End MemoryModel.

End MinCapsGlobalState.
