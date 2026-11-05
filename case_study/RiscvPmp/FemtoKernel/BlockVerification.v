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
     ZArith.ZArith
     Lists.List
     Strings.String.
From Katamaran Require Import
     Base
     Bitvector
     Notations
     RiscvPmp.BlockVer.Spec
     RiscvPmp.BlockVer.TotalVerifier
     RiscvPmp.IrisModel
     RiscvPmp.IrisInstance
     RiscvPmp.Machine
     RiscvPmp.PmpCheck
     RiscvPmp.Sig
     RiscvPmp.Contracts
     RiscvPmp.LoopVerification
     RiscvPmp.Everything
     RiscvPmp.FemtoKernel.Kernel.
From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.proofmode Require string_ident proofmode.
From stdpp Require namespaces.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.
Open Scope ctx_scope.

Import iris.proofmode.proofmode.

Import Contracts.
Import Assembly.
Import ArchState (ArchState).

Import RVPCOM.
Import RVPV2.
Import RVPINST2.
Import RVPBASE2.
Import RVPPRED2.

Section BlockVerification.
  Import bv.notations.
  Import ListNotations.
  Import TermNotations.

  Open Scope hex_Z_scope.

  Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).
  (* Shorthand for the pmp entries in both Katamaran and Iris *)
  Local Abbreviation asn_femto_pmpentries a :=
    ([(term_val ty_pmpcfg_ent femto_pmpcfg_ent0 ,ₜ (a +ᵇ term_val ty_xlenbits (bv.of_N adv_addr)));
      (term_val ty_pmpcfg_ent femto_pmpcfg_ent1 ,ₜ (term_val ty_xlenbits (bv.of_N adv_addr_end)))])%list.
  (* TODO: this notation should already be defined elsewhere, but it's not available here... Find the module where it's defined and import it. *)
  Notation "a '↦ₘ' t" := (asn.chunk (chunk_user (@ptstomem bytes_per_word) [a; t])) (at level 70).

  Import RiscvPmp.Sig.
  #[local] Abbreviation asn_inv_mmio := (asn.chunk (chunk_user (inv_mmio bytes_per_word) [env])). (* Fix word length at 4 for this example, as we do not perform any other writes*)
  #[local] Abbreviation asn_pmp_addr_access l m := (asn.chunk (chunk_user pmp_addr_access [l; m])).
  #[local] Abbreviation asn_pmp_entries l := (asn.chunk (chunk_user pmp_entries [l])).

  Definition post_mip_val : Val ty_Minterrupts :=
    MkMinterrupts false false false false false false false false false.
  Definition term_post_mip_val {Σ} : Term Σ ty_Minterrupts :=
    term_val ty_Minterrupts post_mip_val.

  Definition Σ__csrs : LCtx :=
    ["mtvec" :: ty_xlenbits;
     "mcause" :: ty_xlenbits;
     "mepc" :: ty_xlenbits;
     "mie" :: ty_Minterrupts;
     "mstatus_mpie" :: ty.bool;
     "mstatus_mpp" :: ty_privilege;
     "mstatus_spp" :: ty_privilege;
     "mstatus_spie" :: ty.bool;
     "mstatus_sie" :: ty.bool;
     "mideleg" :: ty_Minterrupts;
     "medeleg" :: ty_Medeleg;
     "scause" :: ty_xlenbits;
     "sscratch" :: ty_xlenbits;
     "sepc" :: ty_xlenbits;
     "stvec" :: ty_xlenbits].

  Definition csrs_valuation (archstate : ArchState) (vmie : Val ty_Minterrupts) : Valuation Σ__csrs :=
    let ms := ArchState.mstate archstate in
    let ss := ArchState.sstate archstate in
    [env]
      .["mtvec" ∷ ty_xlenbits ↦ ArchState.mtvec ms]
      .["mcause" ∷ ty_xlenbits ↦ ArchState.mcause ms]
      .["mepc" ∷ ty_xlenbits ↦ ArchState.mepc ms]
      .["mie" ∷ ty_Minterrupts ↦ vmie]
      .["mstatus_mpie" ∷ ty.bool ↦ ArchState.mpie ms]
      .["mstatus_mpp" ∷ ty_privilege ↦ ArchState.mpp ms]
      .["mstatus_spp" ∷ ty_privilege ↦ S_SPP (ArchState.sstatus ss)]
      .["mstatus_spie" ∷ ty.bool ↦ S_SPIE (ArchState.sstatus ss)]
      .["mstatus_sie" ∷ ty.bool ↦ S_SIE (ArchState.sstatus ss)]
      .["mideleg" ∷ ty_Minterrupts ↦ ArchState.mideleg ms]
      .["medeleg" ∷ ty_Medeleg ↦ ArchState.medeleg ms]
      .["scause" ∷ ty_xlenbits ↦ ArchState.scause ss]
      .["sscratch" ∷ ty_xlenbits ↦ ArchState.sscratch ss]
      .["sepc" ∷ ty_xlenbits ↦ ArchState.sepc ss]
      .["stvec" ∷ ty_xlenbits ↦ ArchState.stvec ss].

  Section WithAsnNotations.
    Import asn.notations.
    Import TermNotations.

    Example femtokernel_init_pre : Assertion (Σ__csrs ▻▻ ["a"::ty_xlenbits]) :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N adv_addr) < term_val ty.int (Z.of_N maxAddr))%asn ∗
        mtvec ↦ term_var "mtvec" ∗
        mcause ↦ term_var "mcause" ∗
        (∃ "v", mip ↦ term_var "v") ∗ mie ↦ term_var "mie" ∗
        mepc ↦ term_var "mepc" ∗
    mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false; term_val ty.bool false] ∗
    mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
    medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
        cur_privilege ↦ term_val ty_privilege Machine ∗
        (∃ "x1", x1 ↦ term_var "x1") ∗
        (asn_pmp_entries (term_list [(term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero);
                                     (term_val ty_pmpcfg_ent default_pmpcfg_ent ,ₜ term_val ty_xlenbits bv.zero)])).

    Example femtokernel_init_post : Assertion (Σ__csrs ▻▻ ["a"::ty_xlenbits; ("an"::ty_xlenbits)]) :=
      (
        (term_var "an" = term_var "a" +ᵇ (term_val ty_xlenbits (bv.of_N adv_addr)))%asn ∗
          (mtvec ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)) ∗
          mcause ↦ term_var "mcause" ∗
          mip ↦ term_post_mip_val ∗ mie ↦ term_var "mie" ∗
          mepc ↦ term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N adv_addr) ∗
        mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_val ty_privilege User; term_val ty.bool true; term_val ty.bool false; term_val ty.bool true; term_val ty.bool false ] ∗
        mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
        medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
          cur_privilege ↦ term_val ty_privilege User ∗
          x1 ↦ term_val ty_xlenbits [bv 0x80] ∗
          asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a")))
      ).

    Definition femtokernel_handler_shared_pre (addr : N) : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
      (term_unop uop.unsigned (term_var "a") + term_val ty.int (Z.of_N (adv_addr - handler_entry_addr)) < term_val ty.int (Z.of_N maxAddr))%asn ∗
        term_var "a" = term_val ty_xlenbits (bv.of_N addr) ∗
        cur_privilege ↦ term_val ty_privilege Machine ∗
        (mtvec ↦ term_val ty_word (bv.of_N handler_entry_addr)) ∗
        mcause ↦ term_var "mcause" ∗
        (∃ "v", mip ↦ term_var "v") ∗ mie ↦ term_var "mie" ∗
        mepc ↦ term_var "mepc" ∗
        sepc ↦ term_var "sepc" ∗
        scause ↦ term_var "scause" ∗
        sscratch ↦ term_var "sscratch" ∗
        stvec ↦ term_var "stvec" ∗
        mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
        medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
        asn_pmp_entries term_femto_pmpentries ∗
        (* asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)))) ∗ (* Different handler sizes cause different entries *) *)
        asn_inv_mmio.

    Definition femtokernel_handler_shared_post (priv : Term (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) ty_privilege) : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]) :=
      cur_privilege ↦ priv ∗
        mtvec ↦ term_val ty_word (bv.of_N handler_entry_addr) ∗
        mcause ↦ term_var "mcause" ∗
        mip ↦ term_post_mip_val ∗ mie ↦ term_var "mie" ∗
        mepc ↦ term_var "mepc" ∗
        sepc ↦ term_var "sepc" ∗
        scause ↦ term_var "scause" ∗
        sscratch ↦ term_var "sscratch" ∗
        stvec ↦ term_var "stvec" ∗
        mideleg ↦ term_val ty_Minterrupts Minterrupts_zero ∗
        medeleg ↦ term_val ty_Medeleg Medeleg_zero ∗
        asn_pmp_entries term_femto_pmpentries.
    (* asn_pmp_entries (term_list (asn_femto_pmpentries (term_var "a" -ᵇ term_val ty_xlenbits (bv.of_N handler_entry_addr)))). (* Different handler sizes cause different entries *) *)

    Example femtokernel_handler_entry_pre : Assertion (Σ__csrs ▻▻ ["x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_entry_addr) (sub_up1 (sub_cat_left _)) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        x5 ↦ term_var "x5" ∗
        x10 ↦ term_var "x10".

    Example femtokernel_handler_entry_post :
      Assertion (Σ__csrs ▻▻ ["x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        (if: (term_var "x10" ?= term_val ty_xlenbits (bv.of_N mmio_write_adv))
         then term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_entry_size)
         else term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (handler_entry_size + handler_dispatch_size + handler_not_zero_size + handler_is_zero_size))) ∗
        x5 ↦ term_val ty_xlenbits (bv.of_N mmio_write_adv) ∗
        x10 ↦ term_var "x10".

    Example femtokernel_handler_dispatch_pre : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_dispatch_addr) (sub_up1 (sub_cat_left _)) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        x1 ↦ term_var "x1" ∗
        term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

    Example femtokernel_handler_dispatch_post :
      Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        (if: (term_var "secret" ?= term_val ty_xlenbits bv.zero)
         then term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (handler_dispatch_size + handler_not_zero_size))
         else term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_dispatch_size)) ∗
        x1 ↦ term_var "secret" ∗
        term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

    (* The not_zero and is_zero blocks share their contract (modulo their address):
       both perform the (only) observable write of the handler, and log the
       secret to the M-mode only MMIO address. *)
    Definition femtokernel_handler_ack_pre (addr : N) : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "x5" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre addr) (sub_up1 (sub_cat_left _)) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        asn.chunk (chunk_user nothingPending env.nil) ∗
        x1 ↦ term_var "x1" ∗
        x5 ↦ term_var "x5" ∗
        term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

    Example femtokernel_handler_ack_post :
      Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "x5" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        term_var "an" = term_val ty_xlenbits (bv.of_N handler_exit_addr) ∗
        x1 ↦ term_val ty_xlenbits bv.zero ∗
        x5 ↦ term_val ty_xlenbits (bv.of_N 42) ∗
        term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret" ∗
        (* The (only) observable write of the handler. The event is fully
           determined, so that both executions agree on it. *)
        asn.chunk (chunk_user (written bytes_per_word)
                     [term_val ty_xlenbits (bv.of_N mmio_write_adv);
                      term_val (ty_bytes bytes_per_word) (bv.of_N 42)]).

    Example femtokernel_handler_not_zero_pre := femtokernel_handler_ack_pre handler_not_zero_addr.
    Example femtokernel_handler_is_zero_pre := femtokernel_handler_ack_pre handler_is_zero_addr.

    Example femtokernel_handler_secret_write_pre : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_secret_write_addr) (sub_up1 (sub_cat_left _)) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        x1 ↦ term_var "x1" ∗
        term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

    Example femtokernel_handler_secret_write_post :
      Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "secret" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_secret_write_size) ∗
                                        x1 ↦ term_val ty_xlenbits bv.zero ∗
                                        term_val ty_xlenbits (bv.of_N data_addr) ↦ₘ term_var "secret".

    Example femtokernel_handler_shutdown_check_pre : Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_pre handler_shutdown_check_addr) (sub_up1 (sub_cat_left _)) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        x1 ↦ term_var "x1" ∗
        x5 ↦ term_var "x5" ∗
        x10 ↦ term_var "x10".

    Example femtokernel_handler_shutdown_check_post :
      Assertion (Σ__csrs ▻▻ ["x1" :: ty_xlenbits; "x5" :: ty_xlenbits; "x10" :: ty_xlenbits] ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      asn.sub_assertion (femtokernel_handler_shared_post (term_val ty_privilege Machine)) (sub_up1 (sub_up1 (sub_cat_left _))) ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
        (if: (term_var "x10" ?= term_val ty_xlenbits (bv.of_N shutdown_code))
         then term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_shutdown_check_size)
         else term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N (handler_shutdown_check_size + handler_shutdown_size))) ∗
        x1 ↦ term_val ty_xlenbits (bv.of_N shutdown_code) ∗
        x5 ↦ term_val ty_xlenbits mmioShutdownAddr ∗
        x10 ↦ term_var "x10".

    (* Powering off the machine is observable by the adversary, and requires
       that the machine is still powered on. The power tokens are kept apart
       from the rest of the pre- and postcondition, as the relational
       verification hands them to the block separately. *)
    Example femtokernel_handler_shutdown_pre : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
      (femtokernel_handler_shared_pre handler_shutdown_addr ∗
         mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"] ∗
         x5 ↦ term_val ty_xlenbits mmioShutdownAddr ∗
         asn.chunk (chunk_user nothingPending env.nil)) ∗
        asn.chunk (chunk_user Sig.powered [term_val ty.bool true]).

    Example femtokernel_handler_shutdown_post :
      Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      (term_var "an" = term_var "a" +ᵇ term_val ty_xlenbits (bv.of_N handler_shutdown_size) ∗
         asn.chunk (chunk_user (Sig.written_shutdown bytes_per_word)
                      [term_val ty_xlenbits mmioShutdownAddr; term_val (ty_bytes bytes_per_word) bv.zero])) ∗
        asn.chunk (chunk_user Sig.powered [term_val ty.bool false]).

    Example femtokernel_handler_exit_pre : Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits]) :=
      femtokernel_handler_shared_pre handler_exit_addr ∗
        mstatus ↦ term_record rmstatus [nenv term_var "mstatus_mpp"; term_var "mstatus_spp"; term_var "mstatus_mpie"; term_var "mstatus_spie"; term_val ty.bool false; term_var "mstatus_sie"].

    Example femtokernel_handler_exit_post :
      Assertion (Σ__csrs ▻▻ ["a" :: ty_xlenbits; "an"::ty_xlenbits]) :=
      femtokernel_handler_shared_post (term_var "mstatus_mpp") ∗
        mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "mstatus_spp"; term_val ty.bool true; term_var "mstatus_spie"; term_var "mstatus_mpie"; term_var "mstatus_sie"] ∗
        term_var "an" = term_var "mepc".

  End WithAsnNotations.

    (* (* note that this computation takes longer than directly proving sat__femtoinit below *) *)
    (* Time Example t_vc__femtoinit : 𝕊 Σ__femtoinit := *)
    (*   Eval vm_compute in *)
    (*   simplify (VC__addr femtokernel_init_pre femtokernel_init femtokernel_init_post). *)

    Definition vc__gen {Σ : LCtx} (pre : Assertion (Σ ▻ "a" ∷ ty_xlenbits))
      (instrs : list AnnotInstr)
      (post : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits))
      : (Assertion (Σ ▻ "a"∷ty_xlenbits) → list AnnotInstr → Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits) → Valid (λ Σ : World, 𝕊 Σ)) → 𝕊 [] :=
      fun sannotated_block_verification_condition =>
        postprocess2 (sannotated_block_verification_condition pre instrs post wnil).

  Definition vc__femtoinit__gen :=
    vc__gen femtokernel_init_pre femtokernel_init_gen femtokernel_init_post.

  Definition vc__femtoinit : 𝕊 [] :=
    vc__femtoinit__gen RVPTVl.sannotated_block_verification_condition.

  (* NOTE: For now this proof covers both the MMIO and non-MMIO Femtokernel variants, since the start of the adversary region is the same in both cases.
     If this were not the case, we would take a naive approach to verifying both versions of the initialization code here; we would require that `adv_start` takes one of the two values present in the two versions of the initialization code.
     A more general approach would verify the contract under a logical value for `adv_start`.
     This would require the block verifier to support taking a list of instructions that can depend on symbolic values as input (i.e. proper terms).
   *)
  Lemma sat__femtoinit : RVPTVl.safeE vc__femtoinit.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual.
  Qed.

  (* Time Example t_vc__femtohandler : 𝕊 [] := *)
  (*   Eval vm_compute in *)
  (*     simplify (VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post). *)

  Definition vc__femtohandler_entry : 𝕊 [] :=
    postprocess2 (RVPTVl.sannotated_block_verification_condition
                   femtokernel_handler_entry_pre
                   femtokernel_handler_entry
                   femtokernel_handler_entry_post wnil).

  Definition vc__femtohandler_dispatch : 𝕊 [] :=
    postprocess2 (RVPTVl.sannotated_block_verification_condition
                   femtokernel_handler_dispatch_pre
                   femtokernel_handler_dispatch
                   femtokernel_handler_dispatch_post wnil).

  Definition vc__femtohandler_not_zero : 𝕊 [] :=
    postprocess2 (RVPTVl.sannotated_block_verification_condition
                   femtokernel_handler_not_zero_pre
                   femtokernel_handler_not_zero
                   femtokernel_handler_ack_post wnil).

  Definition vc__femtohandler_is_zero : 𝕊 [] :=
    postprocess2 (RVPTVl.sannotated_block_verification_condition
                   femtokernel_handler_is_zero_pre
                   femtokernel_handler_is_zero
                   femtokernel_handler_ack_post wnil).

  Definition vc__femtohandler_secret_write : 𝕊 [] :=
    postprocess2 (RVPTVl.sannotated_block_verification_condition
                   femtokernel_handler_secret_write_pre
                   femtokernel_handler_secret_write
                   femtokernel_handler_secret_write_post wnil).

  Definition vc__femtohandler_exit : 𝕊 [] :=
    postprocess2 (RVPTVl.sannotated_block_verification_condition
                   femtokernel_handler_exit_pre
                   femtokernel_handler_exit
                   femtokernel_handler_exit_post wnil).

    (* let vc1 := VC__addr femtokernel_handler_pre femtokernel_handler femtokernel_handler_post in *)
    (* let vc2 := Postprocessing.prune vc1 in *)
    (* let vc3 := Postprocessing.solve_evars vc2 in *)
    (* let vc4 := Postprocessing.solve_uvars vc3 in *)
    (* let vc5 := Postprocessing.prune vc4 in *)
    (* vc5. *)
  (* Import SymProp.notations. *)
  (* Set Printing Depth 200. *)
  (* Eval vm_compute in vc__femtohandler. *)

  Import Erasure.notations.
  Lemma sat__femtohandler_entry : RVPTVl.safeE vc__femtohandler_entry.
  Proof.
    (* We still need to prove that our word falls within mmio *)
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual.
  Qed.

  (* TODO: would rather write {n} (v : bv n), but eq with bv.sext' complains... *)
  Lemma sext'_zero (v : bv 32) : bv.sext' v 0 = v.
  Proof.
    unfold bv.sext'.
    rewrite bv.ones_O.
    destruct (bv.view (@bv.zero 0)).
    rewrite ssrbool.if_same.
    now rewrite bv.app_nil_r.
  Qed.

  Lemma sat__femtohandler_dispatch : RVPTVl.safeE vc__femtohandler_dispatch.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual.
    all: repeat match goal with
           | H : context [bv.sext' _ 0] |- _ => rewrite sext'_zero in H
           end;
         now rewrite ?sext'_zero.
  Qed.

  Lemma sat__femtohandler_not_zero : RVPTVl.safeE vc__femtohandler_not_zero.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual; rewrite ?sext'_zero; auto.
    all: apply bounds_withinMMIO; now compute.
  Qed.

  Lemma sat__femtohandler_is_zero : RVPTVl.safeE vc__femtohandler_is_zero.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual; rewrite ?sext'_zero; auto.
    all: apply bounds_withinMMIO; now compute.
  Qed.

  Lemma sat__femtohandler_secret_write : RVPTVl.safeE vc__femtohandler_secret_write.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual.
    all: apply bounds_withinMMIO; now compute.
  Qed.

  Definition vc__femtohandler_shutdown_check : 𝕊 [] :=
    postprocess2 (RVPTVl.sannotated_block_verification_condition
                   femtokernel_handler_shutdown_check_pre
                   femtokernel_handler_shutdown_check
                   femtokernel_handler_shutdown_check_post wnil).

  Definition vc__femtohandler_shutdown : 𝕊 [] :=
    postprocess2 (RVPTVl.sannotated_block_verification_condition
                   femtokernel_handler_shutdown_pre
                   femtokernel_handler_shutdown
                   femtokernel_handler_shutdown_post wnil).

  Lemma sat__femtohandler_shutdown_check : RVPTVl.safeE vc__femtohandler_shutdown_check.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual.
  Qed.

  Lemma sat__femtohandler_shutdown : RVPTVl.safeE vc__femtohandler_shutdown.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual; rewrite ?sext'_zero; auto.
    all: apply bounds_withinMMIO; now compute.
  Qed.

  Lemma sat__femtohandler_exit : RVPTVl.safeE vc__femtohandler_exit.
  Proof.
    vm_compute.
    constructor; cbn.
    intuition bv_solve_Ltac.solveBvManual.
  Qed.

  Section WithEnvNotations.
    Import env.notations.

    Definition ContractTy (Σ : gFunctors) := Val ty_xlenbits -> ArchState -> Val ty_Minterrupts -> iProp Σ.

    (* The contract of a block, independent of the Iris instance in which it
       is interpreted (see contract_left and contract_right below). *)
    Record BlockContract :=
      MkBlockContract
        { bc_ctx   : LCtx
        ; bc_args  : Valuation bc_ctx
        ; bc_pre   : Assertion (Σ__csrs ▻▻ bc_ctx ▻▻ ["a" :: ty_xlenbits])
        ; bc_block : Block
        ; bc_post  : Assertion (Σ__csrs ▻▻ bc_ctx ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits])
        }.
    Arguments MkBlockContract {bc_ctx} _ _ _ _.

    Definition contract_femtohandler_builder_gen
      {Σ : gFunctors} {Γ}
      (PredDef : PredicateDef (iProp Σ))
      (semTripleBlock_ :
        (Val ty_xlenbits -> iProp Σ) ->
        Val ty_xlenbits ->
        list AST ->
        (Val ty_xlenbits -> Val ty_xlenbits -> iProp Σ) ->
        iProp Σ)
      (ι : Valuation Γ)
      (PRE : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits]))
      (b : Block)
      (POST : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]))
      : ContractTy Σ :=
      fun a archstate vmie =>
        let ι__csrs := csrs_valuation archstate vmie in
        semTripleBlock_
          (λ a, @asn.interpret _ PredDef _ PRE
                  (ι__csrs ►► ι ►► nenv.nil.["a" ∷ ty_xlenbits ↦ a]))
          a (filter_AST b)
          (λ a an, @asn.interpret _ PredDef _ POST
                     (ι__csrs ►► ι ►► nenv.nil.["a" ∷ ty_xlenbits ↦ a].["an" ∷ ty_xlenbits ↦ an])).

    Definition contract_femtohandler_builder_left `{sG : RVPBASEl.sailGS Σ} {Γ}
      (ι : Valuation Γ)
      (PRE : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits]))
      (b : Block)
      (POST : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]))
      : ContractTy Σ :=
      contract_femtohandler_builder_gen
        (@RVPINSTl.PredicateDefIProp _ sG Instance.trivTrivGS)
        (@RVPTVl.semTripleBlock _ sG)
        ι PRE b POST.

    Definition contract_femtohandler_builder_right `{sG : RVPBASEr.sailGS Σ} {Γ}
      (ι : Valuation Γ)
      (PRE : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits]))
      (b : Block)
      (POST : Assertion (Σ__csrs ▻▻ Γ ▻▻ ["a" :: ty_xlenbits; "an" :: ty_xlenbits]))
      : ContractTy Σ :=
      contract_femtohandler_builder_gen
        (@RVPINSTr.PredicateDefIProp _ sG Instance.trivTrivGS)
        (@RVPTVr.semTripleBlock _ sG)
        ι PRE b POST.

    Definition contract_left `{sG : RVPBASEl.sailGS Σ} (c : BlockContract) : ContractTy Σ :=
      contract_femtohandler_builder_left (bc_args c) (bc_pre c) (bc_block c) (bc_post c).

    Definition contract_right `{sG : RVPBASEr.sailGS Σ} (c : BlockContract) : ContractTy Σ :=
      contract_femtohandler_builder_right (bc_args c) (bc_pre c) (bc_block c) (bc_post c).

    Definition contract_femtoinit : BlockContract :=
      MkBlockContract
        nenv.nil
        femtokernel_init_pre
        femtokernel_init_gen
        femtokernel_init_post.

    Lemma contract_femtoinit_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_left contract_femtoinit) a archstate vmie.
    Proof.
      simpl. iIntros (a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      vm_compute.
      apply sat__femtoinit.
    Qed.

    Lemma contract_femtoinit_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
        ⊢ (contract_right contract_femtoinit) a archstate vmie.
    Proof.
      simpl. iIntros (a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      vm_compute.
      apply sat__femtoinit.
    Qed.

    Definition contract_femtohandler_entry (x5 x10 : Val ty_xlenbits) : BlockContract :=
      MkBlockContract
        nenv.nil.["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10]
        femtokernel_handler_entry_pre
        femtokernel_handler_entry
        femtokernel_handler_entry_post.

    Lemma contract_femtohandler_entry_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x5 x10 a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_left (contract_femtohandler_entry x5 x10)) a archstate vmie.
    Proof.
      simpl. iIntros (x5 x10 a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      pose proof sat__femtohandler_entry as H.
      vm_compute; apply H.
    Qed.

    Lemma contract_femtohandler_entry_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x5 x10 a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_right (contract_femtohandler_entry x5 x10)) a archstate vmie.
    Proof.
      simpl. iIntros (x5 x10 a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      pose proof sat__femtohandler_entry as H.
      vm_compute; apply H.
    Qed.

    Definition contract_femtohandler_dispatch (x1 secret : Val ty_xlenbits) : BlockContract :=
      MkBlockContract
        nenv.nil.["x1" ∷ ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret]
        femtokernel_handler_dispatch_pre
        femtokernel_handler_dispatch
        femtokernel_handler_dispatch_post.

    Lemma contract_femtohandler_dispatch_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_left (contract_femtohandler_dispatch x1 secret)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 secret a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      pose proof sat__femtohandler_dispatch as H.
      vm_compute; apply H.
    Qed.

    Lemma contract_femtohandler_dispatch_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_right (contract_femtohandler_dispatch x1 secret)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 secret a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      pose proof sat__femtohandler_dispatch as H.
      vm_compute; apply H.
    Qed.

    Definition contract_femtohandler_not_zero (x1 x5 secret : Val ty_xlenbits) : BlockContract :=
      MkBlockContract
        nenv.nil.["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
        femtokernel_handler_not_zero_pre
        femtokernel_handler_not_zero
        femtokernel_handler_ack_post.

    Lemma contract_femtohandler_not_zero_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 x5 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_left (contract_femtohandler_not_zero x1 x5 secret)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 x5 secret a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      pose proof sat__femtohandler_not_zero as H.
      vm_compute; apply H.
    Qed.

    Lemma contract_femtohandler_not_zero_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 x5 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_right (contract_femtohandler_not_zero x1 x5 secret)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 x5 secret a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      pose proof sat__femtohandler_not_zero as H.
      vm_compute; apply H.
    Qed.

    Definition contract_femtohandler_is_zero (x1 x5 secret : Val ty_xlenbits) : BlockContract :=
      MkBlockContract
        nenv.nil.["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["secret" ∷ ty_xlenbits ↦ secret]
        femtokernel_handler_is_zero_pre
        femtokernel_handler_is_zero
        femtokernel_handler_ack_post.

    Lemma contract_femtohandler_is_zero_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 x5 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_left (contract_femtohandler_is_zero x1 x5 secret)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 x5 secret a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      pose proof sat__femtohandler_is_zero as H.
      vm_compute; apply H.
    Qed.

    Lemma contract_femtohandler_is_zero_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 x5 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_right (contract_femtohandler_is_zero x1 x5 secret)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 x5 secret a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      pose proof sat__femtohandler_is_zero as H.
      vm_compute; apply H.
    Qed.

    Definition contract_femtohandler_secret_write (x1 secret : Val ty_xlenbits) : BlockContract :=
      MkBlockContract
        nenv.nil.["x1" ∷ ty_xlenbits ↦ x1].["secret" ∷ ty_xlenbits ↦ secret]
        femtokernel_handler_secret_write_pre
        femtokernel_handler_secret_write
        femtokernel_handler_secret_write_post.

    Lemma contract_femtohandler_secret_write_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_left (contract_femtohandler_secret_write x1 secret)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 secret a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      pose proof sat__femtohandler_secret_write as H.
      vm_compute; apply H.
    Qed.

    Lemma contract_femtohandler_secret_write_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 secret a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_right (contract_femtohandler_secret_write x1 secret)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 secret a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      pose proof sat__femtohandler_secret_write as H.
      vm_compute; apply H.
    Qed.

    Definition contract_femtohandler_exit : BlockContract :=
      MkBlockContract
        nenv.nil
        femtokernel_handler_exit_pre
        femtokernel_handler_exit
        femtokernel_handler_exit_post.

    Lemma contract_femtohandler_exit_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_left contract_femtohandler_exit) a archstate vmie.
    Proof.
      simpl. iIntros (a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      pose proof sat__femtohandler_exit as H.
      vm_compute; apply H.
    Qed.

    Lemma contract_femtohandler_exit_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_right contract_femtohandler_exit) a archstate vmie.
    Proof.
      simpl. iIntros (a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      pose proof sat__femtohandler_exit as H.
      vm_compute; apply H.
    Qed.

    Definition contract_femtohandler_shutdown_check (x1 x5 x10 : Val ty_xlenbits) : BlockContract :=
      MkBlockContract
        nenv.nil.["x1" ∷ ty_xlenbits ↦ x1].["x5" ∷ ty_xlenbits ↦ x5].["x10" ∷ ty_xlenbits ↦ x10]
        femtokernel_handler_shutdown_check_pre
        femtokernel_handler_shutdown_check
        femtokernel_handler_shutdown_check_post.

    Lemma contract_femtohandler_shutdown_check_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (x1 x5 x10 a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_left (contract_femtohandler_shutdown_check x1 x5 x10)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 x5 x10 a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      pose proof sat__femtohandler_shutdown_check as H.
      vm_compute; apply H.
    Qed.

    Lemma contract_femtohandler_shutdown_check_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (x1 x5 x10 a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_right (contract_femtohandler_shutdown_check x1 x5 x10)) a archstate vmie.
    Proof.
      simpl. iIntros (x1 x5 x10 a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      pose proof sat__femtohandler_shutdown_check as H.
      vm_compute; apply H.
    Qed.

    Definition contract_femtohandler_shutdown : BlockContract :=
      MkBlockContract
        nenv.nil
        femtokernel_handler_shutdown_pre
        femtokernel_handler_shutdown
        femtokernel_handler_shutdown_post.

    Lemma contract_femtohandler_shutdown_verified__l `{sG : RVPBASEl.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_left contract_femtohandler_shutdown) a archstate vmie.
    Proof.
      simpl. iIntros (a archstate vmie).
      iApply (RVPTVl.sound_sannotated_block_verification_condition RVPCONTRl.lemSemBlockVerif).
      pose proof sat__femtohandler_shutdown as H.
      vm_compute; apply H.
    Qed.

    Lemma contract_femtohandler_shutdown_verified__r `{sG : RVPBASEr.sailGS Σ} : ∀ (a : Val ty_xlenbits) (archstate : ArchState) (vmie : Val ty_Minterrupts),
      ⊢ (contract_right contract_femtohandler_shutdown) a archstate vmie.
    Proof.
      simpl. iIntros (a archstate vmie).
      iApply (RVPTVr.sound_sannotated_block_verification_condition RVPCONTRr.lemSemBlockVerif).
      pose proof sat__femtohandler_shutdown as H.
      vm_compute; apply H.
    Qed.
  End WithEnvNotations.

(*   Definition femtoinit_stats := *)
(*     SymProp.Statistics.count_to_stats *)
(*       (SymProp.Statistics.count_nodes *)
(*          (sannotated_block_verification_condition *)
(*             femtokernel_init_pre *)
(*             femtokernel_init_gen *)
(*             (asn.sep femtokernel_init_post asn.debug) *)
(*             wnil) *)
(*          SymProp.Statistics.empty). *)
(*   (* Eval vm_compute in femtoinit_stats. *) *)

(*   (* There is currently no difference, because the adversary addresses are shared between both cases*) *)
(*   Definition femto_init_stats := femtoinit_stats. *)
(*   (* Eval vm_compute in femto_init_stats. *) *)

(*   (* Definition femtohandler_stats := *) *)
(*   (*   SymProp.Statistics.count_to_stats *) *)
(*   (*     (SymProp.Statistics.count_nodes *) *)
(*   (*        (sannotated_block_verification_condition *) *)
(*   (*           femtokernel_handler_pre *) *)
(*   (*           femtokernel_handler *) *)
(*   (*           (asn.sep femtokernel_handler_post asn.debug) *) *)
(*   (*           wnil) *) *)
(*   (*        SymProp.Statistics.empty). *) *)
(*   (* Eval vm_compute in femtohandler_stats. *) *)

End BlockVerification.

Ltac set_to_list s l Hl Hel :=
  remember (elements s) as l eqn:Hel;
  assert (Hl : list_to_set l = s) by (subst; apply list_to_set_elements_L).

Ltac set_subseteq_to_list :=
  match goal with
  | |- ?s1 ⊆@{gset _} ?s2 =>
      let l1 := fresh "l" in
      let l2 := fresh "l" in
      let Hl1 := fresh "Hl" in
      let Hl2 := fresh "Hl" in
      let Hel1 := fresh "Hel" in
      let Hel2 := fresh "Hel" in
      set_to_list s1 l1 Hl1 Hel1;
      set_to_list s2 l2 Hl2 Hel2;
      vm_compute in Hel1;
      vm_compute in Hel2;
      rewrite <- Hl1, <- Hl2;
      apply RVPPREDl.list_to_set_subseteq;
      rewrite Hel1 Hel2
  end.

Ltac solve_elem_of :=
  repeat (try apply list_elem_of_here;
          try apply list_elem_of_further).

Ltac solve_list_subseteq :=
  repeat
    match goal with
    | |- []%list ⊆ ?l =>
        apply list_subseteq_nil
    | |- ?l1 ⊆ ?l2 =>
        apply list_subseteq_cons_iff
    | |- ?P ∧ ?q =>
        split
    | |- ?e ∈ ?l =>
        solve_elem_of
    end.

Ltac solve_subseteq :=
  set_subseteq_to_list;
  solve_list_subseteq.

Ltac reduce_big_sepS_big_sepL :=
  repeat
    match goal with
    | |- context[big_opS ?op ?f ?s] =>
        let l := fresh "l" in
        let Hl := fresh "Hl" in
        let Hel := fresh "Hel" in
        set_to_list s l Hl Hel;
        rewrite <- Hl;
        assert (Hdup : NoDup l) by (subst; apply NoDup_elements);
        rewrite (big_sepS_list_to_set _ _ Hdup);
        vm_compute in Hel;
        rewrite Hel
    end.

Transparent interp_pmp_entries.

(* Definitions and lemmas about the FemtoKernel that are shared by the
   integrity and the confidentiality verification. *)
Section Shared.
  Lemma big_sepL_filter `{BiAffine PROP} {A : Type} {l : list A}
      {φ : A → Prop} (dec : ∀ x, Decision (φ x)) (Φ : A -> PROP) :
    ([∗ list] x ∈ filter φ l, Φ x) ⊣⊢
    ([∗ list] x ∈ l, ⌜φ x⌝ -∗ Φ x).
  Proof. induction l.
    - now cbn.
    - cbn.
      destruct (decide (φ a)) as [Hφ|Hnφ].
      + rewrite big_opL_cons.
        rewrite <-IHl.
        iSplit; iIntros "[Ha Hl]"; iFrame; try done.
        now iApply ("Ha" $! Hφ).
      + rewrite <-IHl.
        iSplit.
        * iIntros "Hl"; iFrame; iIntros "%Hφ"; intuition.
        * iIntros "[Ha Hl]"; now iFrame.
  Qed.

  Definition femto_inv_mmio `{invGS Σ} `{mcMemGS2 Σ} : iProp Σ := interp_inv_mmio bytes_per_word.

  (* Import env.notations. *)

  (* Opaque interp_pmp_entries. *)

  (* (* Needed when introducing the below conditional *) *)
  (* Local Instance if_persistent `{sailGS Σ} (b : bool) (A B : iProp Σ) (P: Persistent A) (P' : Persistent B)  : Persistent (if b then A else B). *)
  (* Proof. destruct b; apply _. Qed. *)

  Definition ptsto_instrs_handler `{mcMemGS Σ} : iProp Σ :=
    RVPCOM.ptsto_instrs (bv.of_N handler_entry_addr) (filter_AST femtokernel_handler_entry) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_dispatch_addr) (filter_AST femtokernel_handler_dispatch) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_not_zero_addr) (filter_AST femtokernel_handler_not_zero) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_is_zero_addr) (filter_AST femtokernel_handler_is_zero) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_shutdown_check_addr) (filter_AST femtokernel_handler_shutdown_check) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_shutdown_addr) (filter_AST femtokernel_handler_shutdown) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_secret_write_addr) (filter_AST femtokernel_handler_secret_write) ∗
    RVPCOM.ptsto_instrs (bv.of_N handler_exit_addr) (filter_AST femtokernel_handler_exit).

  Local Opaque femtokernel_init_gen. (* TODO: figure out why not having this makes the below proof spin in two places *)

  Lemma intro_ptstomem_word `{mcMemGS Σ} v0 v1 v2 v3 (a : Val ty_word) :
    RVPCOM.interp_ptsto (bv.of_Z (0 + bv.unsigned a)) v0 ∗
    RVPCOM.interp_ptsto (bv.of_Z (1 + bv.unsigned a)) v1 ∗
    RVPCOM.interp_ptsto (bv.of_Z (2 + bv.unsigned a)) v2 ∗
    RVPCOM.interp_ptsto (bv.of_Z (3 + bv.unsigned a)) v3 ⊢
      RVPCOM.interp_ptstomem (width := 4) a (bv.app v0 (bv.app v1 (bv.app v2 (bv.app v3 bv.nil)))).
  Proof.
    iIntros "(Hmema & Hmema1 & Hmema2 & Hmema3)".
    unfold RVPCOM.interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z xlenbits (0 + bv.unsigned a)%Z) with a by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (1 + bv.unsigned a)%Z) with (bv.add bv.one a) by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace (@bv.of_Z xlenbits (2 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one a)).
    replace (@bv.of_Z xlenbits (3 + bv.unsigned a)%Z) with (bv.add bv.one (bv.add bv.one (bv.add bv.one a))).
    now iFrame.
    rewrite ?bv.add_assoc.
    change (bv.add _ bv.one) with (@bv.of_Z xlenbits 3).
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    rewrite ?bv.add_assoc.
    now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
  Qed.

  Lemma intro_ptstomem_word2 `{mcMemGS Σ} {μ : Memory} {a : Val ty_word} {v : Val ty_word} :
    mem_has_word μ a v ->
    ([∗ list] a' ∈ bv.seq a 4, RVPCOM.interp_ptsto a' ((memory_ram μ) a')) ⊢ RVPCOM.interp_ptstomem a v.
  Proof.
    iIntros (Hmhw) "Hmem".
    destruct Hmhw as (v0 & v1 & v2 & v3 & Heqμ & Heqv).
    unfold bv.seq, seqZ. change (seq 0 ?x) with [0;1;2;3]%nat%list.
    cbn -[bv.add RVPCOM.interp_ptstomem word].
    iDestruct "Hmem" as "(Hmema & Hmema1 & Hmema2 & Hmema3 & _)".
    inversion Heqμ; subst.
    now iApply (intro_ptstomem_word with "[$Hmema $Hmema1 $Hmema2 $Hmema3]").
  Qed.

  Lemma intro_ptsto_instr `{mcMemGS Σ} {μ : Memory} {a : Val ty_word} {instr : AST} :
    (4 + bv.unsigned a < 2 ^ Z.of_nat xlenbits)%Z ->
    mem_has_instr μ a instr ->
    ([∗ list] a' ∈ bv.seq a 4, RVPCOM.interp_ptsto a' ((memory_ram μ) a'))
      ⊢ RVPCOM.interp_ptsto_instr a instr.
  Proof.
    iIntros (Hrep (v & Hmhw & Heq)) "Hmem".
    iExists v.
    iSplitL; last done.
    now iApply (intro_ptstomem_word2 Hmhw).
  Qed.

  Lemma intro_ptsto_instrs `{mcMemGS Σ} {μ : Memory} {a : Val ty_word} {instrs : list AST} :
    (4 * Z.of_nat (length instrs) + bv.unsigned a < 2 ^ Z.of_nat xlenbits)%Z ->
    mem_has_instrs μ a instrs ->
    ([∗ list] a' ∈ bv.seq a (4 * Z.of_nat (length instrs)), RVPCOM.interp_ptsto a' ((memory_ram μ) a'))
      ⊢ RVPCOM.ptsto_instrs a instrs.
  Proof.
    assert (word > 0) by now compute.
    iIntros (Hrep Hmeminstrs) "Hmem".
    iInduction instrs as [|instr instrs] "IH" forall (a Hrep Hmeminstrs).
    - done.
    - replace (4 * Z.of_nat (length (instr :: instrs)))%Z
        with (4 + 4 * Z.of_nat (length instrs))%Z in * by (cbn; lia).
      rewrite bv.seq_add ?big_opL_app; [|lia..].
      destruct Hmeminstrs as [Hinstr Hmeminstrs].
      iDestruct "Hmem" as "[Hmema Hmema4]".
      iSplitL "Hmema".
      + iApply (intro_ptsto_instr with "Hmema"); auto; Lia.lia.
      + rewrite (@bv.add_comm _ a bv_instrsize).
        iApply ("IH" with "[%] [% //] [-]"); last done.
        pose proof (bv.unsigned_bounds a). change word with xlenbits in *.
        rewrite -bv.unsigned_add_small; change (bv.unsigned (bv.of_N 4)) with 4%Z; lia.
  Qed.

  Lemma intro_ptstoSthL `{mcMemGS Σ} (μ : Memory) (addrs : list Xlenbits)  :
    ([∗ list] a' ∈ addrs, RVPCOM.interp_ptsto a' ((memory_ram μ) a')) ⊢ RVPCOM.ptstoSthL addrs.
  Proof.
    induction addrs as [|a l]; cbn.
    - now iIntros "_".
    - iIntros "[Hmema Hmem]".
      iSplitL "Hmema".
      + now iExists ((memory_ram μ) a).
      + now iApply IHl.
  Qed.

  Lemma sub_heap_mapsto_interp_ptsto `{mcMemGS Σ} {s e} (μ : Memory):
    (Z.of_N minAddr <= bv.unsigned s)%Z → (bv.unsigned s + e <= Z.of_N (minAddr + lenAddr))%Z →
    ([∗ list] y ∈ bv.seq s e, gen_heap.pointsto y (dfrac.DfracOwn 1) (memory_ram μ y)) ⊢ [∗ list] a' ∈ bv.seq s e, RVPCOM.interp_ptsto a' (memory_ram μ a').
  Proof.
    iIntros (Hlow Hhi) "Hlist".
    iApply (big_sepL_mono with "Hlist"). intros ? ? Hsom. cbn.
    iIntros "$". iPureIntro.
    rewrite /= withinMMIO_one /not; apply mmio_ram_False.
    eapply bv.seq_subseteq, list_elem_of_lookup_2, Hsom;
      change (bv.unsigned (bv.of_N minAddr)) with (Z.of_N minAddr); lia.
  Qed.

  Lemma femtokernel_splitMemory {Σ} {mG : mcMemGS Σ} {μ : Memory} (secret : Val ty_xlenbits) :
    mem_has_femtokernel μ secret ->
    ([∗ list] a' ∈ liveAddrs, gen_heap.pointsto a' (dfrac.DfracOwn 1) (memory_ram μ a')) ⊢
      RVPCOM.ptsto_instrs (bv.of_N init_addr) (filter_AST femtokernel_init_gen) ∗
      ptsto_instrs_handler ∗
      RVPCOM.interp_ptstomem (bv.of_N data_addr) secret ∗
      [∗ list] a ∈ advAddrs, RVPCOM.interp_ptsto a (memory_ram μ a).
  Proof.
    iIntros ((Hinit & Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit & Hdata)) "Hmem".
    rewrite liveAddrs_split.
    iDestruct "Hmem" as "(Hinit & Hhandler & Hdata & Hadv)".
    iSplitL "Hinit".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hinit"); now compute. }
    iSplitL "Hhandler". (* Need to solve the goal for both handlers *)
    { unfold ptsto_instrs_handler.
      rewrite handlerAddrs_split.
      iDestruct "Hhandler" as "(Hhentry & Hhdispatch & Hhnotzero & Hhiszero & Hhcheck & Hhshutdown & Hhsecret & Hhexit)".
      iSplitL "Hhentry".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhentry"); now compute. }
      iSplitL "Hhdispatch".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhdispatch"); now compute. }
      iSplitL "Hhnotzero".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhnotzero"); now compute. }
      iSplitL "Hhiszero".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhiszero"); now compute. }
      iSplitL "Hhcheck".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhcheck"); now compute. }
      iSplitL "Hhshutdown".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhshutdown"); now compute. }
      iSplitL "Hhsecret".
      { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
        iApply (sub_heap_mapsto_interp_ptsto with "Hhsecret"); now compute. }
      iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hhexit"); now compute. }
    iSplitL "Hdata".
    { iApply (intro_ptstomem_word2 Hdata).
      iApply (sub_heap_mapsto_interp_ptsto with "Hdata"); now compute. }
    iApply (sub_heap_mapsto_interp_ptsto with "Hadv"); now compute.
  Qed.

  Definition UnaryPredicateDefIProp__l {Σ} (sG : RVPBASEl.sailGS Σ) :=
    @RVPINSTl.PredicateDefIProp _ sG Instance.trivTrivGS.
  Definition UnaryPredicateDefIProp__r {Σ} (sG : RVPBASEr.sailGS Σ) :=
    @RVPINSTr.PredicateDefIProp _ sG Instance.trivTrivGS.

  (* The architectural state with which the femtokernel hands control to the
     adversary (or traps back): M-mode state is fixed by the kernel, except
     for the parts that the adversary can influence. *)
  Definition femto_archstate (priv : Privilege) (ms : ArchState.MState) (ss : ArchState.SState) (pc : Xlenbits) : ArchState :=
    {| ArchState.m := priv;
       ArchState.mstate :=
         {| ArchState.mtvec      := bv.of_N handler_entry_addr;
            ArchState.pmpentries := femto_pmpentries;
            ArchState.mpp        := ArchState.mpp ms;
            ArchState.mcause     := ArchState.mcause ms;
            ArchState.mscratch   := ArchState.mscratch ms;
            ArchState.mepc       := ArchState.mepc ms;
            ArchState.mpie       := ArchState.mpie ms;
            ArchState.mie        := ArchState.mie ms;
            ArchState.mideleg    := Minterrupts_zero;
            ArchState.medeleg    := Medeleg_zero |};
       ArchState.sstate := ss;
       ArchState.pc := pc |}.

  (* The architectural state with which the handler returns to the
     adversary: the pc is the address the handler returns to, everything else
     is fixed by the handler pre- and postconditions. *)
  Definition femto_return_archstate (archstate : ArchState) (vmscratch : Val ty_xlenbits) (an : Val ty_xlenbits) : ArchState :=
    femto_archstate (ArchState.mpp (ArchState.mstate archstate))
      {| ArchState.mtvec      := bv.of_N handler_entry_addr;
         ArchState.pmpentries := femto_pmpentries;
         ArchState.mpp        := User;
         ArchState.mcause     := ArchState.mcause (ArchState.mstate archstate);
         ArchState.mscratch   := vmscratch;
         ArchState.mepc       := ArchState.mepc (ArchState.mstate archstate);
         ArchState.mpie       := true;
         ArchState.mie        := ArchState.mpie (ArchState.mstate archstate);
         ArchState.mideleg    := Minterrupts_zero;
         ArchState.medeleg    := Medeleg_zero |}
      (ArchState.sstate archstate)
      an.

  (* The architectural state on entry of the trap handler, after a trap from
     S- or U-mode. *)
  Definition femto_handler_archstate (mpp : Privilege) (mpie : bool) (mcause mscratch mepc : Xlenbits)
    (ss : ArchState.SState) : ArchState :=
    {| ArchState.m      := Machine;
       ArchState.mstate :=
         {| ArchState.mtvec      := bv.of_N handler_entry_addr;
            ArchState.pmpentries := femto_pmpentries;
            ArchState.mpp        := mpp;
            ArchState.mpie       := mpie;
            ArchState.mie        := false;
            ArchState.mcause     := mcause;
            ArchState.mscratch   := mscratch;
            ArchState.mepc       := mepc;
            ArchState.mideleg    := Minterrupts_zero;
            ArchState.medeleg    := Medeleg_zero |};
       ArchState.sstate := ss;
       ArchState.pc     := bv.of_N handler_entry_addr |}.

  (* The architectural state with which the femtokernel first hands control
     to the adversary, after its initialization. *)
  Definition femto_adv_archstate (mpp : Privilege) (mpie mie : bool) (mcause mscratch mepc : Xlenbits)
    (stvec scause sscratch sepc : Xlenbits) : ArchState :=
    femto_archstate User
      (ArchState.mkMState (bv.of_N handler_entry_addr) femto_pmpentries mpp mpie mie
         mcause mscratch mepc Minterrupts_zero Medeleg_zero)
      (ArchState.mkSState stvec (MkSstatus User false false) scause sscratch sepc)
      (bv.of_N adv_addr).

  (* The architectural state in which the femtokernel starts executing. *)
  Definition femto_init_archstate (γ : RegStore) : ArchState :=
    {| ArchState.m      := Machine;
       ArchState.mstate :=
         {| ArchState.mtvec      := read_register γ mtvec;
            ArchState.pmpentries := [(default_pmpcfg_ent, bv.zero); (default_pmpcfg_ent, bv.zero)];
            ArchState.mpp        := User;
            ArchState.mpie       := false;
            ArchState.mie        := false;
            ArchState.mcause     := read_register γ mcause;
            ArchState.mscratch   := read_register γ mscratch;
            ArchState.mepc       := read_register γ mepc;
            ArchState.mideleg    := Minterrupts_zero;
            ArchState.medeleg    := Medeleg_zero |};
       ArchState.sstate :=
         {| ArchState.stvec    := read_register γ stvec;
            ArchState.sstatus  := MkSstatus User false false;
            ArchState.scause   := read_register γ scause;
            ArchState.sscratch := read_register γ sscratch;
            ArchState.sepc     := read_register γ sepc |};
       ArchState.pc     := bv.of_N init_addr |}.
End Shared.
