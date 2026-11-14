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
     Lists.List
     Strings.String
     ZArith.ZArith
     micromega.Lia.
From Katamaran Require Import
     Notations
     Context
     Bitvector
     Environment
     Sep.Hoare
     Symbolic.Solver
     Symbolic.Propositions
     Symbolic.Worlds
     MicroSail.ShallowExecutor
     MicroSail.SymbolicExecutor
     RiscvPmp.Logic
     RiscvPmp.PmpCheck
     RiscvPmp.Machine
     RiscvPmp.Sig.
From Equations Require Import
     Equations.
From stdpp Require Import
     base.

Import RiscvPmpProgram.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import bv.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

(* NOTE: same as for mincaps, avoid Lemma in definition body for coqwc *)
Definition KatamaranLem := Lemma.

Module Import RiscvPmpSpecification.

  Import RiscvPmpProgramLogic.

    Section ContractDefKit.
      Import asn.notations.
      Import rv_notations.
      Local Notation "a <ᵘₜ b" := (term_binop (bop.relop bop.bvult) a b) (at level 60).
      Local Notation "a <=ᵘₜ b" := (term_binop (bop.relop bop.bvule) a b) (at level 60).
      Local Notation "a &&ₜ b" := (term_binop bop.and a b) (at level 80).
      Local Notation "a ||ₜ b" := (term_binop bop.or a b) (at level 85).
      Local Notation "e1 ',ₜ' e2" := (term_binop bop.pair e1 e2) (at level 100).

      (* Shadow the definition of asn_regs_ptsto that takes an "exclude list",
         we never use it for the Universal Contract verification. *)
      Definition asn_regs_ptsto {Σ} : Assertion Σ := asn_regs_ptsto ∅.

      Section ContractDef.
        Import RiscvNotations.
        Import RiscvPmpSignature.notations.
        Import RiscvPmpSignature.ContractNotations.

        (** Machine Invariant **)
        (* TODO: - this should work for the execute{,_/x/} functions, but step and loop will update
                   the pc, so this should be reflected in their contract (2nd pc(i) -> pc(i + 4)?)



           TODO: short notation out of sync with actual contract
           @pre ∀ m h i . mode(m) ∗ mtvec(h) ∗ pmp_entries(ents) ∗ pc(i) ∗ mepc(_) ∗ mpp(_)
           @post pmp_entries(ents) ∗ (mode(m) ∗ pc(i)) ∨ (mode(M) ∗ pc(h) ...)
           τ f(Δ...)*)
        Definition instr_exec_contract {τ Δ} : SepContract Δ τ :=
          let Σ := ["m" :: ty_privilege; "mtvec" :: ty_xlenbits; "stvec" :: ty_xlenbits; "pc" :: ty_xlenbits; "pmpentries" :: ty.list ty_pmpentry; "mpp" :: ty_privilege; "spp" :: ty_privilege; "mepc" :: ty_xlenbits; "sepc" :: ty_xlenbits; "npc" :: ty_xlenbits; "mpie" :: ty.bool; "spie" :: ty.bool; "mie" :: ty.bool; "sie" :: ty.bool; "sscratch" :: ty_xlenbits; "mscratch" :: ty_xlenbits; "mcause" :: ty_xlenbits; "scause" :: ty_xlenbits; "vmip" :: ty_Minterrupts; "vmie" :: ty_Minterrupts; "mideleg" :: ty_Minterrupts; "medeleg" :: ty_Medeleg] in
          {| sep_contract_logic_variables := sep_contract_logvars Δ Σ;
             sep_contract_localstore      := create_localstore Δ Σ;
             sep_contract_precondition    :=
                           (* Need to force destruct of m, otherwise the execute_CSR verification will be stuck,
                              with the remaining goal simply proceeding by doing this destruct... *)
                           asn.match_enum privilege (term_var "m") (fun _ => ⊤) ∗
                           cur_privilege ↦ term_var "m" ∗
                           mtvec         ↦ term_var "mtvec" ∗
                           stvec         ↦ term_var "stvec" ∗
                           sscratch ↦ term_var "sscratch" ∗
                           pc            ↦ term_var "pc" ∗
                           nextpc        ↦ term_var "npc" ∗
                           mscratch ↦ term_var "mscratch" ∗
                           mepc          ↦ term_var "mepc" ∗
                           sepc          ↦ term_var "sepc" ∗
                           mideleg       ↦ term_var "mideleg" ∗
                           medeleg       ↦ term_var "medeleg" ∗
                           mcause        ↦ term_var "mcause" ∗
                           scause        ↦ term_var "scause" ∗
                           mip ↦ term_var "vmip" ∗
                           mie ↦ term_var "vmie" ∗
                           mstatus       ↦ term_record rmstatus [nenv term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ] ∗
                           asn_pmp_entries (term_var "pmpentries") ∗
                           asn_pmp_addr_access (term_var "pmpentries") (term_var "m") ∗
                           asn_gprs;
             sep_contract_result          := "result_mach_inv";
             sep_contract_postcondition   :=
                           asn_pmp_addr_access (term_var "pmpentries") (term_var "m") ∗
                           asn_gprs ∗
                           pc     ↦ term_var "pc" ∗
               ∃ "mip", mip ↦ term_var "mip" ∗
               ∃ "mie", mie ↦ term_var "mie" ∗
               (  (* Executing normally *)
                       asn_pmp_entries (term_var "pmpentries") ∗
                  ∃ v, nextpc        ↦ term_var v ∗
                       mtvec         ↦ term_var "mtvec" ∗
                       mepc          ↦ term_var "mepc" ∗
                       mideleg       ↦ term_var "mideleg" ∗
                       medeleg       ↦ term_var "medeleg" ∗
                       mscratch      ↦ term_var "mscratch" ∗
                       mcause        ↦ term_var "mcause" ∗
                  (  (* Executing normally in M-mode. Nothing changes, no transitions, those are handled by the other disjuncts, so we rule them out here. *)
                                 term_var "m" = term_val ty_privilege Machine ∗
                                 cur_privilege ↦ term_val ty_privilege Machine ∗
                                 stvec         ↦ term_var "stvec" ∗
                                 mstatus       ↦ term_record rmstatus [nenv term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ] ∗
                                 sepc          ↦ term_var "sepc" ∗
                                 sscratch      ↦ term_var "sscratch" ∗
                                 scause        ↦ term_var "scause"
                   ∨
                     (* Executing normally in U/S-mode. We do allow Supervisor accessible CSRs to be modified here. *)
                                 term_var "m" != term_val ty_privilege Machine ∗
                    asn.exist "new_m" ty_privilege (
                                 cur_privilege ↦ term_var "new_m" ∗
                                 term_var "new_m" != term_val ty_privilege Machine ∗
                    ∃ "new_stvec", stvec       ↦ term_var "new_stvec" ∗
                    ∃ "new_spp", ∃ "new_spie", ∃ "new_sie",
                                 mstatus       ↦ term_record rmstatus [nenv term_var "mpp"; term_var "new_spp"; term_var "mpie"; term_var "new_spie"; term_var "mie"; term_var "new_sie" ] ∗
                    ∃ "new_sepc", sepc         ↦ term_var "new_sepc" ∗
                    ∃ "new_sscratch", sscratch ↦ term_var "new_sscratch" ∗
                    ∃ "new_scause", scause     ↦ term_var "new_scause"))
                ∨
                  (* Modified CSRs, Machine mode case (access to all CSRs) *)
                                 term_var "m"  =  term_val ty_privilege Machine ∗
                  ∃ "new_pmpentries",   asn_pmp_entries (term_var "new_pmpentries") ∗
                                 cur_privilege ↦ term_val ty_privilege Machine ∗
                                 nextpc        ↦ term_var "npc" ∗
                  ∃ "new_mtvec", mtvec         ↦ term_var "new_mtvec" ∗
                  ∃ "new_stvec", stvec         ↦ term_var "new_stvec" ∗
                  ∃ "new_mpp", ∃ "new_spp", ∃ "new_mpie", ∃ "new_spie", ∃ "new_mie", ∃ "new_sie",
                    mstatus       ↦ term_record rmstatus [nenv term_var "new_mpp"; term_var "new_spp"; term_var "new_mpie"; term_var "new_spie"; term_var "new_mie"; term_var "new_sie" ] ∗
                  ∃ "new_mepc",  mepc          ↦ term_var "new_mepc" ∗
                  ∃ "new_sepc",  sepc          ↦ term_var "new_sepc" ∗
                  ∃ "new_mideleg", mideleg ↦ term_var "new_mideleg" ∗
                  ∃ "new_medeleg", medeleg ↦ term_var "new_medeleg" ∗
                  ∃ "new_mscratch", mscratch ↦ term_var "new_mscratch" ∗
                  ∃ "new_mcause", mcause ↦ term_var "new_mcause" ∗
                  ∃ "new_sscratch", sscratch ↦ term_var "new_sscratch" ∗
                  ∃ "new_scause", scause ↦ term_var "new_scause"
                ∨
                  (* Trap occured -> Go into M-mode *)
                  asn_pmp_entries (term_var "pmpentries") ∗
                  cur_privilege ↦ (term_val ty_privilege Machine) ∗
                  nextpc        ↦ term_var "mtvec" ∗
                  mtvec         ↦ term_var "mtvec" ∗
                  ∃ "new_stvec", stvec ↦ term_var "new_stvec" ∗
                  ∃ "new_spp", ∃ "mpie", ∃ "new_spie", ∃ "new_sie",
                    asn.match_enum privilege (term_var "m")
                    (fun K => match K with
                              (* Trap from M-mode: MPP is M-mode (reentrant trap M->M) *)
                              | Machine =>
                                mstatus ↦ term_record rmstatus [nenv term_val ty_privilege Machine; term_var "new_spp"; term_var "mpie"; term_var "new_spie"; term_val ty.bool false; term_var "new_sie" ]
                              (* Trap from S/U-mode: MPP is some S/U privilege level *)
                              | _       => ∃ "new_mpp", (
                                mstatus ↦ term_record rmstatus [nenv term_var "new_mpp"; term_var "new_spp"; term_var "mpie"; term_var "new_spie"; term_val ty.bool false; term_var "new_sie" ] ∗
                                term_var "new_mpp" != term_val ty_privilege Machine)
                              end) ∗
                  ∃ "mepc", mepc          ↦ term_var "mepc" ∗
                  ∃ "new_sepc", sepc ↦ term_var "new_sepc" ∗
                  mideleg ↦ term_var "mideleg" ∗
                  medeleg ↦ term_var "medeleg" ∗
                  ∃ "mscratch", mscratch ↦ term_var "mscratch" ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                  ∃ "new_sscratch", sscratch ↦ term_var "new_sscratch" ∗
                  ∃ "scause", scause ↦ term_var "scause"
                ∨
                  (* MRET = Recover *)
                  asn_pmp_entries (term_var "pmpentries") ∗
                  term_var "m"  =  term_val ty_privilege Machine ∗
                  cur_privilege ↦ term_var "mpp" ∗
                  nextpc        ↦ term_var "mepc" ∗
                  mtvec         ↦ term_var "mtvec" ∗
                  stvec         ↦ term_var "stvec" ∗
                  ∃ "mie",
                  mstatus       ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "spp"; term_val ty.bool true ; term_var "spie"; term_var "mie"; term_var "sie" ] ∗
                  mepc          ↦ term_var "mepc" ∗
                  sepc          ↦ term_var "sepc" ∗
                  mideleg       ↦ term_var "mideleg" ∗
                  medeleg       ↦ term_var "medeleg" ∗
                  ∃ "mscratch", mscratch ↦ term_var "mscratch" ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                  ∃ "sscratch", sscratch ↦ term_var "sscratch" ∗
                  ∃ "scause", scause ↦ term_var "scause"
                ∨
                  (* SRET = Recover *)
                  asn_pmp_entries (term_var "pmpentries") ∗
                  term_var "m" = term_val ty_privilege Machine ∗
                  cur_privilege ↦ term_var "spp" ∗
                  nextpc        ↦ term_var "sepc" ∗
                  mtvec         ↦ term_var "mtvec" ∗
                  stvec         ↦ term_var "stvec" ∗
                  ∃ "sie",
                  mstatus       ↦ term_record rmstatus [nenv term_var "mpp"; term_val ty_privilege User; term_var "mpie"; term_val ty.bool true; term_var "mie"; term_var "sie" ] ∗
                  mepc          ↦ term_var "mepc" ∗
                  sepc          ↦ term_var "sepc" ∗
                  mideleg       ↦ term_var "mideleg" ∗
                  medeleg       ↦ term_var "medeleg" ∗
                  ∃ "mscratch", mscratch ↦ term_var "mscratch" ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                  ∃ "sscratch", sscratch ↦ term_var "sscratch" ∗
                  ∃ "scause", scause ↦ term_var "scause")
          |}.

        Definition sep_contract_execute_RTYPE : SepContractFun execute_RTYPE :=
          instr_exec_contract.

        Definition sep_contract_execute_MUL : SepContractFun execute_MUL :=
          instr_exec_contract.

        Definition sep_contract_execute_ILLEGAL : SepContractFun execute_ILLEGAL :=
          instr_exec_contract.

        Definition sep_contract_execute_ITYPE : SepContractFun execute_ITYPE :=
          instr_exec_contract.

        Definition sep_contract_execute_SHIFTIOP : SepContractFun execute_SHIFTIOP :=
          instr_exec_contract.

        Definition sep_contract_execute_UTYPE : SepContractFun execute_UTYPE :=
          instr_exec_contract.

        Definition sep_contract_execute_BTYPE : SepContractFun execute_BTYPE :=
          instr_exec_contract.

        Definition sep_contract_execute_RISCV_JAL : SepContractFun execute_RISCV_JAL :=
          instr_exec_contract.

        Definition sep_contract_execute_RISCV_JALR : SepContractFun execute_RISCV_JALR :=
          instr_exec_contract.

        Definition sep_contract_execute_ECALL : SepContractFun execute_ECALL :=
          instr_exec_contract.

        Definition sep_contract_execute_EBREAK : SepContractFun execute_EBREAK :=
          {{ ⊤ }}
            fn execute_EBREAK [] ty_retired
          {{ "result_execute_EBREAK", ⊤ }}.

        Definition sep_contract_execute_SRET : SepContractFun execute_SRET :=
          instr_exec_contract.

        Definition sep_contract_execute_MRET : SepContractFun execute_MRET :=
          instr_exec_contract.

        Definition sep_contract_execute_CSR : SepContractFun execute_CSR :=
          instr_exec_contract.

        Definition sep_contract_execute_STORE : SepContractFun execute_STORE :=
          instr_exec_contract.

        Definition sep_contract_execute_LOAD : SepContractFun execute_LOAD :=
          instr_exec_contract.

        Definition sep_contract_execute : SepContractFun execute :=
          instr_exec_contract.

        Definition sep_contract_readCSR : SepContractFun readCSR :=
          {{ mstatus ↦ term_record rmstatus [nenv term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ]
             ∗ mtvec ↦ term_var "mtvec"
             ∗ mscratch ↦ term_var "mscratch"
             ∗ mepc ↦ term_var "mepc"
             ∗ mip ↦ term_var "vmip"
             ∗ mie ↦ term_var "vmie"
             ∗ mideleg ↦ term_var "mideleg"
             ∗ medeleg ↦ term_var "medeleg"
             ∗ mcause ↦ term_var "mcause"
             ∗ pmp0cfg ↦ term_var "cfg0"
             ∗ pmp1cfg ↦ term_var "cfg1"
             ∗ pmpaddr0 ↦ term_var "addr0"
             ∗ pmpaddr1 ↦ term_var "addr1"
             ∗ stvec ↦ term_var "stvec"
             ∗ sscratch ↦ term_var "sscratch"
             ∗ sepc ↦ term_var "sepc"
             ∗ scause ↦ term_var "scause" }}
            fn readCSR [csr :: ty_csridx] ty_xlenbits
          {{ "result_readCSR",
             ∃ "result", term_var "result_readCSR" = term_var "result"
             ∗ mstatus ↦ term_record rmstatus [term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ]
             ∗ mtvec ↦ term_var "mtvec"
             ∗ mscratch ↦ term_var "mscratch"
             ∗ mepc ↦ term_var "mepc"
             ∗ mip ↦ term_var "vmip"
             ∗ mie ↦ term_var "vmie"
             ∗ mideleg ↦ term_var "mideleg"
             ∗ medeleg ↦ term_var "medeleg"
             ∗ mcause ↦ term_var "mcause"
             ∗ pmp0cfg ↦ term_var "cfg0"
             ∗ pmp1cfg ↦ term_var "cfg1"
             ∗ pmpaddr0 ↦ term_var "addr0"
             ∗ pmpaddr1 ↦ term_var "addr1"
             ∗ stvec ↦ term_var "stvec"
             ∗ sscratch ↦ term_var "sscratch"
             ∗ sepc ↦ term_var "sepc"
             ∗ scause ↦ term_var "scause" }}
          with ["mpp" :: ty_privilege; "mtvec" :: ty_xlenbits; "mcause" :: ty_mcause;
                "mepc" :: ty_xlenbits; "cfg0" :: ty_pmpcfg_ent; "cfg1" :: ty_pmpcfg_ent;
                "addr0" :: ty_xlenbits; "addr1" :: ty_xlenbits; "spp" :: ty_privilege;
                "stvec" :: ty_xlenbits; "sepc" :: ty_xlenbits; "scause" :: ty_xlenbits;
                "mpie" :: ty.bool; "spie" :: ty.bool; "mie" :: ty.bool; "sie" :: ty.bool;
                "mscratch" :: ty_xlenbits; "vmip" :: ty_Minterrupts; "vmie" :: ty_Minterrupts;
                "sscratch" :: ty_xlenbits; "mideleg" :: ty_Minterrupts; "medeleg" :: ty_Medeleg].

        Definition sep_contract_writeCSR : SepContractFun writeCSR :=
          (* The logic vars contain a few bindings that we use as read-only (ro)
             binders, to ensure certain regs/fields cannot be modified. *)
          let Σ := [csr :: ty_csridx; value :: ty_xlenbits; "ro_cfg" :: ty_pmpcfg_ent; "ro_mpp" :: ty_privilege; "ro_mie" :: ty.bool; "ro_mpie" :: ty.bool; "ro_mideleg" :: ty_Minterrupts] in
          (* We declare default bindings for the "ro" (read-only) logic vars when
             they are not used in the resulting assertion from csr_ptsto. Each
             case in that function is accompanied with some defaults assertion
             (all, ro_cfg, ro_m), this ensures we do not end up with needless
             existentials in the postcondition when using this contract to
             verify other functions. *)
          let default_ro_cfg : Assertion Σ := term_var "ro_cfg" = term_val ty_pmpcfg_ent default_pmpcfg_ent in
          let default_ro_m : Assertion Σ :=
            term_var "ro_mpp"  = term_val ty_privilege User ∗
            term_var "ro_mie"  = term_val ty.bool false ∗
            term_var "ro_mpie" = term_val ty.bool false in
          let default_ro_mideleg : Assertion Σ := term_var "ro_mideleg" = term_val ty_Minterrupts Minterrupts_zero in
          let all_defaults : Assertion Σ := default_ro_cfg ∗ default_ro_m ∗ default_ro_mideleg in
          (* csr_ptsto returns the assertion needed for a write to a specific csr *)
          let csr_ptsto (csr_param : CSRIdx) : Assertion Σ :=
            match csr_param in CSRIdx with
            | MStatus   => ∃ "mpp", ∃ "spp", ∃ "mpie", ∃ "spie", ∃ "mie", ∃ "sie",
                             mstatus ↦ term_record rmstatus [term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie"]
                             ∗ all_defaults
            | Mie       => ∃ "v", mie ↦ term_var "v" ∗ all_defaults
            | MTvec     => ∃ "v", mtvec ↦ term_var "v" ∗ all_defaults
            | MScratch  => ∃ "v", mscratch ↦ term_var "v" ∗ all_defaults
            | MEpc      => ∃ "v", mepc ↦ term_var "v" ∗ all_defaults
            | MCause    => ∃ "v", mcause ↦ term_var "v" ∗ all_defaults
            | Mideleg   => ∃ "v", mideleg ↦ term_var "v" ∗ all_defaults
            | Medeleg   => ∃ "v", medeleg ↦ term_var "v" ∗ all_defaults
            | MPMP0CFG  => ∃ "v", (pmp0cfg ↦ term_var "v" ∗ asn_expand_pmpcfg_ent (term_var "v"))
                          ∗ ∃ "v", (pmp1cfg ↦ term_var "v" ∗ asn_expand_pmpcfg_ent (term_var "v"))
                          ∗ all_defaults
            | Mip       => ∃ "v", mip ↦ term_var "v" ∗ all_defaults
            | MPMPADDR0 =>
                pmp0cfg ↦ term_var "ro_cfg" ∗ asn_expand_pmpcfg_ent (term_var "ro_cfg")
                ∗ ∃ "v", pmpaddr0 ↦ term_var "v" ∗ default_ro_m ∗ default_ro_mideleg
            | MPMPADDR1 =>
                pmp1cfg ↦ term_var "ro_cfg" ∗ asn_expand_pmpcfg_ent (term_var "ro_cfg")
                ∗ ∃ "v", pmpaddr1 ↦ term_var "v" ∗ default_ro_m ∗ default_ro_mideleg
            | SStatus   =>
                ∃ "v", ∃ "spie", ∃ "sie",  mstatus ↦ term_record rmstatus [term_var "ro_mpp"; term_var "v"; term_var "ro_mpie"; term_var "spie"; term_var "ro_mie"; term_var "sie"]
                ∗ default_ro_cfg ∗ default_ro_mideleg
            | STvec     => ∃ "v", stvec ↦ term_var "v" ∗ all_defaults
            | SScratch  => ∃ "v", sscratch ↦ term_var "v" ∗ all_defaults
            | SEpc      => ∃ "v", sepc ↦ term_var "v" ∗ all_defaults
            | SCause    => ∃ "v", scause ↦ term_var "v" ∗ all_defaults
            (* The two cases below are not very precise, since, similar to sstatus,
               S-mode is only allowed to modify a handful of bits of the mip and mie
               registers (which also depends on some bits of mideleg!). *)
            | Sip       => mideleg ↦ term_var "ro_mideleg" ∗ ∃ "v", mip ↦ term_var "v" ∗ default_ro_cfg ∗ default_ro_m
            | Sie       => mideleg ↦ term_var "ro_mideleg" ∗ ∃ "v", mie ↦ term_var "v" ∗ default_ro_cfg ∗ default_ro_m
            end in
          {{ asn.match_enum csridx (term_var csr) csr_ptsto }}
            fn writeCSR [csr :: ty_csridx; value :: ty_xlenbits] ty.unit
          {{ "result_writeCSR",
             term_var "result_writeCSR" = term_val ty.unit tt
             ∗ asn.sub_assertion (asn.match_enum csridx (term_var csr) csr_ptsto) sub_wk1 }}
          with ["ro_cfg" :: ty_pmpcfg_ent; "ro_mpp" :: ty_privilege; "ro_mie" :: ty.bool;
                "ro_mpie" :: ty.bool; "ro_mideleg" :: ty_Minterrupts].

        Definition sep_contract_check_CSR : SepContractFun check_CSR :=
          {{ ⊤ }}
            fn check_CSR [csr :: ty_csridx; p :: ty_privilege] ty.bool
          {{ "result_check_CSR", ⊤ }}.

        Definition sep_contract_is_CSR_defined : SepContractFun is_CSR_defined :=
          let Σ := ["csr"∷ty_csridx; "p"∷ty_privilege] in
          {{ (* TODO: bit ugly, this is just saying "destruct p", comment this line out and check the valid_contract_is_CSR_defined proof (change it into a Debug contract), we'll be stuck with lots of equalities... *)
             asn.match_enum privilege (term_var p) (fun _ => ⊤) }}
            fn is_CSR_defined [csr :: ty_csridx; p :: ty_privilege] ty.bool
          {{ "result_is_CSR_defined",
              asn.match_enum csridx (term_var csr)
                (fun K => let req_priv : Term Σ ty.bool :=
                            match K with
                            | MStatus   => term_eq (term_var p) (term_val ty_privilege Machine)
                            | Mie       => term_eq (term_var p) (term_val ty_privilege Machine)
                            | Mip       => term_eq (term_var p) (term_val ty_privilege Machine)
                            | MTvec     => term_eq (term_var p) (term_val ty_privilege Machine)
                            | MScratch  => term_eq (term_var p) (term_val ty_privilege Machine)
                            | MEpc      => term_eq (term_var p) (term_val ty_privilege Machine)
                            | MCause    => term_eq (term_var p) (term_val ty_privilege Machine)
                            | Mideleg   => term_eq (term_var p) (term_val ty_privilege Machine)
                            | Medeleg   => term_eq (term_var p) (term_val ty_privilege Machine)
                            | MPMP0CFG  => term_eq (term_var p) (term_val ty_privilege Machine)
                            | MPMPADDR0 => term_eq (term_var p) (term_val ty_privilege Machine)
                            | MPMPADDR1 => term_or (term_eq (term_var p) (term_val ty_privilege Machine)) (term_val ty.bool false)
                            | SStatus   => term_or (term_eq (term_var p) (term_val ty_privilege Machine))
                                                   (term_eq (term_var p) (term_val ty_privilege Supervisor))
                            | STvec     => term_or (term_eq (term_var p) (term_val ty_privilege Machine))
                                                   (term_eq (term_var p) (term_val ty_privilege Supervisor))
                            | SScratch  => term_or (term_eq (term_var p) (term_val ty_privilege Machine))
                                                   (term_eq (term_var p) (term_val ty_privilege Supervisor))
                            | SEpc      => term_or (term_eq (term_var p) (term_val ty_privilege Machine))
                                                   (term_eq (term_var p) (term_val ty_privilege Supervisor))
                            | SCause    => term_or (term_eq (term_var p) (term_val ty_privilege Machine))
                                                   (term_eq (term_var p) (term_val ty_privilege Supervisor))
                            | Sip       => term_or (term_eq (term_var p) (term_val ty_privilege Machine))
                                                   (term_eq (term_var p) (term_val ty_privilege Supervisor))
                            | Sie       => term_or (term_eq (term_var p) (term_val ty_privilege Machine))
                                                   (term_eq (term_var p) (term_val ty_privilege Supervisor))
                            end in
                          let req_priv : Term (Σ ▻ "result_is_CSR_defined" ∷ ty.bool) ty.bool := sub_term req_priv sub_wk1 in
                          term_var "result_is_CSR_defined" = req_priv) }}.

        Definition sep_contract_check_CSR_access : SepContractFun check_CSR_access :=
          {{ ⊤ }}
            fn check_CSR_access [csrrw :: ty_access_type; csrpr :: ty_privilege; p :: ty_privilege] ty.bool
          {{ "result_check_CSR_access",
             asn.match_enum privilege (term_var csrpr)
             (fun K => match K with
                       | Machine =>
                           asn.match_enum privilege (term_var p)
                             (fun K => match K with
                                       | Machine => term_var "result_check_CSR_access" =
                                                      term_val ty.bool true
                                       | _       => term_var "result_check_CSR_access" =
                                                      term_val ty.bool false
                                       end)
                       | Supervisor =>
                           asn.match_enum privilege (term_var p)
                             (fun K => match K with
                                       | Machine    => term_var "result_check_CSR_access" =
                                                         term_val ty.bool true
                                       | Supervisor => term_var "result_check_CSR_access" =
                                                         term_val ty.bool true
                                       | User       => term_var "result_check_CSR_access" =
                                                         term_val ty.bool false
                                       end)
                       | User => term_var "result_check_CSR_access" = term_val ty.bool true
                       end) }}.

        Definition sep_contract_privLevel_to_bits : SepContractFun privLevel_to_bits :=
          {{ ⊤ }}
            fn privLevel_to_bits [p :: ty_privilege] ty_priv_level
          {{ "result_privLevel_to_bits",
             asn.match_enum privilege (term_var p)
             (fun K => match K with
                       | Machine    => term_var "result_privLevel_to_bits" =
                                         term_val ty_priv_level [bits 11]
                       | Supervisor => term_var "result_privLevel_to_bits" =
                                         term_val ty_priv_level [bits 01]
                       | User       => term_var "result_privLevel_to_bits" =
                                         term_val ty_priv_level [bits 00]
                       end) }}.

        Definition sep_contract_csrAccess : SepContractFun csrAccess :=
          {{ ⊤ }}
            fn csrAccess [csr :: ty_csridx] ty_access_type
          {{ "result_csrAccess",
             term_var "result_csrAccess" = term_val ty_access_type ReadWrite }}.

        Definition sep_contract_csrPriv : SepContractFun csrPriv :=
          {{ ⊤ }}
            fn csrPriv [csr :: ty_csridx] ty_privilege
          {{ "result_csrPriv", ⊤ }}.

        Definition sep_contract_handle_mem_exception : SepContractFun handle_mem_exception :=
          {{ pc            ↦ term_var "i"
             ∗ ∃ "npc",    nextpc        ↦ term_var "npc"
             ∗             cur_privilege ↦ term_var p
             ∗             mcause        ↦ term_var "mcause"
             ∗             scause        ↦ term_var "scause"
             ∗             mstatus       ↦ term_record rmstatus [ term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ]
             ∗             medeleg       ↦ term_var "medeleg"
             ∗             mtvec         ↦ term_var tvec
             ∗             stvec         ↦ term_var "stvec"
             ∗             mepc          ↦ term_var "mepc"
             ∗             sepc          ↦ term_var "sepc" }}
            fn handle_mem_exception [addr :: ty_xlenbits; e :: ty_exception_type] ty.unit
          {{ "result_handle_mem_exception",
             term_var "result_handle_mem_exception" = term_val ty.unit tt
             ∗ (( cur_privilege ↦ term_val ty_privilege Supervisor
                  ∗ term_var p != term_val ty_privilege Machine
                  ∗ mcause ↦ term_var "mcause"
                  ∗ ∃ "spie", mstatus ↦ term_record rmstatus [term_var "mpp"; term_var p; term_var "mpie"; term_var "spie"; term_var "mie"; term_val ty.bool false]
                  ∗ medeleg ↦ term_var "medeleg"
                  ∗ term_var "medeleg" != term_val ty_Medeleg Medeleg_zero
                  ∗ mepc ↦ term_var "mepc"
                  ∗ ∃ "scause", scause ↦ term_var "scause"
                  ∗ sepc ↦ term_var "i"
                  ∗ mtvec ↦ term_var tvec
                  ∗ stvec ↦ term_var "stvec"
                  ∗ nextpc ↦ term_var "stvec")
                ∨
                  ( cur_privilege ↦ term_val ty_privilege Machine
                  ∗ ∃ "mcause", mcause ↦ term_var "mcause"
                  ∗ ∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_var p; term_var "spp"; term_var "mpie"; term_var "spie"; term_val ty.bool false; term_var "sie" ]
                  ∗ medeleg ↦ term_var "medeleg"
                  ∗ mepc ↦ term_var "i"
                  ∗ scause ↦ term_var "scause"
                  ∗ sepc ↦ term_var "sepc"
                  ∗ mtvec ↦ term_var tvec
                  ∗ stvec ↦ term_var "stvec"
                  ∗ nextpc ↦ term_var tvec))
             ∗ pc            ↦ term_var "i" }}
          with ["i" :: ty_xlenbits; tvec :: ty_xlenbits; "stvec" :: ty_xlenbits; p :: ty_privilege;
                "mpp" :: ty_privilege; "spp" :: ty_privilege; "mepc" :: ty_xlenbits;
                "sepc" :: ty_xlenbits; "mcause" :: ty_xlenbits; "scause" :: ty_xlenbits;
                "mpie" :: ty.bool; "spie" :: ty.bool; "mie" :: ty.bool; "sie" :: ty.bool;
                "medeleg" :: ty_Medeleg].

        Definition sep_contract_exception_handler : SepContractFun exception_handler :=
          {{ cur_privilege ↦ term_var cur_priv
             ∗             mcause        ↦ term_var "mcause"
             ∗             mstatus       ↦ (term_record rmstatus [ term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ])
             ∗             mtvec         ↦ (term_var "mtvec")
             ∗             mepc          ↦ (term_var "mepc")
             ∗             medeleg       ↦ (term_var "medeleg")
             ∗             scause        ↦ term_var "scause"
             ∗             stvec         ↦ (term_var "stvec")
             ∗             sepc          ↦ (term_var "sepc") }}
            fn exception_handler [cur_priv :: ty_privilege; ctl :: ty_ctl_result; "pc" :: ty_xlenbits] ty_xlenbits
          {{ "result_exception_handler",
             asn.match_union_alt ctl_result (term_var ctl)
             (fun K => match K with
                       | KCTL_TRAP => MkAlt (pat_var e)
                                               ((term_var "result_exception_handler" = term_var "stvec"
                                               ∗ cur_privilege ↦ term_val ty_privilege Supervisor
                                               ∗ term_var cur_priv != term_val ty_privilege Machine
                                               ∗ term_var "medeleg" != term_val ty_Medeleg Medeleg_zero
                                               ∗ mcause ↦ term_var "mcause"
                                               ∗ ∃ "spie", mstatus ↦ term_record rmstatus [nenv term_var "mpp"; term_var cur_priv; term_var "mpie"; term_var "spie"; term_var "mie"; term_val ty.bool false]
                                               ∗ mepc ↦ term_var "mepc"
                                               ∗ medeleg ↦ term_var "medeleg"
                                               ∗ ∃ "scause", scause ↦ term_var "scause"
                                               ∗ sepc ↦ term_var "pc"
                                               ∗ mtvec ↦ term_var "mtvec"
                                               ∗ stvec ↦ term_var "stvec")
                                             ∨
                                               (term_var "result_exception_handler" = term_var "mtvec"
                                               ∗ cur_privilege ↦ term_val ty_privilege Machine
                                               ∗ ∃ "mcause", mcause ↦ term_var "mcause"
                                               ∗ ∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_var cur_priv; term_var "spp"; term_var "mpie"; term_var "spie"; term_val ty.bool false; term_var "sie" ]
                                               ∗ mepc ↦ term_var "pc"
                                               ∗ medeleg ↦ term_var "medeleg"
                                               ∗ scause ↦ term_var "scause"
                                               ∗ sepc ↦ term_var "sepc"
                                               ∗ mtvec ↦ term_var "mtvec"
                                               ∗ stvec ↦ term_var "stvec"))
                       | KCTL_SRET => MkAlt pat_unit
                                        (term_var "result_exception_handler" = term_var "sepc"
                                         ∗             term_var "spp" != term_val ty_privilege Machine
                                         ∗             cur_privilege  ↦ term_var "spp"
                                         ∗             mcause         ↦ term_var "mcause"
                                         ∗ ∃ "sie", mstatus ↦ term_record rmstatus [nenv term_var "mpp"; term_val ty_privilege User; term_var "mpie"; term_val ty.bool true; term_var "mie"; term_var "sie" ]
                                         ∗             mtvec          ↦ term_var "mtvec"
                                         ∗             mepc           ↦ term_var "mepc"
                                         ∗             medeleg        ↦ term_var "medeleg"
                                         ∗             scause         ↦ term_var "scause"
                                         ∗             stvec          ↦ term_var "stvec"
                                         ∗             sepc           ↦ term_var "sepc")
                       | KCTL_MRET => MkAlt pat_unit
                                        (term_var "result_exception_handler" = term_var "mepc"
                                         ∗             cur_privilege ↦ term_var "mpp"
                                         ∗ ∃ "mcause", mcause        ↦ term_var "mcause"
                                         ∗ ∃ "mie", mstatus          ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "spp"; term_val ty.bool true; term_var "spie"; term_var "mie"; term_var "sie" ]
                                         ∗             mtvec         ↦ term_var "mtvec"
                                         ∗             mepc          ↦ term_var "mepc"
                                         ∗             medeleg       ↦ term_var "medeleg"
                                         ∗             scause        ↦ term_var "scause"
                                         ∗             stvec         ↦ term_var "stvec"
                                         ∗             sepc          ↦ term_var "sepc")
                       end) }}
          with ["mpp" :: ty_privilege; "mepc" :: ty_xlenbits; "mtvec" :: ty_xlenbits;
                "spp" :: ty_privilege; "stvec" :: ty_xlenbits; "sepc" :: ty_xlenbits;
                "mcause" :: ty_xlenbits; "scause" :: ty_xlenbits; "mpie" :: ty.bool;
                "spie" :: ty.bool; "mie" :: ty.bool; "sie" :: ty.bool; "medeleg" :: ty_Medeleg].

        Definition sep_contract_handle_illegal : SepContractFun handle_illegal :=
          {{ cur_privilege ↦ term_var p
             ∗ pc ↦ term_var "pc"
             ∗ mcause  ↦ term_var "mcause"
             ∗ mstatus ↦ term_record rmstatus [term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ]
             ∗ medeleg ↦ term_var "medeleg"
             ∗ mepc ↦ term_var "mepc"
             ∗ mtvec ↦ term_var tvec
             ∗ stvec ↦ term_var "stvec"
             ∗ sepc ↦ term_var "sepc"
             ∗ ∃ "scause", scause ↦ term_var "scause"
             ∗ ∃ v, nextpc ↦ term_var v }}
            fn handle_illegal [] ty.unit
          {{ "result_handle_illegal",
             term_var "result_handle_illegal" = term_val ty.unit tt
             ∗ ((cur_privilege ↦ term_val ty_privilege Supervisor
                 ∗ term_var p != term_val ty_privilege Machine
                 ∗ nextpc ↦ term_var "stvec"
                 ∗ term_var "medeleg" != term_val ty_Medeleg Medeleg_zero
                 ∗ mepc ↦ term_var "mepc"
                 ∗ sepc ↦ term_var "pc"
                 ∗ mcause ↦ term_var "mcause"
                 ∗ ∃ "spie", mstatus ↦ term_record rmstatus [nenv term_var "mpp"; term_var p; term_var "mpie"; term_var "spie"; term_var "mie"; term_val ty.bool false])
               ∨
                 (cur_privilege ↦ term_val ty_privilege Machine
                 ∗ nextpc ↦ term_var tvec
                 ∗ mepc ↦ term_var "pc"
                 ∗ sepc ↦ term_var "sepc"
                 ∗ ∃ "mcause", mcause ↦ term_var "mcause"
                 ∗ ∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_var p; term_var "spp"; term_var "mpie"; term_var "spie"; term_val ty.bool false; term_var "sie"]))
             ∗ pc ↦ term_var "pc"
             ∗ medeleg ↦ term_var "medeleg"
             ∗ mtvec ↦ term_var tvec
             ∗ stvec ↦ term_var "stvec"
             ∗ ∃ "scause", scause ↦ term_var "scause" }}
          with [p :: ty_privilege; "pc" :: ty_xlenbits; tvec :: ty_xlenbits; "stvec" :: ty_xlenbits;
                "mepc" :: ty_xlenbits; "sepc" :: ty_xlenbits; "mpp" :: ty_privilege;
                "spp" :: ty_privilege; "mpie" :: ty.bool; "spie" :: ty.bool; "mie" :: ty.bool;
                "sie" :: ty.bool; "medeleg" :: ty_Medeleg; "mcause" :: ty_xlenbits].

        Definition sep_contract_trap_handler : SepContractFun trap_handler :=
          {{ term_var del_priv != term_val ty_privilege User
             ∗ cur_privilege ↦ term_var p
             ∗ mcause  ↦ term_var "mcause"
             ∗ mstatus ↦ term_record rmstatus [term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie"]
             ∗ mepc    ↦ term_var "mepc"
             ∗ mtvec ↦ term_var "mtvec"
             ∗ scause  ↦ term_var "scause"
             ∗ sepc    ↦ term_var "sepc"
             ∗ stvec ↦ term_var "stvec" }}
            fn trap_handler [del_priv :: ty_privilege; "intr" :: ty.bool; c :: ty_exc_code; "pc" :: ty_xlenbits] ty_xlenbits
          {{ "result_trap_handler",
             cur_privilege ↦ term_var del_priv
             ∗ asn.match_enum privilege (term_var del_priv)
                 (fun K => match K with
                           | Machine    =>
                               term_var "result_trap_handler" = term_var "mtvec"
                               ∗ mcause ↦ term_zext (term_var c)
                               ∗ ∃ "mpie", mstatus ↦ term_record rmstatus [nenv term_var p; term_var "spp"; term_var "mpie"; term_var "spie"; term_val ty.bool false; term_var "sie"]
                               ∗ mepc ↦ term_var "pc"
                               ∗ scause ↦ term_var "scause"
                               ∗ sepc ↦ term_var "sepc"
                           | Supervisor =>
                               term_var "result_trap_handler" = term_var "stvec"
                               ∗ term_var "p" != term_val ty_privilege Machine
                               ∗ mcause ↦ term_var "mcause"
                               ∗ ∃ "spie", mstatus ↦ term_record rmstatus [nenv term_var "mpp"; term_var p; term_var "mpie"; term_var "spie"; term_var "mie"; term_val ty.bool false]
                               ∗ mepc ↦ term_var "mepc"
                               ∗ scause ↦ term_zext (term_var c)
                               ∗ sepc ↦ term_var "pc"
                           | User       => ⊥
                           end)
             ∗ mtvec ↦ term_var "mtvec"
             ∗ stvec ↦ term_var "stvec" }}
          with [p :: ty_privilege; "mcause" :: ty_xlenbits; "mpp" :: ty_privilege;
                "spp" :: ty_privilege; "mpie" :: ty.bool; "spie" :: ty.bool; "mie" :: ty.bool;
                "sie" :: ty.bool; "mepc" :: ty_xlenbits; "mtvec" :: ty_xlenbits;
                "scause" :: ty_xlenbits; "sepc" :: ty_xlenbits; "stvec" :: ty_xlenbits].

        Definition sep_contract_prepare_trap_vector : SepContractFun prepare_trap_vector :=
          {{ mtvec ↦ term_var tvec ∗ stvec ↦ term_var "stvec" }}
            fn prepare_trap_vector [p :: ty_privilege; cause :: ty_mcause] ty_xlenbits
          {{ "result_prepare_trap_vector",
             asn.match_enum privilege (term_var p)
               (fun K => match K with
                         | Machine    => term_var "result_prepare_trap_vector" = term_var tvec
                         | Supervisor => term_var "result_prepare_trap_vector" = term_var "stvec"
                         | User       => ⊥
                         end)
             ∗ mtvec ↦ term_var tvec
             ∗ stvec ↦ term_var "stvec" }}
          with [tvec :: ty_xlenbits; "stvec" :: ty_xlenbits].

        Definition sep_contract_tvec_addr : SepContractFun tvec_addr :=
          {{ ⊤ }}
            fn tvec_addr [m :: ty_xlenbits; c :: ty_mcause] (ty.option ty_xlenbits)
          {{ "result_tvec_addr",
             term_var "result_tvec_addr" = term_inl (term_var m) }}.

        Definition sep_contract_exceptionType_to_bits : SepContractFun exceptionType_to_bits :=
          {{ ⊤ }}
            fn exceptionType_to_bits [e :: ty_exception_type] ty_exc_code
          {{ "result_exceptionType_to_bits",
             ∃ result, term_var "result_exceptionType_to_bits" = term_var result }}.

        Definition sep_contract_Medeleg_to_bits : SepContractFun Medeleg_to_bits :=
          {{ ⊤ }}
            fn Medeleg_to_bits ["i" :: ty_Medeleg] ty_xlenbits
          {{ "result_Medeleg_to_bits",
             ∃ result, term_var "result_Medeleg_to_bits" = term_var result }}.

        Definition sep_contract_exception_delegatee : SepContractFun exception_delegatee :=
          {{ medeleg ↦ term_var "medeleg" }}
            fn exception_delegatee [e :: ty_exception_type; p :: ty_privilege] ty_privilege
          {{ "result_exception_delegatee",
             term_var "result_exception_delegatee" != term_val ty_privilege User
             ∗ (if: term_eq (term_var "result_exception_delegatee") (term_val ty_privilege Supervisor)
                then term_var "medeleg" != term_val ty_Medeleg Medeleg_zero
                else ⊤)
             ∗ medeleg ↦ term_var "medeleg" }}
          with ["medeleg" :: ty_Medeleg].

        Definition sep_contract_get_arch_pc : SepContractFun get_arch_pc :=
          {{ pc ↦ term_var v }}
            fn get_arch_pc [] ty_xlenbits
          {{ "result_get_arch_pc",
             term_var "result_get_arch_pc" = term_var v
             ∗ pc ↦ term_var v }}
          with [v :: ty_xlenbits].

        Definition sep_contract_set_next_pc : SepContractFun set_next_pc :=
          {{ ∃ v, nextpc ↦ term_var v }}
            fn set_next_pc [addr :: ty_xlenbits] ty.unit
          {{ "result_set_next_pc",
             term_var "result_set_next_pc" = term_val ty.unit tt
             ∗ nextpc ↦ term_var addr }}.

        Definition sep_contract_get_next_pc : SepContractFun get_next_pc :=
          {{ nextpc ↦ term_var v }}
            fn get_next_pc [] ty_xlenbits
          {{ "result_get_next_pc",
             term_var "result_get_next_pc" = term_var v
             ∗ nextpc ↦ term_var v }}
          with [v :: ty_xlenbits].

        Definition sep_contract_tick_pc : SepContractFun tick_pc :=
          {{ nextpc ↦ term_var "npc" ∗ ∃ "i", pc ↦ term_var "i" }}
            fn tick_pc [] ty.unit
          {{ "result_tick_pc",
             term_var "result_tick_pc" = term_val ty.unit tt
             ∗ nextpc ↦ term_var "npc"
             ∗ pc     ↦ term_var "npc" }}
          with ["npc" :: ty_xlenbits].

        Definition sep_contract_to_bits (l : nat) : SepContractFun (to_bits l) :=
          {{ ⊤ }}
            fn (to_bits l) [value :: ty.int] (ty.bvec l)
          {{ "result_to_bits",
             term_var "result_to_bits" = term_get_slice_int (term_var value) }}.

        Definition sep_contract_rX : SepContractFun rX :=
          {{ asn_gprs }}
            fn rX [rs :: ty_regno] ty_xlenbits
          {{ "result_rX", asn_gprs }}.

        Definition sep_contract_wX : SepContractFun wX :=
          {{ asn_gprs }}
            fn wX [rd :: ty_regno; v :: ty_xlenbits] ty.unit
          {{ "result_wX",
             term_var "result_wX" = term_val ty.unit tt
             ∗ asn_gprs }}.

        Definition sep_contract_step {τ Δ} : SepContract Δ τ :=
          let Σ := ["m" :: ty_privilege; "mtvec" :: ty_xlenbits; "stvec" :: ty_xlenbits; "pmpentries" :: ty.list ty_pmpentry; "mpp" :: ty_privilege; "spp" :: ty_privilege; "pc" :: ty_xlenbits; "mcause" :: ty_xlenbits; "mscratch" :: ty_xlenbits; "mepc" :: ty_xlenbits; "scause" :: ty_xlenbits; "sscratch" :: ty_xlenbits; "sepc" :: ty_xlenbits; "mpie" :: ty.bool; "spie" :: ty.bool; "mie" :: ty.bool; "sie" :: ty.bool; "mideleg" :: ty_Minterrupts; "medeleg" :: ty_Medeleg] in
          {| sep_contract_logic_variables := sep_contract_logvars Δ Σ;
             sep_contract_localstore      := create_localstore Δ Σ;
             sep_contract_precondition    :=
                           asn.match_enum privilege (term_var "m") (fun _ => ⊤) ∗
                           asn_pmp_addr_access (term_var "pmpentries") (term_var "m") ∗
                           asn_gprs ∗
                           asn_pmp_entries (term_var "pmpentries") ∗
               ∃ "mie",    mie           ↦ term_var "mie" ∗
               ∃ "mip",    mip           ↦ term_var "mip" ∗
                           cur_privilege ↦ term_var "m" ∗
                           pc            ↦ term_var "pc" ∗
               ∃ "npc",    nextpc        ↦ term_var "npc" ∗
                           mtvec         ↦ term_var "mtvec" ∗
                           stvec         ↦ term_var "stvec" ∗
                           mstatus ↦ term_record rmstatus [ term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ] ∗
                           mepc          ↦ term_var "mepc" ∗
                           sepc          ↦ term_var "sepc" ∗
                           mideleg       ↦ term_var "mideleg" ∗
                           medeleg       ↦ term_var "medeleg" ∗
                           mscratch      ↦ term_var "mscratch" ∗
                           mcause        ↦ term_var "mcause" ∗
                           sscratch      ↦ term_var "sscratch" ∗
                           scause        ↦ term_var "scause";
             sep_contract_result          := "result_mach_inv";
             sep_contract_postcondition   :=
               (  (* Executing normally *)
                              asn_pmp_addr_access (term_var "pmpentries") (term_var "m") ∗
                              asn_gprs ∗
                              asn_pmp_entries (term_var "pmpentries") ∗
                  ∃ "mie",    mie           ↦ term_var "mie" ∗
                  ∃ "mip",    mip           ↦ term_var "mip" ∗
                  ∃ v,       (pc        ↦ term_var v ∗
                              nextpc    ↦ term_var v) ∗
                              mtvec         ↦ term_var "mtvec" ∗
                              mepc          ↦ term_var "mepc" ∗
                              mideleg       ↦ term_var "mideleg" ∗
                              medeleg       ↦ term_var "medeleg" ∗
                              mscratch ↦ term_var "mscratch" ∗
                              mcause ↦ term_var "mcause" ∗
                  (  (* Executing normally in M-mode. Nothing changes, no transitions, those are handled by the other disjuncts, so we rule them out here. *)
                                 term_var "m" = term_val ty_privilege Machine ∗
                                 cur_privilege ↦ term_val ty_privilege Machine ∗
                                 stvec         ↦ term_var "stvec" ∗
                                 mstatus ↦ term_record rmstatus [ term_var "mpp"; term_var "spp"; term_var "mpie"; term_var "spie"; term_var "mie"; term_var "sie" ] ∗
                                 sepc          ↦ term_var "sepc" ∗
                                 sscratch ↦ term_var "sscratch" ∗
                                 scause ↦ term_var "scause"
                   ∨
                     (* Executing normally in U/S-mode. We do allow Supervisor accessible CSRs to be modified here. *)
                                 term_var "m" != term_val ty_privilege Machine ∗
                    asn.exist "new_m" ty_privilege (
                                 cur_privilege ↦ term_var "new_m" ∗
                                 term_var "new_m" != term_val ty_privilege Machine ∗
                    ∃ "new_stvec", stvec       ↦ term_var "new_stvec" ∗
                    ∃ "new_spp", ∃ "new_spie", ∃ "new_sie",
                                 mstatus ↦ term_record rmstatus [ term_var "mpp"; term_var "new_spp"; term_var "mpie"; term_var "new_spie"; term_var "mie"; term_var "new_sie" ] ∗
                    ∃ "new_sepc", sepc         ↦ term_var "new_sepc" ∗
                    ∃ "new_sscratch", sscratch ↦ term_var "new_sscratch" ∗
                    ∃ "new_scause", scause     ↦ term_var "new_scause"))
                ∨
                  (* Modified CSRs, Machine mode case (access to all CSRs) *)
                                 asn_pmp_addr_access (term_var "pmpentries") (term_var "m") ∗
                                 asn_gprs ∗
                  ∃ "new_pmpentries",   asn_pmp_entries (term_var "new_pmpentries") ∗
                                 term_var "m"  =  term_val ty_privilege Machine ∗
                  ∃ "mie",       mie           ↦ term_var "mie" ∗
                  ∃ "mip",       mip           ↦ term_var "mip" ∗
                                 cur_privilege ↦ term_val ty_privilege Machine ∗
                  ∃ v, (pc                ↦ term_var v ∗ (* tick, nextpc + 4 *)
                        nextpc            ↦ term_var v) ∗
                  ∃ "new_mtvec", mtvec         ↦ term_var "new_mtvec" ∗
                  ∃ "new_mpp", ∃ "new_spp", ∃ "new_mpie", ∃ "new_spie", ∃ "new_mie", ∃ "new_sie", mstatus       ↦ term_record rmstatus [ term_var "new_mpp"; term_var "new_spp"; term_var "new_mpie"; term_var "new_spie"; term_var "new_mie"; term_var "new_sie" ] ∗
                  ∃ "new_mepc",  mepc          ↦ term_var "new_mepc" ∗
                  ∃ "new_sepc",  sepc          ↦ term_var "new_sepc" ∗
                  ∃ "new_mideleg", mideleg       ↦ term_var "new_mideleg" ∗
                  ∃ "new_medeleg", medeleg       ↦ term_var "new_medeleg" ∗
                  ∃ "new_mscratch", mscratch ↦ term_var "new_mscratch" ∗
                  ∃ "new_mcause", mcause ↦ term_var "new_mcause" ∗
                  ∃ "new_sscratch", sscratch ↦ term_var "new_sscratch" ∗
                  ∃ "new_scause", scause ↦ term_var "new_scause"
                ∨
                  (* Trap occured -> Go into M-mode *)
                  asn_pmp_addr_access (term_var "pmpentries") (term_var "m") ∗
                  asn_gprs ∗
                  asn_pmp_entries (term_var "pmpentries") ∗
                  ∃ "mie",    mie           ↦ term_var "mie" ∗
                  ∃ "mip",    mip           ↦ term_var "mip" ∗
                  cur_privilege ↦ (term_val ty_privilege Machine) ∗
                  pc            ↦ term_var "mtvec" ∗
                  nextpc        ↦ term_var "mtvec" ∗
                  mtvec         ↦ term_var "mtvec" ∗
                  ∃ "new_stvec", stvec ↦ term_var "new_stvec" ∗
                  ∃ "new_spp", ∃ "mpie", ∃ "new_spie", ∃ "new_sie",
                    asn.match_enum privilege (term_var "m")
                    (fun K => match K with
                              (* Trap from M-mode: MPP is M-mode (reentrant trap M->M) *)
                              | Machine =>
                                mstatus ↦ term_record rmstatus [nenv term_val ty_privilege Machine; term_var "new_spp"; term_var "mpie"; term_var "new_spie"; term_val ty.bool false; term_var "new_sie" ]
                              (* Trap from S/U-mode: MPP is some S/U privilege level *)
                              | _       => ∃ "new_mpp", (
                                mstatus ↦ term_record rmstatus [nenv term_var "new_mpp"; term_var "new_spp"; term_var "mpie"; term_var "new_spie"; term_val ty.bool false; term_var "new_sie" ] ∗
                                term_var "new_mpp" != term_val ty_privilege Machine)
                              end) ∗
                  ∃ "mepc", mepc          ↦ term_var "mepc" ∗
                  ∃ "new_sepc", sepc ↦ term_var "new_sepc" ∗
                  mideleg       ↦ term_var "mideleg" ∗
                  medeleg       ↦ term_var "medeleg" ∗
                  ∃ "mscratch", mscratch ↦ term_var "mscratch" ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                  ∃ "new_sscratch", sscratch ↦ term_var "new_sscratch" ∗
                  ∃ "scause", scause ↦ term_var "scause"
                ∨
                  (* MRET = Recover *)
                  asn_pmp_addr_access (term_var "pmpentries") (term_var "m") ∗
                  asn_gprs ∗
                  asn_pmp_entries (term_var "pmpentries") ∗
                  term_var "m"  =  term_val ty_privilege Machine ∗
                  ∃ "mie",    mie           ↦ term_var "mie" ∗
                  ∃ "mip",    mip           ↦ term_var "mip" ∗
                  cur_privilege ↦ term_var "mpp" ∗
                  ∃ "mepc", (mepc          ↦ term_var "mepc" ∗
                             pc            ↦ term_var "mepc" ∗
                             nextpc        ↦ term_var "mepc") ∗
                  sepc          ↦ term_var "sepc" ∗
                  mideleg       ↦ term_var "mideleg" ∗
                  medeleg       ↦ term_var "medeleg" ∗
                  mtvec         ↦ term_var "mtvec" ∗
                  stvec         ↦ term_var "stvec" ∗
                  ∃ "mscratch", mscratch ↦ term_var "mscratch" ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                  ∃ "sscratch", sscratch ↦ term_var "sscratch" ∗
                  ∃ "scause", scause ↦ term_var "scause" ∗
                  ∃ "mie", mstatus ↦ term_record rmstatus [nenv term_val ty_privilege User; term_var "spp"; term_val ty.bool true; term_var "spie"; term_var "mie"; term_var "sie" ]
                ∨
                  (* SRET = Recover *)
                  asn_pmp_addr_access (term_var "pmpentries") (term_var "m") ∗
                  asn_gprs ∗
                  asn_pmp_entries (term_var "pmpentries") ∗
                  term_var "m"  =  term_val ty_privilege Machine ∗
                  ∃ "mie",    mie           ↦ term_var "mie" ∗
                  ∃ "mip",    mip           ↦ term_var "mip" ∗
                  cur_privilege ↦ term_var "spp" ∗
                  ∃ "sepc", (sepc          ↦ term_var "sepc" ∗
                             pc            ↦ term_var "sepc" ∗
                             nextpc        ↦ term_var "sepc") ∗
                  mepc          ↦ term_var "mepc" ∗
                  mideleg       ↦ term_var "mideleg" ∗
                  medeleg       ↦ term_var "medeleg" ∗
                  mtvec         ↦ term_var "mtvec" ∗
                  stvec         ↦ term_var "stvec" ∗
                  ∃ "mscratch", mscratch ↦ term_var "mscratch" ∗
                  ∃ "mcause", mcause ↦ term_var "mcause" ∗
                  ∃ "sscratch", sscratch ↦ term_var "sscratch" ∗
                  ∃ "scause", scause ↦ term_var "scause" ∗
                  ∃ "sie", mstatus ↦ term_record rmstatus [nenv term_var "mpp"; term_val ty_privilege User; term_var "mpie"; term_val ty.bool true; term_var "mie"; term_var "sie" ])
          |}.

        Definition sep_contract_fetch : SepContractFun fetch :=
          {{ pc ↦ term_var "i"
             ∗ cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
            fn fetch [] ty_fetch_result
          {{ "result_fetch",
             pc ↦ term_var "i"
             ∗ cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
          with ["i" :: ty_xlenbits; p :: ty_privilege; "entries" :: ty.list ty_pmpentry].

        Definition sep_contract_init_model : SepContractFun init_model :=
          {{ ∃ p, cur_privilege ↦ term_var p
             ∗ ∃ "es", asn_pmp_entries (term_var "es") }}
            fn init_model [] ty.unit
          {{ "result_init_model",
             term_var "result_init_model" = term_val ty.unit tt
             ∗ cur_privilege ↦ term_val ty_privilege Machine
             ∗ ∃ "es", asn_pmp_entries (term_var "es") }}.

        Definition sep_contract_init_sys : SepContractFun init_sys :=
          {{ ∃ p, cur_privilege ↦ term_var p
             ∗ ∃ "es", asn_pmp_entries (term_var "es") }}
            fn init_sys [] ty.unit
          {{ "result_init_sys",
             term_var "result_init_sys" = term_val ty.unit tt
             ∗ cur_privilege ↦ term_val ty_privilege Machine
             ∗ ∃ "es", asn_pmp_entries (term_var "es") }}.

        Definition sep_contract_init_pmp : SepContractFun init_pmp :=
          {{ ∃ "cfg0", pmp0cfg ↦ term_var "cfg0" ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1" }}
            fn init_pmp [] ty.unit
          {{ "result_init_pmp",
             ∃ "cfg0", pmp0cfg ↦ term_var "cfg0" ∗ ∃ "cfg1", pmp1cfg ↦ term_var "cfg1"
             ∗ term_var "result_init_pmp" = term_val ty.unit tt }}.

        Definition sep_contract_within_phys_mem : SepContractFun within_phys_mem :=
          {{ ⊤ }}
            fn within_phys_mem [paddr :: ty_xlenbits; width :: ty.int] ty.bool
          {{ "result_within_phys_mem",
             let paddr_int : Term _ ty.int := term_unsigned (term_var paddr) in
             if: term_var "result_within_phys_mem"
             then term_val ty.int (Z.of_N minAddr) <= paddr_int
                  ∗ (term_binop bop.plus paddr_int (term_var width)) <= term_val ty.int (Z.of_N maxAddr)
             else (paddr_int < term_val ty.int (Z.of_N minAddr)
                   ∨ term_val ty.int (Z.of_N maxAddr) < (term_binop bop.plus paddr_int (term_var width))) }}.

        Definition sep_contract_checked_mem_read (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@checked_mem_read bytes H) :=
          {{ term_union access_type KRead (term_val ty.unit tt) ⊑ term_var t
             ∗ cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p)
             ∗ asn_pmp_access (term_var paddr) (term_val ty_xlenbits (Bitvector.bv.of_nat bytes)) (term_var "entries") (term_var p) (term_var t) }}
            fn (@checked_mem_read bytes H) [t :: ty_access_type; paddr :: ty_xlenbits] (ty_memory_op_result bytes)
          {{ "result_checked_mem_read",
             cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
          with [p :: ty_privilege; "entries" :: ty.list ty_pmpentry].

        Definition sep_contract_checked_mem_write (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@checked_mem_write bytes H) :=
          {{ asn_pmp_access (term_var paddr) (term_val ty_xlenbits (Bitvector.bv.of_nat bytes)) (term_var "entries") (term_var p) (term_var acc)
             ∗ term_union access_type KWrite (term_val ty.unit tt) ⊑ term_var acc
             ∗ cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
            fn (@checked_mem_write bytes H) [paddr :: ty_xlenbits; data :: ty_bytes bytes] (ty_memory_op_result 1)
          {{ "result_checked_mem_write",
             cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
          with [p :: ty_privilege; "entries" :: ty.list ty_pmpentry; acc :: ty_access_type].

        Definition sep_contract_pmp_mem_read (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@pmp_mem_read bytes H) :=
          {{ term_union access_type KRead (term_val ty.unit tt) ⊑ term_var t
             ∗ cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
            fn (@pmp_mem_read bytes H) [t :: ty_access_type; p :: ty_privilege; paddr :: ty_xlenbits] (ty_memory_op_result bytes)
          {{ "result_pmp_mem_read",
             cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
          with ["entries" :: ty.list ty_pmpentry].

        Definition sep_contract_pmp_mem_write (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@pmp_mem_write bytes H) :=
          {{ (* NOTE: only ever called with typ = Write *)
             (term_var typ = term_union access_type KWrite (term_val ty.unit tt)
              ∨ term_var typ = term_union access_type KReadWrite (term_val ty.unit tt))
             ∗ cur_privilege ↦ term_var priv
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var priv) }}
            fn (@pmp_mem_write bytes H) [paddr :: ty_xlenbits; data :: ty_bytes bytes; typ :: ty_access_type; priv :: ty_privilege] (ty_memory_op_result 1)
          {{ "result_pmp_mem_write",
             cur_privilege ↦ term_var priv
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var priv) }}
          with ["entries" :: ty.list ty_pmpentry].

        Definition sep_contract_mem_write_value (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@mem_write_value bytes H) :=
          {{ cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
            fn (@mem_write_value bytes H) [paddr :: ty_xlenbits; value :: ty_bytes bytes] (ty_memory_op_result 1)
          {{ "result_pmp_mem_write",
             cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
          with [p :: ty_privilege; "entries" :: ty.list ty_pmpentry].

        Definition sep_contract_mem_read (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@mem_read bytes H) :=
          {{ (term_var typ = term_union access_type KRead (term_val ty.unit tt)
               ∨ term_var typ = term_union access_type KExecute (term_val ty.unit tt))
             ∗ cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
            fn (@mem_read bytes H) [typ :: ty_access_type; paddr :: ty_xlenbits] (ty_memory_op_result bytes)
          {{ "result_mem_read",
             cur_privilege ↦ term_var p
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var p) }}
          with [p :: ty_privilege; "entries" :: ty.list ty_pmpentry].

        Definition sep_contract_pmpCheck (bytes : nat) {H : restrict_bytes bytes} : SepContractFun (@pmpCheck bytes H) :=
          {{ asn_pmp_entries (term_var "entries") }}
            fn (@pmpCheck bytes H) [addr :: ty_xlenbits; acc :: ty_access_type; priv :: ty_privilege] (ty.option ty_exception_type)
          {{ "result_pmpCheck",
             asn_match_option
             _ (term_var "result_pmpCheck") e
             (asn_pmp_entries (term_var "entries"))
             (asn_pmp_entries (term_var "entries") ∗ asn_pmp_access (term_var addr) (term_get_slice_int (term_val ty.int (Z.of_nat bytes))) (term_var "entries") (term_var priv) (term_var acc)) }}
          with ["entries" :: ty.list ty_pmpentry].


        (* A [ty_pmpcfg_ent] argument destructured into its fields, which become
           logic variables of the contract. *)
        Definition pmpcfg_ent_pat (fL fA fX fW fR : LVar) : ArgBinding :=
          arg_pat ty_pmpcfg_ent
            [fL ∷ ty.bool; fA ∷ ty_pmpaddrmatchtype; fX ∷ ty.bool; fW ∷ ty.bool; fR ∷ ty.bool]
            (term_record rpmpcfg_ent
               [term_var_in (ctx.in_succ (ctx.in_succ (ctx.in_succ (ctx.in_succ ctx.in_zero))));
                term_var_in (ctx.in_succ (ctx.in_succ (ctx.in_succ ctx.in_zero)));
                term_var_in (ctx.in_succ (ctx.in_succ ctx.in_zero));
                term_var_in (ctx.in_succ ctx.in_zero);
                term_var_in ctx.in_zero]).

        Definition sep_contract_pmpCheckPerms : SepContractFun pmpCheckPerms :=
          {{ ⊤ }}
            fn pmpCheckPerms [pmpcfg_ent_pat L A X W R; acc :: ty_access_type; priv :: ty_privilege] ty.bool
          {{ "result_pmpCheckPerms",
             let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
             if: term_var "result_pmpCheckPerms"
             then asn_pmp_check_perms entry (term_var acc) (term_var priv)
             else ⊤ }}.

        Definition sep_contract_pmpCheckRWX : SepContractFun pmpCheckRWX :=
          {{ ⊤ }}
            fn pmpCheckRWX [pmpcfg_ent_pat L A X W R; acc :: ty_access_type] ty.bool
          {{ "result_pmpCheckRWX",
             let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
             if: term_var "result_pmpCheckRWX"
             then asn_pmp_check_rwx entry (term_var acc)
             else ⊤ }}.

        Definition sep_contract_pmpAddrRange : SepContractFun pmpAddrRange :=
          {{ ⊤ }}
            fn pmpAddrRange [pmpcfg_ent_pat L A X W R; pmpaddr :: ty_xlenbits; prev_pmpaddr :: ty_xlenbits] ty_pmp_addr_range
          {{ "result_pmpAddrRange",
             asn.match_enum pmpaddrmatchtype (term_var A)
               (fun K => match K with
                         | OFF => term_var "result_pmpAddrRange" = term_inr (term_val ty.unit tt)
                         | TOR => term_var "result_pmpAddrRange" = term_inl (term_var prev_pmpaddr ,ₜ term_var pmpaddr)
                         end) }}.

        Definition sep_contract_pmpMatchAddr : SepContractFun pmpMatchAddr :=
          {{ ⊤ }}
            fn pmpMatchAddr [addr :: ty_xlenbits; width :: ty_xlenbits; rng :: ty_pmp_addr_range] ty_pmpaddrmatch
          {{ "result_pmpMatchAddr",
             asn_match_option
             _ (term_var rng) v
             (asn.match_prod
                (term_var v) lo hi
                (asn.match_enum pmpaddrmatch (term_var "result_pmpMatchAddr")
                  (fun K => match K with
                            | PMP_NoMatch =>
                                asn_bool (term_var hi <ᵘₜ term_var lo)
                                ∨ (asn_bool (term_var lo <=ᵘₜ term_var hi) ∗ asn_bool (term_binop bop.bvadd (term_var addr) (term_var width) <=ᵘₜ term_var lo))
                                ∨ (asn_bool (term_var lo <=ᵘₜ term_var hi) ∗ asn_bool (term_var lo <ᵘₜ term_binop bop.bvadd (term_var addr) (term_var width)) ∗ asn_bool (term_var hi <=ᵘₜ term_var addr))
                            | PMP_PartialMatch =>
                                term_var lo <=ᵘ term_var hi ∗
                                term_var lo <ᵘ term_binop bop.bvadd (term_var addr) (term_var width) ∗
                                term_var addr <ᵘ term_var hi ∗
                                (term_var addr <ᵘ term_var lo ∨ term_var hi <ᵘ (term_binop bop.bvadd (term_var addr) (term_var width)))
                            | PMP_Match =>
                                  (term_var lo) <=ᵘ (term_var hi)
                                ∗ (term_var lo) <ᵘ  (term_binop bop.bvadd (term_var addr) (term_var width))
                                ∗ (term_var lo) <=ᵘ (term_var addr)
                                ∗ (term_var addr) <ᵘ (term_var hi)
                                ∗ (term_binop bop.bvadd (term_var addr) (term_var width)) <=ᵘ (term_var hi)
                            end)))
             (term_var "result_pmpMatchAddr" = term_val ty_pmpaddrmatch PMP_NoMatch) }}.

        Definition sep_contract_pmpMatchEntry : SepContractFun pmpMatchEntry :=
          {{ ⊤ }}
            fn pmpMatchEntry [addr :: ty_xlenbits; width :: ty_xlenbits; acc :: ty_access_type; priv :: ty_privilege; pmpcfg_ent_pat L A X W R; pmpaddr :: ty_xlenbits; prev_pmpaddr :: ty_xlenbits] ty_pmpmatch
          {{ "result_pmpMatchEntry",
               let entry := term_record rpmpcfg_ent [term_var L; term_var A; term_var X; term_var W; term_var R] in
               asn.match_enum pmpmatch (term_var "result_pmpMatchEntry")
                 (fun K => match K with
                           | PMP_Continue =>
                                    term_var A = term_val ty_pmpaddrmatchtype OFF
                                    ∨ (asn.formula (formula_relop bop.neq (term_var A) (term_val ty_pmpaddrmatchtype OFF)) ∗
                                         (asn_bool (term_var pmpaddr <ᵘₜ term_var prev_pmpaddr)
                                          ∨ (asn_bool (term_var prev_pmpaddr <=ᵘₜ term_var pmpaddr) ∗ asn_bool (term_binop bop.bvadd (term_var addr) (term_var width) <=ᵘₜ term_var prev_pmpaddr))
                                          ∨ (asn_bool (term_var prev_pmpaddr <=ᵘₜ term_var pmpaddr) ∗ asn_bool (term_var prev_pmpaddr <ᵘₜ term_binop bop.bvadd (term_var addr) (term_var width)) ∗ asn_bool (term_var pmpaddr <=ᵘₜ term_var addr))))
                           | PMP_Fail     =>
                               asn_bool (term_not
                                           (term_var prev_pmpaddr <=ᵘₜ term_var addr &&ₜ term_var addr <ᵘₜ term_var pmpaddr))
                               ∨ ⊤ (* TODO: either we have a partial match, or we don't have the required permissions! *)
                           | PMP_Success  =>
                                  (term_var prev_pmpaddr) <=ᵘ (term_var pmpaddr)
                                ∗ (term_var prev_pmpaddr) <ᵘ  (term_binop bop.bvadd (term_var addr) (term_var width))
                                ∗ (term_var prev_pmpaddr) <=ᵘ (term_var addr)
                                ∗ (term_var addr) <ᵘ (term_var pmpaddr)
                                ∗ (term_binop bop.bvadd (term_var addr) (term_var width)) <=ᵘ (term_var pmpaddr)
                               ∗ asn_pmp_check_perms entry (term_var acc) (term_var priv)
                               ∗ term_var A = term_val ty_pmpaddrmatchtype TOR
                           end) }}.

        Definition sep_contract_pmpLocked : SepContractFun pmpLocked :=
          {{ ⊤ }}
            fn pmpLocked [pmpcfg_ent_pat L A X W R] ty.bool
          {{ "result_pmpLocked", term_var "result_pmpLocked" = term_var L }}.

        Definition sep_contract_pmpWriteCfg : SepContractFun pmpWriteCfg :=
          {{ asn_expand_pmpcfg_ent (term_var cfg) }}
            fn pmpWriteCfg [cfg :: ty_pmpcfg_ent; value :: ty_byte] ty_pmpcfg_ent
          {{ "result_pmpWriteCfg",
             ∃ "cfg", (term_var "result_pmpWriteCfg" = term_var "cfg" ∗ asn_expand_pmpcfg_ent (term_var "cfg")) }}.


        Definition sep_contract_pmpWriteCfgReg : SepContractFun pmpWriteCfgReg :=
          {{ ∃ "cfg0", (pmp0cfg ↦ term_var "cfg0" ∗ asn_expand_pmpcfg_ent (term_var "cfg0"))
             ∗ ∃ "cfg1", (pmp1cfg ↦ term_var "cfg1" ∗ asn_expand_pmpcfg_ent (term_var "cfg1")) }}
            fn pmpWriteCfgReg ["n" :: ty.int; value :: ty_xlenbits] ty.unit
          {{ "result_pmpWriteCfgReg",
             term_var "result_pmpWriteCfgReg" = term_val ty.unit tt
             ∗ ∃ "cfg0", (pmp0cfg ↦ term_var "cfg0" ∗ asn_expand_pmpcfg_ent (term_var "cfg0"))
             ∗ ∃ "cfg1", (pmp1cfg ↦ term_var "cfg1" ∗ asn_expand_pmpcfg_ent (term_var "cfg1")) }}.

        Definition sep_contract_pmpWriteAddr : SepContractFun pmpWriteAddr :=
          {{ ⊤ }}
            fn pmpWriteAddr [locked :: ty.bool; addr :: ty_xlenbits; value :: ty_xlenbits] ty_xlenbits
          {{ "result_pmpWriteAddr",
             if: term_var locked
             then term_var "result_pmpWriteAddr" = term_var addr
             else term_var "result_pmpWriteAddr" = term_var value }}.

        Definition contract_environment : SepContractEnv :=
          fun Δ τ fn =>
            match fn with
            | execute_RTYPE           => Some sep_contract_execute_RTYPE
            | execute_ITYPE           => Some sep_contract_execute_ITYPE
            | execute_SHIFTIOP        => Some sep_contract_execute_SHIFTIOP
            | execute_UTYPE           => Some sep_contract_execute_UTYPE
            | execute_BTYPE           => Some sep_contract_execute_BTYPE
            | execute_RISCV_JAL       => Some sep_contract_execute_RISCV_JAL
            | execute_RISCV_JALR      => Some sep_contract_execute_RISCV_JALR
            | execute_ECALL           => Some sep_contract_execute_ECALL
            | execute_EBREAK          => Some sep_contract_execute_EBREAK
            | execute_SRET            => Some sep_contract_execute_SRET
            | execute_MRET            => Some sep_contract_execute_MRET
            | execute_CSR             => Some sep_contract_execute_CSR
            | execute_STORE           => Some sep_contract_execute_STORE
            | execute_LOAD            => Some sep_contract_execute_LOAD
            | execute_MUL             => Some sep_contract_execute_MUL
            | execute_ILLEGAL         => Some sep_contract_execute_ILLEGAL
            | get_arch_pc             => Some sep_contract_get_arch_pc
            | get_next_pc             => Some sep_contract_get_next_pc
            | set_next_pc             => Some sep_contract_set_next_pc
            | tick_pc                 => Some sep_contract_tick_pc
            | to_bits l               => Some (sep_contract_to_bits l)
            | exception_handler       => Some sep_contract_exception_handler
            | handle_mem_exception    => Some sep_contract_handle_mem_exception
            | handle_illegal          => Some sep_contract_handle_illegal
            | trap_handler            => Some sep_contract_trap_handler
            | prepare_trap_vector     => Some sep_contract_prepare_trap_vector
            | tvec_addr               => Some sep_contract_tvec_addr
            | exceptionType_to_bits   => Some sep_contract_exceptionType_to_bits
            | Medeleg_to_bits         => Some sep_contract_Medeleg_to_bits
            | exception_delegatee     => Some sep_contract_exception_delegatee
            | rX                      => Some sep_contract_rX
            | wX                      => Some sep_contract_wX
            (* | abs                     => Some sep_contract_abs *)
            | within_phys_mem         => Some sep_contract_within_phys_mem
            | readCSR                 => Some sep_contract_readCSR
            | writeCSR                => Some sep_contract_writeCSR
            (* | check_CSR               => Some sep_contract_check_CSR *)
            | is_CSR_defined          => Some sep_contract_is_CSR_defined
            | check_CSR_access        => Some sep_contract_check_CSR_access
            | privLevel_to_bits       => Some sep_contract_privLevel_to_bits
            | csrAccess               => Some sep_contract_csrAccess
            | csrPriv                 => Some sep_contract_csrPriv
            | @checked_mem_read bytes H => Some (@sep_contract_checked_mem_read bytes H)
            | @checked_mem_write bytes H => Some (@sep_contract_checked_mem_write bytes H)
            | @pmp_mem_read bytes H   => Some (@sep_contract_pmp_mem_read bytes H)
            | @pmp_mem_write bytes H  => Some (@sep_contract_pmp_mem_write bytes H)
            | @pmpCheck bytes H       => Some (@sep_contract_pmpCheck bytes H)
            | pmpCheckPerms           => Some sep_contract_pmpCheckPerms
            | pmpCheckRWX             => Some sep_contract_pmpCheckRWX
            | pmpAddrRange            => Some sep_contract_pmpAddrRange
            | pmpMatchAddr            => Some sep_contract_pmpMatchAddr
            | pmpMatchEntry           => Some sep_contract_pmpMatchEntry
            | pmpLocked               => Some sep_contract_pmpLocked
            | @pmpWriteCfgReg         => Some sep_contract_pmpWriteCfgReg
            | pmpWriteCfg             => Some sep_contract_pmpWriteCfg
            | pmpWriteAddr            => Some sep_contract_pmpWriteAddr
            | @mem_write_value bytes H => Some (@sep_contract_mem_write_value bytes H)
            | @mem_read bytes H       => Some (@sep_contract_mem_read bytes H)
            | init_model              => Some sep_contract_init_model
            | init_sys                => Some sep_contract_init_sys
            | init_pmp                => Some sep_contract_init_pmp
            | fetch                   => Some sep_contract_fetch
            | execute                 => Some sep_contract_execute
            | step                    => Some sep_contract_step
            | _                       => None
            end.

        Lemma linted_contract_environment :
          forall Δ τ (fn : Fun Δ τ),
            match contract_environment fn with
            | Some cnt => Linted cnt
            | None   => True
            end.
        Proof. intros ? ? []; try constructor. Qed.

      End ContractDef.

      Section ForeignDef.
        Import RiscvPmpSignature.notations.
        Import RiscvPmpSignature.ContractNotations.
        Local Notation "e1 '=?' e2" := (term_binop (bop.relop bop.eq) e1 e2).

        Definition sep_contract_read_ram (bytes : nat) : SepContractFunX (read_ram bytes) :=
          {{ asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]) }}
            fn (read_ram bytes) ["paddr" :: ty_xlenbits] (ty_bytes bytes)
          {{ "result_read_ram",
             term_var "result_read_ram" = term_var "w"
             ∗ asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]) }}
          with ["w" :: ty_bytes bytes].

        Definition sep_contract_write_ram (bytes : nat) : SepContractFunX (write_ram bytes) :=
          {{ ∃ "w", asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]) }}
            fn (write_ram bytes) ["paddr" :: ty_xlenbits; "data" :: ty_bytes bytes] ty.bool
          {{ "result_write_ram",
             asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "data"]) }}.

        (* NOTE: for now, this always returns False, since we do not provide the adversary with access to MMIO. In the future, this could just branch non-deterministically in the post. *)
        (* TODO: return `is_mmio`-chunk here once untrusted code gains access to MMIO *)

        Definition sep_contract_within_mmio (bytes : nat) {H: restrict_bytes bytes}: SepContractFunX (@within_mmio bytes H) :=
          {{ cur_privilege ↦ term_var "p"
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var "p")
             ∗ (∃ "t", asn_pmp_access (term_var "paddr") (term_val ty_xlenbits (Bitvector.bv.of_nat bytes)) (term_var "entries") (term_var "p") (term_var "t")) }}
            fn (@within_mmio bytes H) ["paddr" :: ty_xlenbits] ty.bool
          {{ "result_is_within",
             term_var "result_is_within" = term_val ty.bool false
             ∗ cur_privilege ↦ term_var "p"
             ∗ asn_pmp_entries (term_var "entries")
             ∗ asn_pmp_addr_access (term_var "entries") (term_var "p") }}
          with ["p" :: ty_privilege; "entries" :: ty.list ty_pmpentry].

        (* NOTE: no need for sensible contracts for `mmio_read`/`mmio_write` yet, as we will not grant untrusted code access to `mmio` directly *)
       Definition sep_contract_mmio_read (bytes : nat) (H : restrict_bytes bytes) : SepContractFunX (mmio_read H) :=
          {{ ⊥ }}
            fn (mmio_read H) ["paddr" :: ty_xlenbits] (ty_bytes bytes)
          {{ "result_read_mmio", ⊥ }}.
       Definition sep_contract_mmio_write (bytes : nat) (H : restrict_bytes bytes) : SepContractFunX (mmio_write H) :=
          {{ ⊥ }}
            fn (mmio_write H) ["paddr" :: ty_xlenbits; "data" :: ty_bytes bytes] ty.bool
          {{ "result_write_mmio", ⊥ }}.

        Definition sep_contract_decode    : SepContractFunX decode :=
          {{ ⊤ }}
            fn decode ["bv" :: ty_xlenbits] ty_ast
          {{ "result_decode", ⊤ }}.

        Definition sep_contract_externalWorldUpdates    : SepContractFunX externalWorldUpdates :=
          {{ mip ↦ term_var "vmip" }}
            fn externalWorldUpdates [] ty.unit
          {{ "result_externalWorldUpdates", ∃ "nvmip", mip ↦ term_var "nvmip" }}
          with ["vmip" :: ty_Minterrupts].

        Definition sep_contract_powered_on : SepContractFunX powered_on :=
          {{ ⊥ }}
            fn powered_on [] ty.bool
          {{ "result_powered_on", ⊥ }}.

        Definition contract_environment_foreign : SepContractEnvEx :=
          fun Δ τ fn =>
            match fn with
            | read_ram bytes       => sep_contract_read_ram bytes
            | write_ram bytes      => sep_contract_write_ram bytes
            | @within_mmio bytes H => @sep_contract_within_mmio bytes H
            | mmio_read bytes      => sep_contract_mmio_read bytes
            | mmio_write bytes     => sep_contract_mmio_write bytes
            | decode               => sep_contract_decode
            | externalWorldUpdates => sep_contract_externalWorldUpdates
            | powered_on           => sep_contract_powered_on
            end.

        Lemma linted_contract_environment_foreign :
          forall Δ τ (fn : FunX Δ τ),
            Linted (contract_environment_foreign fn).
        Proof.
          intros ? ? []; try constructor.
        Qed.
      End ForeignDef.

      Section LemDef.
        Import RiscvPmpSignature.notations.
        Import RiscvNotations.
        Import RiscvPmpSignature.ContractNotations.

        Definition lemma_open_gprs : SepLemma open_gprs :=
          {{ asn_gprs }}
            lem open_gprs []
          {{ asn_regs_ptsto }}.

        Definition lemma_close_gprs : SepLemma close_gprs :=
          {{ asn_regs_ptsto }}
            lem close_gprs []
          {{ asn_gprs }}.

        Definition lemma_open_ptsto_instr : SepLemma open_ptsto_instr :=
          {{ ⊤ }}
            lem open_ptsto_instr [paddr :: ty_xlenbits]
          {{ ⊤ }}.

        Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
          {{ ⊤ }}
            lem close_ptsto_instr [paddr :: ty_xlenbits; w :: ty_word]
          {{ ⊤ }}.

        Definition lemma_open_pmp_entries : SepLemma open_pmp_entries :=
          {{ asn_pmp_entries (term_var "entries") }}
            lem open_pmp_entries []
          {{ ∃ "cfg0", ∃ "addr0", ∃ "cfg1", ∃ "addr1",
             (pmp0cfg ↦ term_var "cfg0" ∗ pmpaddr0 ↦ term_var "addr0" ∗
              pmp1cfg ↦ term_var "cfg1" ∗ pmpaddr1 ↦ term_var "addr1" ∗
              asn_expand_pmpcfg_ent (term_var "cfg0") ∗
              asn_expand_pmpcfg_ent (term_var "cfg1") ∗
              term_var "entries" = term_list [(term_var "cfg0" ,ₜ term_var "addr0");
                                              (term_var "cfg1" ,ₜ term_var "addr1")]) }}
          with ["entries" :: ty.list ty_pmpentry].

        Definition lemma_close_pmp_entries : SepLemma close_pmp_entries :=
          {{ pmp0cfg ↦ term_var "cfg0" ∗ pmpaddr0 ↦ term_var "addr0" ∗
             pmp1cfg ↦ term_var "cfg1" ∗ pmpaddr1 ↦ term_var "addr1" }}
            lem close_pmp_entries []
          {{ asn_pmp_entries (term_list [(term_var "cfg0" ,ₜ term_var "addr0");
             (term_var "cfg1" ,ₜ term_var "addr1")]) }}
          with ["cfg0" :: ty_pmpcfg_ent; "addr0" :: _; "cfg1" :: ty_pmpcfg_ent; "addr1" :: _].

        Definition lemma_extract_pmp_ptsto (bytes : nat) : SepLemma (extract_pmp_ptsto bytes) :=
          let Σ := [paddr :: ty_xlenbits; acc :: ty_access_type; "entries" :: ty.list ty_pmpentry; p :: ty_privilege] in
          let bv_bytes : Term Σ _ := term_val ty_xlenbits (Bitvector.bv.of_nat bytes) in
          {{ let paddr_int : Term _ ty.int := term_unsigned (term_var paddr) in
             asn_pmp_addr_access (term_var "entries") (term_var p)
             ∗ term_val ty.int (Z.of_N minAddr) <= paddr_int
             ∗ (term_binop bop.plus paddr_int (term_val ty.int (Z.of_nat bytes))) <= term_val ty.int (Z.of_N maxAddr)
             ∗ asn_pmp_access (term_var paddr) bv_bytes (term_var "entries") (term_var p) (term_var acc) }}
            lem (extract_pmp_ptsto bytes) [paddr :: ty_xlenbits]
          {{ asn_pmp_addr_access_without (term_var paddr) bytes (term_var "entries") (term_var p)
             ∗ ∃ "w", asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]) }}
          with [acc :: ty_access_type; "entries" :: ty.list ty_pmpentry; p :: ty_privilege].

        Definition lemma_return_pmp_ptsto (bytes : nat) : SepLemma (return_pmp_ptsto bytes) :=
          let Σ := [paddr :: ty_xlenbits; "entries" :: ty.list ty_pmpentry; p :: ty_privilege] in
          let bv_bytes : Term Σ _ := term_val ty_xlenbits (Bitvector.bv.of_nat bytes) in
          {{ asn_pmp_addr_access_without (term_var paddr) bytes (term_var "entries") (term_var p)
             ∗ ∃ "w", asn.chunk (chunk_user (ptstomem bytes) [term_var "paddr"; term_var "w"]) }}
            lem (return_pmp_ptsto bytes) [paddr :: ty_xlenbits]
          {{ asn_pmp_addr_access (term_var "entries") (term_var p) }}
          with ["entries" :: ty.list ty_pmpentry; p :: ty_privilege].

        Definition lemma_close_mmio_write (immm : Bitvector.bv.bv 12) (widthh : WordWidth): SepLemma (close_mmio_write immm widthh) :=
          {{ ⊤ }}
            lem (close_mmio_write immm widthh) ["paddr" :: ty_xlenbits; "r" :: ty_regno]
          {{ ⊤ }}
          with ["w" :: ty_xlenbits].

        Definition lemma_environment : LemmaEnv :=
          fun Δ l =>
            match l with
            | open_gprs               => lemma_open_gprs
            | close_gprs              => lemma_close_gprs
            | open_pmp_entries        => lemma_open_pmp_entries
            | close_pmp_entries       => lemma_close_pmp_entries
            | open_ptsto_instr        => lemma_open_ptsto_instr
            | close_ptsto_instr       => lemma_close_ptsto_instr
            | extract_pmp_ptsto bytes => lemma_extract_pmp_ptsto bytes
            | return_pmp_ptsto bytes  => lemma_return_pmp_ptsto bytes
            | close_mmio_write immm widthh => lemma_close_mmio_write immm widthh
            end.

      End LemDef.

    End ContractDefKit.

  #[export] Instance riscvpmp_universal_contract_specification : Specification :=
    {| CEnv   := contract_environment;
       CEnvEx := contract_environment_foreign;
       LEnv   := lemma_environment;
       fail_rule_pre := true;
    |}.

End RiscvPmpSpecification.

Module RiscvPmpValidContracts.
  Import RiscvPmpProgramLogic.
  Import RiscvPmpExecutor.
  Import RiscvPmpShallowExec.

  Inductive Fuel : Set :=
  | NoInlining
  | InlineOneLevel
  | InlineMoreLevels (n : nat).

  Definition fuel_to_nat (f : Fuel) : nat :=
    match f with
    | NoInlining     => 1
    | InlineOneLevel => 2
    | InlineMoreLevels n => n
    end.

  Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractReflect c (FunDef f)
    | None   => False
    end.

  Definition ValidContractWithErasure {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractWithErasure c (FunDef f)
    | None   => False
    end.

  Definition ValidContractWithFuel {Δ τ} (fuel : Fuel) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractReflectWithFuel (fuel_to_nat fuel) c (FunDef f)
    | None   => False
    end.

  Definition ValidContractDebug {Δ τ} (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContract c (FunDef f)
    | None => False
    end.

  Definition ValidContractDebugWithFuel {Δ τ} (fuel : Fuel) (f : Fun Δ τ) : Prop :=
    match CEnv f with
    | Some c => Symbolic.ValidContractWithFuel (fuel_to_nat fuel) c (FunDef f)
    | None   => False
    end.

  Ltac symbolic_simpl :=
    apply Symbolic.validcontract_with_erasure_sound;
    vm_compute;
    constructor;
    cbn.

  Section Debug.
    Coercion stm_exp : Exp >-> Stm.
    Local Notation "'use' 'lemma' lem args" := (stm_lemma lem args%env) (at level 10, lem at next level) : exp_scope.
    Local Notation "'use' 'lemma' lem" := (stm_lemma lem env.nil) (at level 10, lem at next level) : exp_scope.

    Import RiscvNotations.
    Import RiscvμSailNotations.
    Import SymProp.notations.
    Import asn.notations.
    Import rv_notations.

  End Debug.

  (* TODO: proof with new PMP addressing mode (NA4) *)
  Lemma valid_contract_pmpCheck (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@pmpCheck bytes H).
  Proof.
    destruct H; now vm_compute.
  Qed.

  Lemma valid_contract_step : ValidContractDebugWithFuel (InlineMoreLevels 4) step.
  Proof.
    apply Symbolic.validcontract_reflect_fuel_sound; vm_reflexivity.
  Qed.

  Lemma valid_contract_pmpWriteCfgReg : ValidContract pmpWriteCfgReg.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_pmpWriteCfg : ValidContract pmpWriteCfg.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_pmpWriteAddr : ValidContract pmpWriteAddr.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_init_model : ValidContract init_model.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_fetch : ValidContract fetch.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute : ValidContract execute.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_init_sys : ValidContract init_sys.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_init_pmp : ValidContract init_pmp.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_handle_mem_exception : ValidContract handle_mem_exception.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_mem_write_value (bytes : nat) {H : restrict_bytes bytes} : ValidContract (@mem_write_value bytes H).
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_mem_read (bytes : nat) {H : restrict_bytes bytes} : ValidContract (@mem_read bytes H).
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_checked_mem_read (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@checked_mem_read bytes H).
  Proof. destruct H; symbolic_simpl; eauto. Qed.

  (* TODO: remove? *)
  (* Lemma valid_contract_checked_mem_read_shallow (bytes : nat) : Shallow.ValidContract (sep_contract_checked_mem_read bytes) (fun_checked_mem_read bytes). *)
  (* Proof. *)
  (*   econstructor. *)
  (*   cbv [CPureSpecM.pure *)
  (*          CPureSpecM.bind *)
  (*          CHeapSpecM.bind *)
  (*          CHeapSpecM.bind_right *)
  (*          CHeapSpecM.consume *)
  (*          CHeapSpecM.lift_purem *)
  (*          CHeapSpecM.assert_eq_nenv *)
  (*          CPureSpecM.angelic]. *)
  (*   exists (Z.of_nat bytes). *)
  (*   cbv [inst inst_store inst_env inst_chunk]. *)
  (*   cbv [evals eval]. *)
  (*   compute. *)
  (* Admitted. *)

  (* Lemma valid_contract_checked_mem_read (bytes : nat) : ValidContractDebug (checked_mem_read bytes). *)
  (* Proof with trivial. *)
    (* apply Symbolic.validcontract_with_erasure_sound. *)
    (* compute. *)
    (* constructor. *)
    (* cbn. *)
    (* intros acc paddr p entries Hsub Hacc **. *)
    (* exists acc. split... exists acc. split... split... *)
  (* Admitted. *)

  Lemma valid_contract_checked_mem_write (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@checked_mem_write bytes H).
  Proof. destruct H; symbolic_simpl; eauto. Qed.

  Lemma valid_contract_pmp_mem_read (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@pmp_mem_read bytes H).
  Proof. destruct H; now vm_compute. Qed.

  Lemma valid_contract_pmp_mem_write (bytes : nat) {H : restrict_bytes bytes} : ValidContractDebug (@pmp_mem_write bytes H).
  Proof.
    destruct H; symbolic_simpl;
      intros; (split; intros; [now exists Write|now exists ReadWrite]).
  Qed.

  Lemma valid_contract_pmpCheckRWX : ValidContract pmpCheckRWX.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_pmpCheckPerms : ValidContract pmpCheckPerms.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_pmpAddrRange : ValidContract pmpAddrRange.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_pmpMatchAddr : ValidContractDebug pmpMatchAddr.
  Proof.
    symbolic_simpl.
    intros; split; intros; bv_comp;
      repeat match goal with
        | H : _ <=ᵘ _ |- _ => apply bv.ule_iff_unsigned_le in H
        | H : _ <ᵘ _ |- _ => apply bv.ult_iff_unsigned_lt in H
        end; lia.
  Qed.

  Lemma valid_contract_pmpMatchEntry : ValidContract pmpMatchEntry.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_pmpLocked : ValidContract pmpLocked.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_readCSR : ValidContractWithFuel InlineOneLevel readCSR.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_writeCSR : ValidContractWithFuel (InlineMoreLevels 2) writeCSR.
  Proof. vm_reflexivity. Qed.

  (* Lemma valid_contract_check_CSR : ValidContract check_CSR.
  Proof. vm_reflexivity. Qed. *)

  Lemma valid_contract_is_CSR_defined : ValidContract is_CSR_defined.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_check_CSR_access : ValidContract check_CSR_access.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_csrAccess : ValidContract csrAccess.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_csrPriv : ValidContract csrPriv.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_privLevel_to_bits : ValidContract privLevel_to_bits.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_trap_handler : ValidContract trap_handler.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_prepare_trap_vector : ValidContract prepare_trap_vector.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_tvec_addr : ValidContract tvec_addr.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exceptionType_to_bits : ValidContract exceptionType_to_bits.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_Medeleg_to_bits : ValidContract Medeleg_to_bits.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exception_delegatee : ValidContractWithFuel InlineOneLevel exception_delegatee.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_exception_handler : ValidContract exception_handler.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_handle_illegal : ValidContract handle_illegal.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_get_arch_pc : ValidContract get_arch_pc.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_get_next_pc : ValidContract get_next_pc.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_set_next_pc : ValidContract set_next_pc.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_tick_pc : ValidContract tick_pc.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_to_bits (l : nat) : ValidContract (to_bits l).
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_rX : ValidContract rX.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_wX : ValidContract wX.
  Proof. vm_reflexivity. Qed.

  (* Lemma valid_contract_abs : ValidContract abs. *)
  (* Proof. now vm_compute. Qed. *)

  Lemma valid_contract_within_phys_mem : ValidContractDebug within_phys_mem.
  Proof.
    apply Symbolic.validcontract_with_erasure_sound.
    vm_compute. constructor. cbn. intros.
    lia.
  Qed.

  Lemma valid_contract_execute_RTYPE : ValidContractWithFuel InlineOneLevel execute_RTYPE.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_ITYPE : ValidContractWithFuel InlineOneLevel execute_ITYPE.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_SHIFTIOP : ValidContractWithFuel InlineOneLevel execute_SHIFTIOP.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_UTYPE : ValidContract execute_UTYPE.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_BTYPE : ValidContract execute_BTYPE.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_RISCV_JAL : ValidContract execute_RISCV_JAL.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_RISCV_JALR : ValidContract execute_RISCV_JALR.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_ECALL : ValidContract execute_ECALL.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_EBREAK : ValidContractDebug execute_EBREAK.
  Proof. now symbolic_simpl. Qed.

  Lemma valid_contract_execute_SRET : ValidContract execute_SRET.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_MRET : ValidContract execute_MRET.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_STORE : ValidContract execute_STORE.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_LOAD : ValidContractWithFuel InlineOneLevel execute_LOAD.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_CSR : ValidContract execute_CSR.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_MUL : ValidContract execute_MUL.
  Proof. vm_reflexivity. Qed.

  Lemma valid_contract_execute_ILLEGAL : ValidContract execute_ILLEGAL.
  Proof. vm_reflexivity. Qed.

  Lemma pmp_check_perms_gives_access :
    forall acc p L0 A0 X0 W0 R0,
      Pmp_check_perms {| L := L0; A := A0; X := X0; W := W0; R := R0 |} acc p ->
      decide_access_pmp_perm acc
                             (pmp_get_perms {| L := L0; A := A0; X := X0; W := W0; R := R0 |} p) = true.
  Proof.
    intros; destruct p, acc, L0, X0, W0, R0;
      simpl; cbv in H; subst; auto.
  Qed.

  Open Scope N_scope.

  Lemma valid_contract : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContract f ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContract in Hvc.
    rewrite Hcenv in Hvc.
    exists 1%nat.
    apply Symbolic.validcontract_reflect_sound.
    apply Hvc.
  Qed.

  Lemma valid_contract_with_fuel : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ) (fuel : Fuel),
      CEnv f = Some c ->
      ValidContractWithFuel fuel f ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? f c fuel Hcenv Hvc.
    unfold ValidContractWithFuel in Hvc.
    rewrite Hcenv in Hvc.
    exists (fuel_to_nat fuel).
    now apply Symbolic.validcontract_reflect_fuel_sound.
  Qed.

  Lemma valid_contract_debug : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      ValidContractDebug f ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? f c Hcenv Hvc.
    unfold ValidContractDebug in Hvc.
    rewrite Hcenv in Hvc.
    exists 1%nat.
    apply Hvc.
  Qed.

  Lemma valid_contract_debug_with_fuel : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ) (fuel : Fuel),
      CEnv f = Some c ->
      ValidContractDebugWithFuel fuel f ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros ? ? f c fuel Hcenv Hvc.
    unfold ValidContractDebugWithFuel in Hvc.
    rewrite Hcenv in Hvc.
    exists (fuel_to_nat fuel).
    apply Hvc.
  Qed.

  Lemma ValidContracts : forall {Δ τ} (f : Fun Δ τ) (c : SepContract Δ τ),
      CEnv f = Some c ->
      exists fuel, Symbolic.ValidContractWithFuel fuel c (FunDef f).
  Proof.
    intros Δ τ f c H.
    destruct f; try solve [cbn in H; discriminate]. (* Only those f for which a contract is defined need to be proven valid *)
    - refine (valid_contract _ H valid_contract_rX).
    - refine (valid_contract _ H valid_contract_wX).
    - refine (valid_contract _ H valid_contract_get_arch_pc).
    - refine (valid_contract _ H valid_contract_get_next_pc).
    - refine (valid_contract _ H valid_contract_set_next_pc).
    - refine (valid_contract _ H valid_contract_tick_pc).
    - refine (valid_contract _ H (valid_contract_to_bits l)).
    - refine (valid_contract_debug _ H valid_contract_within_phys_mem).
    - refine (valid_contract _ H (@valid_contract_mem_read bytes H0)).
    - refine (valid_contract_debug _ H (@valid_contract_checked_mem_read bytes H0)).
    - refine (valid_contract_debug _ H (@valid_contract_checked_mem_write bytes H0)).
    - refine (valid_contract_debug _ H (@valid_contract_pmp_mem_read bytes H0)).
    - refine (valid_contract_debug _ H (@valid_contract_pmp_mem_write bytes H0)).
    - refine (valid_contract _ H valid_contract_pmpLocked).
    - refine (valid_contract _ H valid_contract_pmpWriteCfgReg).
    - refine (valid_contract _ H valid_contract_pmpWriteCfg).
    - refine (valid_contract _ H valid_contract_pmpWriteAddr).
    - refine (valid_contract_debug _ H valid_contract_pmpCheck).
    - refine (valid_contract _ H valid_contract_pmpCheckPerms).
    - refine (valid_contract _ H valid_contract_pmpCheckRWX).
    - refine (valid_contract _ H valid_contract_pmpMatchEntry).
    - refine (valid_contract _ H valid_contract_pmpAddrRange).
    - refine (valid_contract_debug _ H valid_contract_pmpMatchAddr).
    - refine (valid_contract _ H (@valid_contract_mem_write_value bytes H0)).
    - refine (valid_contract _ H valid_contract_init_model).
    - refine (valid_contract_debug_with_fuel _ _ H valid_contract_step).
    - refine (valid_contract _ H valid_contract_fetch).
    - refine (valid_contract _ H valid_contract_init_sys).
    - refine (valid_contract _ H valid_contract_init_pmp).
    - refine (valid_contract _ H valid_contract_exceptionType_to_bits).
    - refine (valid_contract _ H valid_contract_Medeleg_to_bits).
    - refine (valid_contract _ H valid_contract_privLevel_to_bits).
    - refine (valid_contract _ H valid_contract_handle_mem_exception).
    - refine (valid_contract _ H valid_contract_exception_handler).
    - refine (valid_contract_with_fuel _ _ H valid_contract_exception_delegatee).
    - refine (valid_contract _ H valid_contract_trap_handler).
    - refine (valid_contract _ H valid_contract_prepare_trap_vector).
    - refine (valid_contract _ H valid_contract_tvec_addr).
    - refine (valid_contract _ H valid_contract_handle_illegal).
    - refine (valid_contract _ H valid_contract_is_CSR_defined).
    - refine (valid_contract _ H valid_contract_csrAccess).
    - refine (valid_contract _ H valid_contract_csrPriv).
    - refine (valid_contract _ H valid_contract_check_CSR_access).
    - refine (valid_contract_with_fuel _ _ H valid_contract_readCSR).
    - refine (valid_contract_with_fuel _ _ H valid_contract_writeCSR).
    - refine (valid_contract _ H valid_contract_execute).
    - refine (valid_contract_with_fuel _ _ H valid_contract_execute_RTYPE).
    - refine (valid_contract_with_fuel _ _ H valid_contract_execute_ITYPE).
    - refine (valid_contract_with_fuel _ _ H valid_contract_execute_SHIFTIOP).
    - refine (valid_contract _ H valid_contract_execute_UTYPE).
    - refine (valid_contract _ H valid_contract_execute_BTYPE).
    - refine (valid_contract _ H valid_contract_execute_RISCV_JAL).
    - refine (valid_contract _ H valid_contract_execute_RISCV_JALR).
    - refine (valid_contract_with_fuel _ _ H valid_contract_execute_LOAD).
    - refine (valid_contract _ H valid_contract_execute_STORE).
    - refine (valid_contract _ H valid_contract_execute_ECALL).
    - refine (valid_contract_debug _ H valid_contract_execute_EBREAK).
    - refine (valid_contract _ H valid_contract_execute_SRET).
    - refine (valid_contract _ H valid_contract_execute_MRET).
    - refine (valid_contract _ H valid_contract_execute_CSR).
    - refine (valid_contract _ H valid_contract_execute_MUL).
    - refine (valid_contract _ H valid_contract_execute_ILLEGAL).
  Qed.
End RiscvPmpValidContracts.
