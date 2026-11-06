(* Size statistics of the verification conditions of the RiscvPmp case study:
   the raw symbolic execution tree vs. the VC after postprocessing. *)

From Stdlib Require Import
     NArith.NArith
     Strings.String
     Lists.List.
From Katamaran Require Import
     Base
     Bitvector
     RiscvPmp.Machine
     RiscvPmp.Logic
     RiscvPmp.Contracts.

Import Sig.RiscvPmpSignature.
Import RiscvPmpProgram.
Import Contracts.RiscvPmpSpecification.
Import RiscvPmpProgramLogic.
Import RiscvPmpExecutor.
Import Symbolic.Statistics.

Ltac show name t :=
  let r := eval vm_compute in (vc_stats_to_list t) in idtac name r.

Goal forall (l bytes : nat) (H : restrict_bytes bytes), True.
  intros l bytes H.
  Time show "VCSTAT rX fuel=1" (vc_stats 1 rX).
  Time show "VCSTAT wX fuel=1" (vc_stats 1 wX).
  Time show "VCSTAT get_arch_pc fuel=1" (vc_stats 1 get_arch_pc).
  Time show "VCSTAT get_next_pc fuel=1" (vc_stats 1 get_next_pc).
  Time show "VCSTAT set_next_pc fuel=1" (vc_stats 1 set_next_pc).
  Time show "VCSTAT tick_pc fuel=1" (vc_stats 1 tick_pc).
  Time show "VCSTAT to_bits fuel=1" (vc_stats 1 (to_bits l)).
  Time show "VCSTAT within_phys_mem fuel=1" (vc_stats 1 within_phys_mem).
  Time show "VCSTAT mem_read fuel=1" (vc_stats 1 (@mem_read bytes H)).
  Time show "VCSTAT checked_mem_read_1 fuel=1" (vc_stats 1 (@checked_mem_read 1 restrict_bytes_one)).
  Time show "VCSTAT checked_mem_read_2 fuel=1" (vc_stats 1 (@checked_mem_read 2 restrict_bytes_two)).
  Time show "VCSTAT checked_mem_read_4 fuel=1" (vc_stats 1 (@checked_mem_read 4 restrict_bytes_four)).
  Time show "VCSTAT checked_mem_write_1 fuel=1" (vc_stats 1 (@checked_mem_write 1 restrict_bytes_one)).
  Time show "VCSTAT checked_mem_write_2 fuel=1" (vc_stats 1 (@checked_mem_write 2 restrict_bytes_two)).
  Time show "VCSTAT checked_mem_write_4 fuel=1" (vc_stats 1 (@checked_mem_write 4 restrict_bytes_four)).
  Time show "VCSTAT pmp_mem_read_1 fuel=1" (vc_stats 1 (@pmp_mem_read 1 restrict_bytes_one)).
  Time show "VCSTAT pmp_mem_read_2 fuel=1" (vc_stats 1 (@pmp_mem_read 2 restrict_bytes_two)).
  Time show "VCSTAT pmp_mem_read_4 fuel=1" (vc_stats 1 (@pmp_mem_read 4 restrict_bytes_four)).
  Time show "VCSTAT pmp_mem_write_1 fuel=1" (vc_stats 1 (@pmp_mem_write 1 restrict_bytes_one)).
  Time show "VCSTAT pmp_mem_write_2 fuel=1" (vc_stats 1 (@pmp_mem_write 2 restrict_bytes_two)).
  Time show "VCSTAT pmp_mem_write_4 fuel=1" (vc_stats 1 (@pmp_mem_write 4 restrict_bytes_four)).
  Time show "VCSTAT pmpLocked fuel=1" (vc_stats 1 pmpLocked).
  Time show "VCSTAT pmpWriteCfgReg fuel=1" (vc_stats 1 pmpWriteCfgReg).
  Time show "VCSTAT pmpWriteCfg fuel=1" (vc_stats 1 pmpWriteCfg).
  Time show "VCSTAT pmpWriteAddr fuel=1" (vc_stats 1 pmpWriteAddr).
  Time show "VCSTAT pmpCheck_1 fuel=1" (vc_stats 1 (@pmpCheck 1 restrict_bytes_one)).
  Time show "VCSTAT pmpCheck_2 fuel=1" (vc_stats 1 (@pmpCheck 2 restrict_bytes_two)).
  Time show "VCSTAT pmpCheck_4 fuel=1" (vc_stats 1 (@pmpCheck 4 restrict_bytes_four)).
  Time show "VCSTAT pmpCheckPerms fuel=1" (vc_stats 1 pmpCheckPerms).
  Time show "VCSTAT pmpCheckRWX fuel=1" (vc_stats 1 pmpCheckRWX).
  Time show "VCSTAT pmpMatchEntry fuel=1" (vc_stats 1 pmpMatchEntry).
  Time show "VCSTAT pmpAddrRange fuel=1" (vc_stats 1 pmpAddrRange).
  Time show "VCSTAT pmpMatchAddr fuel=1" (vc_stats 1 pmpMatchAddr).
  Time show "VCSTAT mem_write_value fuel=1" (vc_stats 1 (@mem_write_value 4 restrict_bytes_four)).
  Time show "VCSTAT init_model fuel=1" (vc_stats 1 init_model).
  Time show "VCSTAT step fuel=4" (vc_stats 4 step).
  Time show "VCSTAT fetch fuel=1" (vc_stats 1 fetch).
  Time show "VCSTAT init_sys fuel=1" (vc_stats 1 init_sys).
  Time show "VCSTAT init_pmp fuel=1" (vc_stats 1 init_pmp).
  Time show "VCSTAT exceptionType_to_bits fuel=1" (vc_stats 1 exceptionType_to_bits).
  Time show "VCSTAT Medeleg_to_bits fuel=1" (vc_stats 1 Medeleg_to_bits).
  Time show "VCSTAT privLevel_to_bits fuel=1" (vc_stats 1 privLevel_to_bits).
  Time show "VCSTAT handle_mem_exception fuel=1" (vc_stats 1 handle_mem_exception).
  Time show "VCSTAT exception_handler fuel=1" (vc_stats 1 exception_handler).
  Time show "VCSTAT exception_delegatee fuel=2" (vc_stats 2 exception_delegatee).
  Time show "VCSTAT trap_handler fuel=1" (vc_stats 1 trap_handler).
  Time show "VCSTAT prepare_trap_vector fuel=1" (vc_stats 1 prepare_trap_vector).
  Time show "VCSTAT tvec_addr fuel=1" (vc_stats 1 tvec_addr).
  Time show "VCSTAT handle_illegal fuel=1" (vc_stats 1 handle_illegal).
  Time show "VCSTAT is_CSR_defined fuel=1" (vc_stats 1 is_CSR_defined).
  Time show "VCSTAT csrAccess fuel=1" (vc_stats 1 csrAccess).
  Time show "VCSTAT csrPriv fuel=1" (vc_stats 1 csrPriv).
  Time show "VCSTAT check_CSR_access fuel=1" (vc_stats 1 check_CSR_access).
  Time show "VCSTAT readCSR fuel=2" (vc_stats 2 readCSR).
  Time show "VCSTAT writeCSR fuel=2" (vc_stats 2 writeCSR).
  Time show "VCSTAT execute fuel=1" (vc_stats 1 execute).
  Time show "VCSTAT execute_RTYPE fuel=2" (vc_stats 2 execute_RTYPE).
  Time show "VCSTAT execute_ITYPE fuel=2" (vc_stats 2 execute_ITYPE).
  Time show "VCSTAT execute_SHIFTIOP fuel=2" (vc_stats 2 execute_SHIFTIOP).
  Time show "VCSTAT execute_UTYPE fuel=1" (vc_stats 1 execute_UTYPE).
  Time show "VCSTAT execute_BTYPE fuel=1" (vc_stats 1 execute_BTYPE).
  Time show "VCSTAT execute_RISCV_JAL fuel=1" (vc_stats 1 execute_RISCV_JAL).
  Time show "VCSTAT execute_RISCV_JALR fuel=1" (vc_stats 1 execute_RISCV_JALR).
  Time show "VCSTAT execute_LOAD fuel=2" (vc_stats 2 execute_LOAD).
  Time show "VCSTAT execute_STORE fuel=1" (vc_stats 1 execute_STORE).
  Time show "VCSTAT execute_ECALL fuel=1" (vc_stats 1 execute_ECALL).
  Time show "VCSTAT execute_EBREAK fuel=1" (vc_stats 1 execute_EBREAK).
  Time show "VCSTAT execute_SRET fuel=1" (vc_stats 1 execute_SRET).
  Time show "VCSTAT execute_MRET fuel=1" (vc_stats 1 execute_MRET).
  Time show "VCSTAT execute_CSR fuel=1" (vc_stats 1 execute_CSR).
  Time show "VCSTAT execute_MUL fuel=1" (vc_stats 1 execute_MUL).
  Time show "VCSTAT execute_ILLEGAL fuel=1" (vc_stats 1 execute_ILLEGAL).
Abort.
