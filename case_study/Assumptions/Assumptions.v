
Require
  Katamaran.MinimalCaps.LoopVerification
  Katamaran.RiscvPmp.Everything
  Katamaran.RiscvPmp.FemtoKernel.
Import Stdlib.Numbers.BinNums Stdlib.Strings.String Bitvector.

Goal True. idtac "Assumptions of MinimalCaps universal contract:". Abort.
Print Assumptions MinimalCaps.LoopVerification.valid_semContract_loop2.

Goal True. idtac "Assumptions of Risc-V PMP universal contract (left instance):". Abort.
Print Assumptions RiscvPmp.Everything.LoopVerificationl.valid_semTriple_loop.

Goal True. idtac "Assumptions of Risc-V PMP universal contract (right instance):". Abort.
Print Assumptions RiscvPmp.Everything.LoopVerificationr.valid_semTriple_loop.

Goal True. idtac "Assumptions of Risc-V PMP binary universal contract:". Abort.
Print Assumptions RiscvPmp.Everything.LoopVerificationBinary.valid_semTriple_loop.

Goal True. idtac "Assumptions of femtokernel integrity end-to-end theorem:". Abort.
Print Assumptions RiscvPmp.FemtoKernel.femtokernel_endToEnd.

Goal True. idtac "Assumptions of relational FemtoKernel verification:". Abort.
Print Assumptions RiscvPmp.FemtoKernel.femtokernel_init_safe_rel.

Goal True. idtac "Assumptions of femtokernel relational end-to-end theorem:". Abort.
Print Assumptions RiscvPmp.FemtoKernel.femtokernel_rel_endToEnd.
