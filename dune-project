(lang dune 3.21)
(using rocq 0.11)

(license BSD-2-Clause)
(maintainers "Steven Keuchel <steven.keuchel@vub.be>")
(authors "Dominique Devriese" "Georgy Lukyanov" "Sander Huyghebaert" "Steven Keuchel")
(source (github katamaran-project/katamaran))
(homepage "https://katamaran-project.github.io/")

(version 0.2.0)

(package
 (name rocq-katamaran)
 (synopsis "Separation logic-based verification of instruction sets")
 (description "Katamaran is a semi-automated separation logic verifier for
the Sail specification language. It works on an embedded
version of Sail called Sail and verifies separation
logic-based contracts of functions by generating (succinct)
first-order verification conditions. It further comes with a
complete model based on the Iris separation logic
framework.")
 (tags
  ("keyword:program verification"
   "keyword:separation logic"
   "keyword:symbolic execution"
   "keyword:instruction sets"
   "category:Computer Science/Semantics and Compilation/Semantics"
   "logpath:Katamaran"))
 (depends
  (rocq-core      (and (>= 9.2)    (< 9.4)))
  (rocq-stdlib    (>= 9.0))
  (rocq-equations (and (>= 1.3.2)  (< 1.4)))
  (rocq-iris      (and (>= 4.5.0)  (< 4.6)))
  (rocq-stdpp     (and (>= 1.13.0) (< 1.14)))))

(package
 (name rocq-katamaran-minimalcaps)
 (synopsis "Katamaran case study: MinimalCaps, a minimal capability machine")
 (tags ("logpath:Katamaran.MinimalCaps"))
 (depends (rocq-katamaran (= :version))))

(package
 (name rocq-katamaran-riscvpmp)
 (synopsis "Katamaran case study: RISC-V with physical memory protection")
 (tags ("logpath:Katamaran.RiscvPmp"))
 (depends (rocq-katamaran (= :version))))

(package
 (name rocq-katamaran-gvt)
 (synopsis "Katamaran example: GVT on top of the RiscvPmp case study")
 (tags ("logpath:Katamaran.RiscvPmp.GVT"))
 (depends (rocq-katamaran-riscvpmp (= :version))))
