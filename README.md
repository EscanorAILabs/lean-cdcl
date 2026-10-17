# LeanCDCL: Machine-Checked Formalization of CDCL SAT Solver Soundness in Lean 4

This project provides a clean, machine-checked formalization of the fundamental algorithms powering modern Conflict-Driven Clause Learning (CDCL) Boolean Satisfiability (SAT) solvers within the Lean 4 interactive theorem prover.

---

## 🎯 Scope and Formal Objectives

Modern SAT solvers combine Boolean Constraint Propagation (BCP / Unit Propagation) with First Unique Implication Point (1-UIP) conflict analysis and non-chronological backtracking. While highly optimized in C/C++ implementations (e.g., MiniSat, CaDiCaL, Kissat), formal verification guarantees total correctness (*soundness* and *completeness*) down to kernel-checked proofs.

This library formalizes:
1. **Core Semantics (`Basic.lean`):** Literals, clauses, CNF formulas, truth assignments, and semantic satisfaction.
2. **Unit Propagation (`UnitPropagation.lean`):** Soundness and satisfiability preservation under iterative Boolean unit resolution.
3. **Clause Learning and Backtracking (`ClauseLearning.lean`):** Semantic preservation when asserting implied conflict clauses generated via 1-UIP resolution cuts.
4. **Solver Soundness & Verification (`Proofs.lean`):** Formal guarantees that `cdcl_soundness_sat` (models satisfy original formulas) and `cdcl_soundness_unsat` (refutations imply semantic unsatisfiability).

---

## 📁 Repository Structure

```
01_brique_cdcl_lean4/
├── lakefile.lean             # Lake build system configuration
├── lean-toolchain            # Lean version pin (v4.14.0)
├── README.md                 # Project documentation
├── PAPER_DRAFT_CDCL_LEAN4.md # Formal paper draft (ITP/CPP/SAT)
├── GUIDE_VALIDATION_ZULIP... # Community submission and Zulip roadmap
└── CdclProof/
    ├── Basic.lean            # Semantic foundations (Literals, Clauses, SAT)
    ├── UnitPropagation.lean  # BCP soundness and state transition invariants
    ├── ClauseLearning.lean   # 1-UIP assertion and non-chronological backtrack
    └── Proofs.lean           # End-to-end soundness theorems and unit checks
```

---

## 🛠️ Verification and Build

Ensure you have Lean 4 installed via `elan`. Then run:

```bash
lake update
lake build
```

Expected output:
```text
Build completed successfully.
```

---

## 🔬 Core Formal Theorems

| Module | Theorem | Formal Statement / Significance |
|---|---|---|
| `Basic` | `lit_neg_not_both` | `satisfies_lit a l = true → satisfies_lit a l.neg = false` |
| `Basic` | `empty_clause_unsat` | `satisfies_clause a [] = false` (Contradiction) |
| `Basic` | `clause_sat_exists_lit` | Clause satisfaction implies existence of a satisfied literal |
| `UnitPropagation` | `unit_prop_soundness` | Unit clause requires assigning the unique unassigned literal |
| `UnitPropagation` | `unit_prop_preserves_sat` | Propagation preserves the satisfiability set of the CNF |
| `ClauseLearning` | `add_implied_preserves_sat` | Adding an implied lemma is equi-satisfiable with the original CNF |
| `ClauseLearning` | `cdcl_soundness_sat` | If solver yields SAT with model $M$, then $M \models F$ |
| `ClauseLearning` | `cdcl_soundness_unsat` | If solver yields UNSAT, $F$ is semantically unsatisfiable |
| `ClauseLearning` | `cdcl_completeness` | Totality of decision procedure under terminating search |

---

## 📌 Status and Mathlib Roadmap

- Core algebraic structures and Boolean assignment lemmas: **100% Verified (0 sorry)**.
- 1-UIP trail resolution graph formalization: Active development for direct inclusion in the upstream Mathlib formal verification ecosystem.
