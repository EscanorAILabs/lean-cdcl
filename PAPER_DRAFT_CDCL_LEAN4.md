# Machine-Checked Formalization of Conflict-Driven Clause Learning in Lean 4

**Author:** Escanor AI Labs (Frontier Automated Reasoning Group)  
**Target Venues:** *International Conference on Interactive Theorem Proving (ITP)* / *Certified Programs and Proofs (CPP)* / *Theory and Applications of Satisfiability Testing (SAT)* / *Journal of Automated Reasoning (JAR)*

---

## Abstract

Boolean Satisfiability (SAT) solvers based on the Conflict-Driven Clause Learning (CDCL) paradigm constitute the computational core of modern automated reasoning, hardware verification, and software synthesis. While empirical solver efficiency has been extensively refined over the past two decades, verifying their formal correctness within dependent type theory remains essential for certified theorem proving. We present **LeanCDCL**, a formalization in the Lean 4 interactive theorem prover certifying the semantic correctness, unit propagation invariants, and clause-learning mechanisms of CDCL. Specifically, we establish machine-checked proofs that Boolean Constraint Propagation (BCP) preserves satisfiability, that 1-UIP conflict resolution clauses are logical consequences of the initial formula, and that solver output (SAT or UNSAT) is unconditionally sound. All definitions and core lemmas are verified by the Lean 4 kernel without external trust dependencies.

---

## 1. Introduction

The propositional satisfiability problem (SAT) is the canonical NP-complete decision problem. Despite worst-case exponential bounds, modern SAT solvers routinely resolve industrial instances involving millions of variables and clauses. This breakthrough relies on the **CDCL (Conflict-Driven Clause Learning)** algorithm, which augments the classical Davis-Putnam-Logemann-Loveland (DPLL) procedure with:
1. Two-watched-literals unit propagation (Boolean Constraint Propagation),
2. Implication graph analysis to extract asserting conflict clauses (First Unique Implication Point, 1-UIP),
3. Non-chronological backtracking (backjumping), and
4. Dynamic variable selection heuristics (VSIDS).

While solvers such as CaDiCaL, Kissat, and MiniSat generate UNSAT certificates (DRAT/LRAT) to be verified post-hoc by proof checkers, establishing **in-kernel, verified implementations** in interactive theorem provers eliminates external translation overhead and guarantees proof soundness by construction.

In this work, we present a modular Lean 4 formalization of CDCL semantics and invariants. Our contributions are:
- A purely functional formalization of CNF semantics, partial assignments, and unit clauses in Lean 4 (`Basic.lean`).
- Machine-checked proofs that unit propagation preserves semantic satisfiability (`UnitPropagation.lean`).
- Formalization of clause addition invariance and global solver soundness (`ClauseLearning.lean`).

---

## 2. Formal Semantic Framework

### 2.1 Literals and Clauses
Variables are represented by natural numbers $\mathbb{N}$. A literal $l \in \text{Lit}$ is either positive or negative:
```lean
inductive Lit where
  | pos (v : Nat) : Lit
  | neg (v : Nat) : Lit
```
A clause $C$ is a list of literals, and a formula $F$ is a list of clauses in Conjunctive Normal Form (CNF).

### 2.2 Truth Assignments and Satisfaction
A partial assignment $A : \text{Assignment}$ maps variable indices to optional boolean values (`Option Bool`).
Semantic satisfaction is formalized constructively:
- A literal $l = \text{pos}(v)$ is satisfied by $A$ if $A(v) = \text{some true}$.
- A clause $C$ is satisfied if $\exists l \in C$, $A \models l$.
- A formula $F$ is satisfied if $\forall C \in F$, $A \models C$.

We formally prove:
```lean
theorem empty_clause_unsat (a : Assignment) :
    satisfies_clause a [] = false
```
establishing that the derivation of an empty clause certifies global unsatisfiability.

---

## 3. Soundness of Unit Propagation

Unit propagation identifies clauses where all literals except one are falsified under assignment $A$, forcing the remaining literal to evaluate to `true`.

We formalize the unit predicate and prove the fundamental transition invariant:
```lean
theorem unit_prop_soundness (a : Assignment) (c : Clause) (l : Lit) :
    is_unit_clause a c = some l →
    (∀ a', satisfies_clause a' c = true → 
           assignment_agrees a a' → 
           satisfies_lit a' l = true)
```
Consequently, adding forced unit assignments does not discard any satisfying models of the original CNF formula:
```lean
theorem unit_prop_preserves_sat (f : Formula) (a : Assignment) (l : Lit) :
    (∃ c ∈ f, is_unit_clause a c = some l) →
    (∃ a', satisfies_formula a' f = true ∧ assignment_agrees a a') →
    (∃ a', satisfies_formula a' f = true ∧ assignment_agrees (assign a l.var (lit_val l)) a')
```

---

## 4. Conflict Analysis and 1-UIP Clause Learning

When a conflict occurs (i.e., a clause is falsified under the current assignment trail), the solver constructs an implication graph whose vertices are assigned literals and directed edges represent antecedent clauses.

The 1-UIP scheme selects the unique implication point closest to the conflict literal. We prove that any clause derived by resolution on antecedent implication clauses is a semantic entailment of the input formula:
```lean
theorem add_implied_preserves_sat (f : Formula) (c : Clause) :
    (∀ a, satisfies_formula a f = true → satisfies_clause a c = true) →
    ((∃ a, satisfies_formula a f = true) ↔ 
     (∃ a, satisfies_formula a (c :: f) = true))
```

### Main Soundness Result:
From these modular building blocks, we obtain the master soundness theorems:
```lean
theorem cdcl_soundness_sat (f : Formula) (a : Assignment) :
    cdcl_solve f = .sat a → satisfies_formula a f = true

theorem cdcl_soundness_unsat (f : Formula) :
    cdcl_solve f = .unsat → ∀ a, satisfies_formula a f = false
```

---

## 5. Related Work and Comparison

Previous verified SAT projects include:
- **JinjaThreads & IsaSAT (Isabelle/HOL):** Highly optimized verified SAT solver with imperative data structures by Blanchette, Fleury, and Weidenbach.
- **Coq SAT checkers:** Certified DRAT checkers by Cruz-Filipe et al.
- **Lean 3 / Lean 4 SAT:** Verified resolution certificate checkers and encoding frameworks.

LeanCDCL distinguishes itself by targeting direct integration with Lean 4's macro and metaprogramming pipeline, making verified SAT reasoning accessible natively inside `simp` and tactic automation without external binary invocations.

---

## 6. Conclusion and Future Work

LeanCDCL provides a concise, mathematically certified foundation for CDCL solving in Lean 4. Future extensions include formalizing two-watched-literal pointer arithmetic using Lean 4 array invariants and contributing these foundational lemmas to the core Mathlib formal verification library.
