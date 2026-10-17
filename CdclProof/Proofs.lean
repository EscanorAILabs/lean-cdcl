/-
  CdclProof.Proofs — Théorèmes prouvés et exemples concrets
-/

import CdclProof.Basic
import CdclProof.UnitPropagation
import CdclProof.ClauseLearning

namespace CdclProof

-- ── Exemple 1: UNSAT trivial (x) ∧ (¬x) ──

/-- La formule (x) ∧ (¬x) est UNSAT -/
theorem unsat_trivial :
    is_unsat [[{ var := "x", negated := false }], [{ var := "x", negated := true }]] := by
  intro a
  simp [is_unsat, satisfies_formula, satisfies_clause, satisfies_lit]

-- ── Exemple 2: SAT trivial (x ∨ y) ──

/-- La formule (x ∨ y) est SAT -/
theorem sat_trivial :
    is_satisfiable [[{ var := "x", negated := false }, { var := "y", negated := false }]] := by
  exact ⟨fun _ => true, by simp [satisfies_formula, satisfies_clause, satisfies_lit]⟩

-- ── Exemple 3: L'unit propagation est sound sur un exemple concret ──

/-- Si on a la clause (x ∨ y) et x est faux, alors y doit être vrai ──
    C'est l'essence de l'unit propagation. -/
theorem unit_prop_example (a : Assignment)
    (h_x_false : a "x" = false) :
    satisfies_clause a [{ var := "x", negated := false }, { var := "y", negated := false }] = true →
    a "y" = true := by
  intro h
  simp [satisfies_clause, satisfies_lit] at h
  rcases h with h_x | h_y
  · rw [h_x] at h_x_false; contradiction
  · exact h_y

-- ── Exemple 4: La clause apprise préserve la satisfiability ──

/-- Ajouter une tautologie (clause toujours vraie) préserve la satisfiability ──
    Une tautologie est impliquée par n'importe quelle formule. -/
theorem tautology_preserves_sat (f : Formula) (v : Var) :
    implied_by f [{ var := v, negated := false }, { var := v, negated := true }] := by
  intro a h_sat
  by_cases h : a v = true
  · exact clause_sat_if_lit_sat a _ _ (List.mem_cons_self _ _) (by simp [satisfies_lit, h])
  · exact clause_sat_if_lit_sat a _ _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
      (by simp [satisfies_lit, h])

-- ── Résumé des théorèmes prouvés ──

/-!
  Théorèmes prouvés dans CdclProof:

  1. Basic.lean:
     - lit_neg_not_both, lit_neg_iff, empty_clause_unsat
     - clause_sat_if_lit_sat, clause_sat_exists_lit

  2. UnitPropagation.lean:
     - falsifies_implies_not_satisfied, not_falsified_implies_satisfied
     - unit_prop_soundness (sans sorry)
     - unit_prop_preserves_sat (1 sorry: cas polarité opposée)

  3. ClauseLearning.lean:
     - add_implied_preserves_sat (forward + backward + iff)
     - learned_clause_implied, backtrack_preserves_sat
     - cdcl_soundness_sat, cdcl_soundness_unsat, cdcl_completeness

  4. Proofs.lean:
     - unsat_trivial, sat_trivial, unit_prop_example, tautology_preserves_sat

  Sorries restants: 1 (cas edge polarité opposée dans unit_prop_preserves_sat)
-/

end CdclProof
