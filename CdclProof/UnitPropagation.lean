/-
  CdclProof.UnitPropagation — Soundness de l'unit propagation

  Principe: si une clause a tous ses littéraux sauf un assignés à faux,
  alors le littéral restant DOIT être vrai dans toute assignation satisfaisant
  la formule. L'assigner à vrai préserve donc la satisfiability.
-/

import CdclProof.Basic

namespace CdclProof

-- ── Définitions pour l'unit propagation ──

/-- Un littéral est falsifié par une assignation si sa valeur est l'opposé -/
def falsifies_lit (a : Assignment) (l : Lit) : Bool :=
  if l.negated then a l.var else !(a l.var)

/-- Si un littéral est falsifié, il n'est pas satisfait -/
theorem falsifies_implies_not_satisfied (a : Assignment) (l : Lit) :
    falsifies_lit a l = true → satisfies_lit a l = false := by
  intro h
  cases l.negated
  · simp [falsifies_lit] at h; simp [satisfies_lit, h]
  · simp [falsifies_lit] at h; simp [satisfies_lit, h]

/-- Si un littéral n'est pas falsifié (assignation totale), il est satisfait -/
theorem not_falsified_implies_satisfied (a : Assignment) (l : Lit) :
    falsifies_lit a l = false → satisfies_lit a l = true := by
  intro h
  cases l.negated
  · simp [falsifies_lit] at h; simp [satisfies_lit, h]
  · simp [falsifies_lit] at h; simp [satisfies_lit, h]

/-- Si une clause est unitaire et satisfaite, le littéral non-falsifié est satisfait -/
theorem unit_prop_soundness (a : Assignment) (c : Clause) (l : Lit)
    (h_mem : l ∈ c)
    (h_only : ∀ l' ∈ c, l' ≠ l → falsifies_lit a l' = true)
    (h_sat : satisfies_clause a c = true) :
    satisfies_lit a l = true := by
  by_cases h : satisfies_lit a l = true
  · exact h
  · exfalso
    have h_l_falsified : falsifies_lit a l = true := by
      cases l.negated
      · simp [falsifies_lit, satisfies_lit] at *; exact h
      · simp [falsifies_lit, satisfies_lit] at *; exact h
    have h_all_falsified : ∀ l' ∈ c, falsifies_lit a l' = true := by
      intro l' h_mem'
      by_cases h_eq : l' = l
      · rw [h_eq]; exact h_l_falsified
      · exact h_only l' h_mem' h_eq
    have h_none_sat : ∀ l' ∈ c, satisfies_lit a l' = false := by
      intro l' h_mem'
      exact falsifies_implies_not_satisfied a l' (h_all_falsified l' h_mem')
    simp [satisfies_clause] at h_sat
    rcases h_sat with ⟨l', h_mem', h_sat'⟩
    have h_ns := h_none_sat l' h_mem'
    rw [h_sat'] at h_ns
    contradiction

/-- L'unit propagation préserve la satisfiability:
    Si a satisfait f, et c ∈ f avec l comme seul littéral non-falsifié,
    alors a étendue avec l satisfait encore f. -/
theorem unit_prop_preserves_sat (a : Assignment) (f : Formula) (c : Clause) (l : Lit)
    (h_clause : c ∈ f)
    (h_l_in_c : l ∈ c)
    (h_l_unfalsified : falsifies_lit a l = false)
    (h_only_unfalsified : ∀ l' ∈ c, l' ≠ l → falsifies_lit a l' = true)
    (h_sat : satisfies_formula a f = true) :
    satisfies_formula (fun v => if v = l.var then !l.negated else a v) f = true := by
  simp [satisfies_formula] at h_sat ⊢
  intro c' h_c'_in_f
  by_cases h_eq : c' = c
  · subst h_eq
    have h_sat_l : satisfies_lit (fun v => if v = l.var then !l.negated else a v) l = true := by
      simp [satisfies_lit]
    exact clause_sat_if_lit_sat _ _ _ h_l_in_c h_sat_l
  · have h_c'_sat : satisfies_clause a c' = true := h_sat c' h_c'_in_f
    rcases clause_sat_exists_lit a c' h_c'_sat with ⟨l', h_mem', h_sat'⟩
    by_cases h_var_eq : l'.var = l.var
    · by_cases h_same_neg : l'.negated = l.negated
      · have h_l'_eq_l : l' = l := by
          cases l' with | mk v1 n1 =>
          cases l with | mk v2 n2 =>
          have hv : v1 = v2 := h_var_eq
          have hn : n1 = n2 := h_same_neg
          rw [hv, hn]
        subst h_l'_eq_l
        have h_sat_l : satisfies_lit (fun v => if v = l'.var then !l'.negated else a v) l' = true := by
          simp [satisfies_lit]
        exact clause_sat_if_lit_sat _ _ _ h_mem' h_sat_l
      · sorry
    · have h_sat_l' : satisfies_lit (fun v => if v = l.var then !l.negated else a v) l' = true := by
        cases hn : l'.negated with
        | false => simp [satisfies_lit, hn, h_var_eq] at h_sat' ⊢; exact h_sat'
        | true => simp [satisfies_lit, hn, h_var_eq] at h_sat' ⊢; exact h_sat'
      exact clause_sat_if_lit_sat _ _ _ h_mem' h_sat_l'

end CdclProof
