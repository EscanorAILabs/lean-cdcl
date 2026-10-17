/-
  CdclProof.Basic — Définitions de base: littéraux, clauses, formules, assignations

  On formalise la sémantique SAT en Lean 4:
  - Une variable est un identifiant (String)
  - Un littéral est une variable + une polarité
  - Une clause est une liste de littéraux (disjonction)
  - Une formule est une liste de clauses (conjonction)
  - Une assignation est une fonction variable → bool

  On définit la satisfaction: quand est-ce qu'une assignation satisfait un littéral,
  une clause, une formule.
-/

namespace CdclProof

-- ── Types de base ──

/-- Une variable propositionnelle est identifiée par son nom -/
abbrev Var := String

/-- Un littéral: variable + polarité (true = positif, false = négatif) -/
structure Lit where
  var : Var
  negated : Bool
  deriving DecidableEq, Repr

/-- L'opposé d'un littéral -/
def Lit.neg (l : Lit) : Lit :=
  { l with negated := !l.negated }

/-- Une clause est une disjonction de littéraux -/
abbrev Clause := List Lit

/-- Une formule est une conjonction de clauses -/
abbrev Formula := List Clause

/-- Une assignation: variable → valeur de vérité -/
abbrev Assignment := Var → Bool

-- ── Sémantique: satisfaction ──

/-- Une assignation a satisfait un littéral l si:
    - l est positif et a(l.var) = true, ou
    - l est négatif et a(l.var) = false -/
def satisfies_lit (a : Assignment) (l : Lit) : Bool :=
  if l.negated then
    !(a l.var)
  else
    a l.var

/-- Une assignation a satisfait une clause c si au moins un littéral de c est satisfait -/
def satisfies_clause (a : Assignment) (c : Clause) : Bool :=
  c.any (satisfies_lit a)

/-- Une assignation a satisfait une formule f si toutes les clauses de f sont satisfaites -/
def satisfies_formula (a : Assignment) (f : Formula) : Bool :=
  f.all (satisfies_clause a)

-- ── Définitions dérivées ──

/-- Une formule est satisfiable s'il existe une assignation qui la satisfait -/
def is_satisfiable (f : Formula) : Prop :=
  ∃ a : Assignment, satisfies_formula a f = true

/-- Une formule est insatisfiable (UNSAT) si aucune assignation ne la satisfait -/
def is_unsat (f : Formula) : Prop :=
  ∀ a : Assignment, satisfies_formula a f = false

-- ── Lemmes de base sur la satisfaction ──

@[simp]
theorem satisfies_lit_pos (a : Assignment) (v : Var) :
    satisfies_lit a { var := v, negated := false } = a v := by
  simp [satisfies_lit]

@[simp]
theorem satisfies_lit_neg (a : Assignment) (v : Var) :
    satisfies_lit a { var := v, negated := true } = !(a v) := by
  simp [satisfies_lit]

/-- Un littéral et son opposé ne peuvent pas être satisfaits simultanément -/
theorem lit_neg_not_both (a : Assignment) (l : Lit) :
    satisfies_lit a l = true → satisfies_lit a l.neg = false := by
  intro h
  cases l.negated
  · simp [satisfies_lit, Lit.neg] at h ⊢
    simp [h]
  · simp [satisfies_lit, Lit.neg] at h ⊢
    simp [h]

/-- Si un littéral est satisfait, son opposé ne l'est pas -/
theorem lit_neg_iff (a : Assignment) (l : Lit) :
    satisfies_lit a l = true ↔ satisfies_lit a l.neg = false := by
  constructor
  · exact lit_neg_not_both a l
  · intro h
    cases l.negated
    · simp [satisfies_lit, Lit.neg] at h ⊢
      simp [h]
    · simp [satisfies_lit, Lit.neg] at h ⊢
      simp [h]

/-- Une clause vide n'est jamais satisfaite -/
theorem empty_clause_unsat (a : Assignment) :
    satisfies_clause a [] = false := by
  simp [satisfies_clause]

/-- Une clause avec un littéral satisfait est satisfaite -/
theorem clause_sat_if_lit_sat (a : Assignment) (c : Clause) (l : Lit) :
    l ∈ c → satisfies_lit a l = true → satisfies_clause a c = true := by
  intro h_mem h_sat
  simp [satisfies_clause]
  exact ⟨l, h_mem, h_sat⟩

/-- Si une clause est satisfaite, au moins un de ses littéraux est satisfait -/
theorem clause_sat_exists_lit (a : Assignment) (c : Clause) :
    satisfies_clause a c = true → ∃ l ∈ c, satisfies_lit a l = true := by
  intro h
  simp [satisfies_clause] at h
  exact h

end CdclProof
