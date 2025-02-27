import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals

namespace Axiom_3_9

axiom MySet.univ_spec.{u} {α : Type u} (P : α → Prop) : MySet α
notation:max "⦃|" P:max "⦄" => MySet.univ_spec P

axiom MySet.mem_univ_spec.{u} {α : Type u} (P : α → Prop) (x : α) :
  x ∈ ⦃|P⦄ ↔ P x

namespace Example

noncomputable def P {γ : Type u} : γ → Prop :=
  fun x => ∃ (α : Type u), (γ = MySet α) ∧ x ∉ x

example (h : γ = MySet ℕ) : P (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : γ) := by
  use ℕ
  constructor
  · exact h
  · intro h'
    rw [MySet.mem_union (⦃2⦄ ∪ ⦃3⦄) ⦃4⦄ (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄)] at h'
    rw [MySet.mem_union ⦃2⦄ ⦃3⦄ (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄)] at h'
    rcases h' with (h1 | h2)
    · rcases h1 with (h11 | h12)
      · sorry
      · sorry
    · sorry

end Example

end Axiom_3_9

-- Axiom 3.10
axiom MySet.regularity.{u} {α : Type u} :
  ∀ (A : MySet α), A.nonempty →
  (∃ (x : MySet α), x ∈ A ∧ MySet.disjoint x A)
  ∨ (∃ (ν : Type u) (x : ν), x ∈ A ∧ ν ≠ MySet α)
