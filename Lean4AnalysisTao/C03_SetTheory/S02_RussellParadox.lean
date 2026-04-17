import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals
import Lean4AnalysisTao.C03_SetTheory.S02_RussellParadox_Extras

-- Axiom 3.9 (Universal specification). Inconsistent with the other set
-- axioms (Russell's paradox below); quarantined in its own namespace.
namespace Axiom_3_9

axiom MySet.univ_spec
    {α : Type}
    (P : α → Prop) :
    MySet α
notation:max "⦃|" P:max "⦄" => MySet.univ_spec P

axiom MySet.mem_univ_spec
    {α : Type}
    (P : α → Prop)
    (x : α) :
    x ∈ ⦃|P⦄ ↔ P x

namespace Example

-- Russell's predicate.
noncomputable def P
    {γ : Type} :
    γ → Prop :=
  fun x => ∃ (α : Type), (γ = MySet α) ∧ x ∉ x

example :
    P (⦃𝟚⦄ ∪ ⦃𝟛⦄ ∪ ⦃𝟜⦄ : MySet MyNat) := by
  use MyNat
  refine And.intro rfl ?_
  intro hself
  have aux
      (n : MyNat)
      (hmem : (⦃𝟚⦄ ∪ ⦃𝟛⦄ ∪ ⦃𝟜⦄ : MySet MyNat) ∈ (⦃n⦄ : MySet MyNat)) :
      False := by
    rw [MySet.mem_singleton_obj n (⦃𝟚⦄ ∪ ⦃𝟛⦄ ∪ ⦃𝟜⦄ : MySet MyNat)] at hmem
    have htype :
        MySet MyNat = MyNat :=
      type_eq_of_heq hmem
    exact MySet.type_ne MyNat htype
  rw [MySet.mem_union (⦃𝟚⦄ ∪ ⦃𝟛⦄) ⦃𝟜⦄ (⦃𝟚⦄ ∪ ⦃𝟛⦄ ∪ ⦃𝟜⦄ : MySet MyNat)] at hself
  rcases hself with h12 | h4
  · rw [MySet.mem_union (⦃𝟚⦄ : MySet MyNat) ⦃𝟛⦄ (⦃𝟚⦄ ∪ ⦃𝟛⦄ ∪ ⦃𝟜⦄ : MySet MyNat)] at h12
    rcases h12 with h2 | h3
    · exact aux 𝟚 h2
    · exact aux 𝟛 h3
  · exact aux 𝟜 h4

end Example

end Axiom_3_9

-- Axiom 3.10 (Regularity).
axiom MySet.regularity
    {α : Type}
    (A : MySet α)
    (hA : MySet.nonempty A) :
    (∃ (x : MySet α), x ∈ A ∧ MySet.disjoint x A)
    ∨ (∃ (ν : Type) (x : ν), x ∈ A ∧ ν ≠ MySet α)

section Exercises

-- Exercise 3.2.1
example :
    ∃ (E : MySet MyNat), ∀ (x : MyNat), x ∉ E := by
  sorry

-- Exercise 3.2.2
example
    (A : MySet MyNat) :
    A ∉ A := by
  sorry

example
    (A B : MySet MyNat) :
    A ∉ B ∨ B ∉ A := by
  sorry

-- Exercise 3.2.3
example :
    ∃ (Ω : MySet MyNat), ∀ (x : MyNat), x ∈ Ω := by
  sorry

end Exercises
