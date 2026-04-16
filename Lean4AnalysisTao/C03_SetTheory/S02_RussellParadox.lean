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
    P (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : MySet Nat) := by
  use Nat
  refine And.intro rfl ?_
  intro hself
  have aux
      (n : Nat)
      (hmem : (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : MySet Nat) ∈ (⦃n⦄ : MySet Nat)) :
      False := by
    rw [MySet.mem_singleton_obj n (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : MySet Nat)] at hmem
    have htype :
        MySet Nat = Nat :=
      type_eq_of_heq hmem
    exact MySet.type_ne Nat htype
  rw [MySet.mem_union (⦃2⦄ ∪ ⦃3⦄) ⦃4⦄ (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : MySet Nat)] at hself
  rcases hself with h12 | h4
  · rw [MySet.mem_union (⦃2⦄ : MySet Nat) ⦃3⦄ (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : MySet Nat)] at h12
    rcases h12 with h2 | h3
    · exact aux 2 h2
    · exact aux 3 h3
  · exact aux 4 h4

end Example

end Axiom_3_9

-- Axiom 3.10 (Regularity).
axiom MySet.regularity
    {α : Type}
    (A : MySet α)
    (hA : (MySet.nonempty A)) :
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
