import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals
import Lean4AnalysisTao.C03_SetTheory.S02_RussellParadox_Extras

-- Axiom 3.9 (Universal specification / comprehension).
-- "Dangerous!"; see Russell's paradox below; this axiom is inconsistent with
-- the rest of the set-theoretic axioms, so it is quarantined in its own
-- namespace and is NOT used elsewhere in the project.
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

-- Russell's predicate: "γ is MySet α for some α, and the would-be-set does
-- not contain itself."
noncomputable def P
    {γ : Type} :
    γ → Prop :=
  fun x => ∃ (α : Type), (γ = MySet α) ∧ x ∉ x

-- Tao's illustration that `P ({2,3,4})` holds: the set `{2,3,4}` is not one
-- of the natural numbers `2, 3, 4`, so it is not an element of itself.
-- Formally we use `MySet.mem_singleton_obj` (the cross-type form of Axiom
-- 3.4) together with `MySet.type_ne` (both from `S02_RussellParadox_Extras`).
example :
    P (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : MySet Nat) := by
  use Nat
  refine And.intro rfl ?_
  intro hself
  have aux : ∀ (n : Nat),
      (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : MySet Nat) ∉ (⦃n⦄ : MySet Nat) := by
    intro n hmem
    rw [MySet.mem_singleton_obj n (⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ : MySet Nat)] at hmem
    have htype : MySet Nat = Nat :=
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

-- Axiom 3.10 (Regularity / Foundation).
-- If A is a non-empty set then A has an element which is either not a set,
-- or is disjoint from A.
axiom MySet.regularity
    {α : Type}
    (A : MySet α) :
    A.nonempty →
    (∃ (x : MySet α), x ∈ A ∧ MySet.disjoint x A)
    ∨ (∃ (ν : Type) (x : ν), x ∈ A ∧ ν ≠ MySet α)

section Exercises

-- Exercise 3.2.1
-- The universal specification axiom implies Axioms 3.3, 3.4, 3.5, 3.6, 3.7
-- (and, assuming natural numbers are objects, Axiom 3.8).
-- We illustrate with the empty-set axiom (3.3); the remaining derivations
-- are analogous and are left to the solutions file.
example :
    ∃ (E : MySet MyNat), ∀ (x : MyNat), x ∉ E := by
  sorry

-- Exercise 3.2.2
-- Using regularity (and singleton), if A is a set then A ∉ A.
example
    (A : MySet MyNat) :
    A ∉ A := by
  sorry

-- Furthermore, for any two sets A and B, either A ∉ B or B ∉ A.
example
    (A B : MySet MyNat) :
    A ∉ B ∨ B ∉ A := by
  sorry

-- Exercise 3.2.3
-- The universal specification axiom is equivalent to postulating a universal
-- set Ω containing every object. We state the forward direction here:
-- if Axiom 3.9 holds, then a universal set exists.
example :
    ∃ (Ω : MySet MyNat), ∀ (x : MyNat), x ∈ Ω := by
  sorry

end Exercises
