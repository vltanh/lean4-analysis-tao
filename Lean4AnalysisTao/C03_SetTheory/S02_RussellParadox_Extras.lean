import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals

/-!
Scaffolding for §3.2. Tao's membership axioms quantify over every object in
one informal universe; the typed §3.1 versions only handle same-type
elements. §3.2 needs the cross-type reading, so we add object-level forms
here (via `HEq`) plus the type-hierarchy fact `MySet α ≠ α`.
-/

namespace MySet

-- Axiom 3.4 (singleton), stated "for every object y".
axiom mem_singleton_obj
    {α γ : Type}
    (a : α)
    {β : Type}
    (y : β) :
    y ∈ (⦃a⦄ : γ) ↔ HEq y a

-- Axiom 3.4 (pair), stated "for every object y".
axiom mem_pair_obj
    {α γ : Type}
    (a b : α)
    {β : Type}
    (y : β) :
    y ∈ (⦃a, b⦄ : γ) ↔ HEq y a ∨ HEq y b

-- Cross-type intersection membership; object-level analogue of Axiom 3.6.
axiom mem_inter_obj
    {α : Type}
    (S₁ S₂ : MySet α)
    {β : Type}
    (y : β) :
    y ∈ S₁ ∩ S₂ ↔ y ∈ S₁ ∧ y ∈ S₂

-- Type hierarchy: `MySet α` is not itself `α`.
axiom type_ne
    (α : Type) :
    MySet α ≠ α

end MySet
