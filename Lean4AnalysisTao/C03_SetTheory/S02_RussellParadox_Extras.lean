import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals

/-!
Scaffolding for §3.2 (Russell's Paradox).

Tao's Axiom 3.4 (and the related membership axioms) quantify over every
*object* in a single informal universe. In our typed encoding, the versions
in §3.1 (`MySet.mem_singleton`, `MySet.mem_pair`) quantify only over
same-type elements; they are correct but strictly weaker than Tao's
statement. For §3.2 we need the cross-type reading: a `MySet ℕ` cannot be
an element of a `MySet ℕ` singleton built from a `ℕ`.

We restore the missing content here (not in the main §3.1 file, since these
are formalization-side reinforcements of axioms that Tao states once and for
all at the level of objects):

* `MySet.mem_singleton_obj`, `MySet.mem_pair_obj`; strengthen Axioms 3.4 by
  quantifying over `y : β` for any `β`, using `HEq y a` (heterogeneous
  equality) in place of `y = a`.
* `MySet.type_ne`; the type-hierarchy fact that `MySet α` is not itself
  `α` (sets and their elements live at different levels of the hierarchy;
  Tao informally relies on this throughout §3.2).
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

-- Cross-type intersection membership (object-level form).
-- Derived-in-spirit from Axiom 3.6 (specification) quantified over objects,
-- but our `MySet.mem_spec` is restricted to same-type; this axiom fills the
-- gap so cross-type elements interact with `∩` the way §3.2 needs.
axiom mem_inter_obj
    {α : Type}
    (S₁ S₂ : MySet α)
    {β : Type}
    (y : β) :
    y ∈ S₁ ∩ S₂ ↔ y ∈ S₁ ∧ y ∈ S₂

-- Type hierarchy: a set of α-objects is not itself an α-object.
axiom type_ne
    (α : Type) :
    MySet α ≠ α

end MySet
