/-
Tactic shims that replace the bits of Mathlib the C02 development relied on.
-/

import Lean4AnalysisTao.MyClassical

namespace MyUtil

theorem not_and_or
    (p q : Prop) :
    ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  · intro h
    rcases MyClassical.em p with hp | hnp
    · exact Or.inr (fun hq => h ⟨hp, hq⟩)
    · exact Or.inl hnp
  · intro hor ⟨hp, hq⟩
    rcases hor with h | h
    · exact h hp
    · exact h hq

end MyUtil

export MyUtil (not_and_or)

/--
`by_contra h`; assume `¬ goal` as hypothesis `h` and derive `False`.
If the goal is already `¬P`, just `intro h` (no classical reasoning needed).
-/
macro "by_contra " h:ident : tactic =>
  `(tactic|
    first
    | intro $h:ident
    | (apply MyClassical.byContradiction; intro $h:ident))

/-- `by_contra`; assume `¬ goal` as hypothesis `h` (default name). -/
macro "by_contra" : tactic =>
  `(tactic|
    first
    | intro h
    | (apply MyClassical.byContradiction; intro h))

/--
`use x₁, …, xₙ`; provide witnesses for a goal built from `Exists`/`And`
anonymous constructors. After refining, tries `rfl`/`assumption` to close
any residual goal (mirroring Mathlib's convenience behaviour).
-/
macro "use " xs:term,+ : tactic =>
  `(tactic| (refine ⟨$xs,*, ?_⟩ <;> first | rfl | assumption | skip))
