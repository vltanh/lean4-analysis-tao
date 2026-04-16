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
    · exact Or.inr (fun hq => h (And.intro hp hq))
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
    | refine MyClassical.byContradiction _ (fun $h:ident => ?_))

/-- `by_contra`; assume `¬ goal` as hypothesis `h` (default name). -/
macro "by_contra" : tactic =>
  `(tactic|
    first
    | intro h
    | refine MyClassical.byContradiction _ (fun h => ?_))

/--
`use x₁, …, xₙ`; provide witnesses for a goal built from `Exists`/`And`
anonymous constructors, leaving a single `?_` for the residual obligation.
-/
macro "use " xs:term,+ : tactic =>
  `(tactic| refine ⟨$xs,*, ?_⟩)
