/-
A self-contained classical reasoning layer.

Rebuilds the pieces of Lean's `Classical` namespace that this project uses,
starting from our own `choice` axiom. This is strictly a pedagogical mirror:
`propext` and `funext` still come from Lean core (they are not derivable from
choice alone), but no piece of the Classical API itself is reused.
-/

universe u v

namespace MyClassical

/-- Axiom of choice: from a proof that `α` is inhabited, pick an element. -/
axiom choice {α : Sort u} : Nonempty α → α

/-- Given `∃ x, p x`, produce a subtype witness. -/
noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop)
    (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

/-- Given `∃ x, p x`, pick such an `x`. -/
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

/-- The chosen element satisfies the predicate. -/
theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property

/--
Excluded middle, via Diaconescu's theorem.

Uses `choice` together with `propext` and `funext` from Lean core.
-/
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hut, hvf]
      Or.inl hne
  have p_implies_uv : p → u = v := fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) := fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) := fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h

theorem byContradiction {p : Prop} (h : ¬p → False) : p :=
  (em p).elim id (fun hnp => (h hnp).elim)

end MyClassical
