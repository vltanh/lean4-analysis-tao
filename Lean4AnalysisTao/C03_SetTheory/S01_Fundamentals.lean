import Mathlib.Tactic.ByContra

universe u
variable {α β γ : Type u}

-- Axiom 3.1
axiom MySet (α : Type u) : Type u

-- Definition 3.1.1
axiom MySet.mem : γ → α → Prop
notation:50 x:50 " ∈ " S:50 => MySet.mem S x
notation:50 x:50 " ∉ " S:50 => ¬ (x ∈ S)

-- Axiom 3.2
axiom MySet.ext {A B : MySet α} :
  A = B ↔ (∀ (x : α), x ∈ A ↔ x ∈ B)

-- Axiom 3.3
axiom MySet.empty {α : Type u} : MySet α
notation:max "∅" => MySet.empty

axiom MySet.not_mem_empty :
  ∀ (x : α), x ∉ (∅ : MySet α)

def MySet.nonempty (S : MySet α) : Prop :=
  S ≠ ∅

-- Lemma 3.1.5
theorem MySet.single_choice {A : MySet α} (h : MySet.nonempty A) :
  ∃ (x : α), x ∈ A := by
  by_contra hxnA
  push_neg at hxnA
  have hxnemp : ∀ (x : α), ¬x ∈ (∅ : MySet α) := by
    intro x
    exact MySet.not_mem_empty x
  have : ∀ (x : α), x ∈ A ↔ x ∈ (∅ : MySet α) := by
    intro x
    exact iff_of_false (hxnA x) (hxnemp x)
  have : A = ∅ := MySet.ext.mpr this
  exact h this

-- Axiom 3.4
axiom MySet.singleton (a : α) : MySet α
notation:max "⦃" a:max "⦄" => MySet.singleton a

axiom MySet.mem_singleton (a : α) :
  ∀ (y : α), y ∈ ⦃a⦄ ↔ y = a

axiom MySet.pair (a b : α) : MySet α
notation:max "⦃" a:max "," b:max "⦄" => MySet.pair a b

axiom MySet.mem_pair (a b : α) :
  ∀ (y : α), y ∈ ⦃a, b⦄ ↔ y = a ∨ y = b

-- Remarks 3.1.8
example (a : α) :
  ∀ (S : MySet α),
    (∀ (y : α), y ∈ S ↔ y = a) → S = ⦃a⦄ := by
  sorry

example (a b : α) :
  ⦃a, b⦄ = ⦃b, a⦄ := by
  sorry

example (a : α) :
  ⦃a, a⦄ = ⦃a⦄ := by
  sorry

-- Example 3.1.9
example :
  ∅ ≠ ⦃(∅ : MySet α)⦄ := by
  sorry

example :
  ∅ ≠ ⦃⦃(∅ : MySet α)⦄⦄ := by
  sorry

example :
  ∅ ≠ ⦃∅, ⦃(∅ : MySet α)⦄⦄ := by
  sorry

example :
  ⦃∅⦄ ≠ ⦃⦃(∅ : MySet α)⦄⦄ := by
  sorry

example :
  ⦃∅⦄ ≠ ⦃∅, ⦃(∅ : MySet α)⦄⦄ := by
  sorry

example :
  ⦃⦃∅⦄⦄ ≠ ⦃∅, ⦃(∅ : MySet α)⦄⦄ := by
  sorry

-- Axiom 3.5
axiom MySet.union (A B : MySet α) : MySet α
infixl:65 " ∪ " => MySet.union

axiom MySet.mem_union (A B : MySet α) :
  ∀ (x : α), x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

-- Remark 3.1.11
example (A B : MySet α) (h : A = A') :
  A ∪ B = A' ∪ B := by
  -- Use Axiom 3.2 and Axiom 3.5
  sorry

example (A B : MySet α) (h : B = B') :
  A ∪ B = A ∪ B' := by
  -- Use Axiom 3.2 and Axiom 3.5
  sorry

-- Lemma 3.1.12
theorem MySet.pair_eq_union_singleton (a b : MySet α) :
  ⦃a, b⦄ = ⦃a⦄ ∪ ⦃b⦄ := by
  sorry

theorem MySet.union_comm (A B : MySet α) :
  A ∪ B = B ∪ A := by
  sorry

theorem MySet.union_assoc (A B C : MySet α) :
  (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  rw [MySet.ext]
  intro x
  constructor
  · intro h
    rw [MySet.mem_union (A ∪ B) C] at h
    rcases h with (h | h)
    · rw [MySet.mem_union A B] at h
      rcases h with (h | h)
      · rw [MySet.mem_union A (B ∪ C)]
        exact Or.inl h
      · rw [MySet.mem_union A (B ∪ C)]
        rw [MySet.mem_union B C]
        exact Or.inr (Or.inl h)
    · rw [MySet.mem_union A (B ∪ C)]
      rw [MySet.mem_union B C]
      exact Or.inr (Or.inr h)
  · intro h
    rw [MySet.mem_union A (B ∪ C)] at h
    rcases h with (h | h)
    · rw [MySet.mem_union (A ∪ B) C]
      rw [MySet.mem_union A B]
      exact Or.inl (Or.inl h)
    · rw [MySet.mem_union B C] at h
      rcases h with (h | h)
      · rw [MySet.mem_union (A ∪ B) C]
        rw [MySet.mem_union A B]
        exact Or.inl (Or.inr h)
      · rw [MySet.mem_union (A ∪ B) C]
        exact Or.inr h

theorem MySet.union_self (A : MySet α) :
  A ∪ A = A := by
  sorry

theorem MySet.union_empty (A : MySet α) :
  A ∪ ∅ = A := by
  sorry

theorem MySet.empty_union (A : MySet α) :
  ∅ ∪ A = A := by
  sorry

-- Definition 3.1.14
def MySet.subset (A B : MySet α) :=
  ∀ (x : α), x ∈ A → x ∈ B
infix:50 " ⊆ " => MySet.subset
notation A:50 " ⊊ " B:50 => A ⊆ B ∧ A ≠ B

-- Remark 3.1.15
example (A B : MySet α) (h : A = A') :
  A ⊆ B ↔ A' ⊆ B := by
  rw [h]

-- Example 3.1.16
example (A : MySet α) :
  A ⊆ A := by
  sorry

example (A : MySet α) :
  ∅ ⊆ A := by
  sorry

-- Proposition 3.1.17
theorem MySet.subset_trans (A B C : MySet α) :
  A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAB hBC
  rw [MySet.subset] at hAB
  rw [MySet.subset] at hBC
  rw [MySet.subset]
  intro x hxA
  have : x ∈ B := hAB x hxA
  have : x ∈ C := hBC x this
  exact this

theorem MySet.subset_antisymm (A B : MySet α) :
  A ⊆ B → B ⊆ A → A = B := by
  sorry

theorem MySet.proper_ss_of_proper_ss_of_proper_ss (A B C : MySet α) :
  A ⊊ B → B ⊊ C → A ⊊ C := by
  sorry

-- Axiom 3.6
axiom MySet.spec (A : MySet α) (P : α → Prop) : MySet α

axiom MySet.mem_spec (A : MySet α) (P : α → Prop) :
  ∀ (y : α), y ∈ MySet.spec A P ↔ y ∈ A ∧ P y

theorem MySet.spec_ss (A : MySet α) (P : α → Prop) :
  MySet.spec A P ⊆ A := by
  sorry

theorem MySet.spec_eq_spec_of_eq
  {A A' : MySet α} (P : α → Prop) (h : A = A') :
  MySet.spec A P = MySet.spec A' P := by
  sorry

-- Definition 3.1.22
noncomputable def MySet.inter (S₁ S₂ : MySet α) : MySet α :=
  MySet.spec S₁ (fun x => x ∈ S₂)
infixl:70 " ∩ " => MySet.inter

theorem MySet.mem_inter (S₁ S₂ : MySet α) :
  ∀ (x : α), x ∈ S₁ ∩ S₂ ↔ x ∈ S₁ ∧ x ∈ S₂ := by
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec S₁ (fun x => x ∈ S₂)]

def MySet.disjoint (A B : MySet α) : Prop :=
  A ∩ B = ∅

example : MySet.disjoint (∅ : MySet α) ∅ := by
  sorry

-- Definition 3.1.26
noncomputable def MySet.diff (A B : MySet α) : MySet α :=
  MySet.spec A (fun x => x ∉ B)
infix:70 " \\ " => MySet.diff

-- Proposition 3.1.27
-- (a)
-- See Lemma 3.1.12
-- theorem MySet.union_empty (A : Type) :
--   A ∪ ∅ = A := by
--   sorry

theorem MySet.inter_empty (A : MySet α) :
  A ∩ ∅ = ∅ := by
  sorry

-- (b)
theorem MySet.union_superset
  (X A : MySet α) (hA : A ⊆ X) :
  A ∪ X = X := by
  sorry

theorem MySet.inter_superset
  (X A : MySet α) (hA : A ⊆ X) :
  A ∩ X = A := by
  sorry

-- (c)
theorem MySet.inter_self (A : MySet α) :
  A ∩ A = A := by
  sorry

-- See Lemma 3.1.12
-- theorem MySet.union_self (A : Type) :
--   A ∪ A = A := by
--   sorry

-- (d)
-- See Lemma 3.1.12
-- theorem MySet.union_comm (A B : Type) :
--   A ∪ B = B ∪ A := by
--   sorry

theorem MySet.inter_comm (A B : MySet α) :
  A ∩ B = B ∩ A := by
  sorry

-- (e)
-- See Lemma 3.1.12
-- theorem MySet.union_assoc (A B C : Type) :
--   (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
--   sorry

theorem MySet.inter_assoc (A B C : MySet α) :
  (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  sorry

-- (f)
theorem MySet.inter_union_distrib (A B C : MySet α) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  sorry

theorem MySet.union_inter_distrib (A B C : MySet α) :
  A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry

-- (g)
theorem MySet.union_diff_superset
  (X A : MySet α) (hA : A ⊆ X) :
  A ∪ (X \ A) = X := by
  sorry

theorem MySet.inter_diff_superset
  (X A : MySet α) (hA : A ⊆ X) :
  A ∩ (X \ A) = ∅ := by
  sorry

theorem MySet.superset_diff_union
  (X A B : MySet α) (hA : A ⊆ X) (hB : B ⊆ X) :
  X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  sorry

theorem MySet.superset_diff_inter
  (X A B : MySet α) (hA : A ⊆ X) (hB : B ⊆ X) :
  X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  sorry

-- Axiom 3.7
axiom MySet.replace
  (A : MySet α) (P : α → β → Prop)
  (hP : ∀ (x : α), x ∈ A →
    (∃ (y : β), (P x y ∧ (∀ (z : β), P x z → z = y)))) :
  MySet β

axiom MySet.mem_replace
  (A : MySet α) (P : α → β → Prop)
  (hP : ∀ (x : α), x ∈ A →
    (∃ (y : β), (P x y ∧ (∀ (z : β), P x z → z = y)))) :
  ∀ (z : β),
    z ∈ MySet.replace A P hP ↔ (∃ (x : α), x ∈ A ∧ P x z)

-- Example 3.1.30
-- TODO

-- Axiom 3.8
-- TODO

section Exercises

-- Exercise 3.1.1
example (a b c d : α)
  (h : ⦃a, b⦄ = ⦃c, d⦄) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  sorry

-- Exercise 3.1.5
example (A B : MySet α) :
  ((A ⊆ B) ↔ (A ∪ B = B))
  ∧ ((A ⊆ B) ↔ (A ∩ B = A)) := by
  sorry

-- Exercise 3.1.7
example (A B : MySet α) :
  A ∩ B ⊆ A := by
  sorry

example (A B : MySet α) :
  A ∩ B ⊆ B := by
  sorry

example (A B C : MySet α) :
  C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B := by
  sorry

example (A B : MySet α) :
  A ⊆ A ∪ B := by
  sorry

example (A B : MySet α) :
  B ⊆ A ∪ B := by
  sorry

example (A B C : MySet α) :
  A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  sorry

-- Exercise 3.1.8
example (A B : MySet α) :
  A ∩ (A ∪ B) = A := by
  sorry

example (A B : MySet α) :
  A ∪ (A ∩ B) = A := by
  sorry

-- Exercise 3.1.9
example (A B X : MySet α)
  (hu : A ∪ B = X) (hi : A ∩ B = ∅) :
  A = X \ B := by
  sorry

example (A B X : MySet α)
  (hu : A ∪ B = X) (hi : A ∩ B = ∅) :
  B = X \ A := by
  sorry

-- Exercise 3.1.10
example (A B : MySet α) :
  MySet.disjoint (A \ B) (A ∩ B) := by
  sorry

example (A B : MySet α) :
  MySet.disjoint (A \ B) (B \ A) := by
  sorry

example (A B : MySet α) :
  MySet.disjoint (A ∩ B) (B \ A) := by
  sorry

example (A B : MySet α) :
  (A \ B) ∪ (A ∩ B) ∪ (B \ A) = A ∪ B := by
  sorry

-- Exercise 3.1.11
-- TODO

-- Exercise 3.1.12
-- (a)
example (A B A' B' : MySet α)
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  A' ∪ B' ⊆ A ∪ B := by
  sorry

example (A B A' B' : MySet α)
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  A' ∩ B' ⊆ A ∩ B := by
  sorry

-- (b)
example (A B A' B' : MySet α)
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  ¬ (A' \ B' ⊆ A \ B) := by
  sorry

-- Exercise 3.1.13
example (A : MySet α) (hA : MySet.nonempty A) :
  ¬ (∃ (B : MySet α), B ⊊ A) ↔ (∃ (x : α), A = ⦃x⦄) := by
  sorry

end Exercises
