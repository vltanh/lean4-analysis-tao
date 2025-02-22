import Mathlib.Tactic.ByContra

-- Definition 3.1.1
axiom MySet.mem : Type → Type → Prop
notation:50 x:50 " ∈ " S:50 => MySet.mem S x
notation:50 x:50 " ∉ " S:50 => ¬ (x ∈ S)

-- Axiom 3.1
axiom MySet (α : Type) : Type

-- Axiom 3.2
axiom MySet.ext {A B : Type} :
  A = B ↔ (∀ (x : Type), x ∈ A ↔ x ∈ B)

-- Axiom 3.3
axiom MySet.empty : Type
notation:max "∅" => MySet.empty

axiom MySet.not_mem_empty :
  ∀ (x : Type), x ∉ ∅

def MySet.nonempty (S : Type) : Prop :=
  S ≠ ∅

-- Lemma 3.1.5
theorem MySet.single_choice {A : Type} (h : MySet.nonempty A) :
  ∃ (x : Type), x ∈ A := by
  by_contra hxnA
  push_neg at hxnA
  have hxnemp : ∀ (x : Type), ¬x ∈ ∅ := by
    intro x
    exact MySet.not_mem_empty x
  have : ∀ (x : Type), x ∈ A ↔ x ∈ ∅ := by
    intro x
    exact iff_of_false (hxnA x) (hxnemp x)
  have : A = ∅ := MySet.ext.mpr this
  exact h this

-- Axiom 3.4
axiom MySet.singleton (a : Type) : Type

axiom MySet.mem_singleton (a : Type) :
  ∀ (y : Type), y ∈ MySet.singleton a ↔ y = a

axiom MySet.pair (a b : Type) : Type

axiom MySet.mem_pair (a b : Type) :
  ∀ (y : Type), y ∈ MySet.pair a b ↔ y = a ∨ y = b

-- Remarks 3.1.8
example (a : Type) :
  ∀ (S : Type),
    (∀ (y : Type), y ∈ S ↔ y = a) → S = MySet.singleton a := by
  intro S h
  rw [MySet.ext]
  intro x
  rw [h x]
  rw [MySet.mem_singleton a]

example (a b : Type) :
  MySet.pair a b = MySet.pair b a := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_pair a b]
  rw [MySet.mem_pair b a]
  exact Or.comm

example (a : Type) :
  MySet.pair a a = MySet.singleton a := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_pair a a]
  rw [MySet.mem_singleton a]
  rw [or_self (x = a)]

-- Example 3.1.9
example :
  ∅ ≠ MySet.singleton ∅ := by
  sorry

example :
  ∅ ≠ MySet.singleton (MySet.singleton ∅) := by
  sorry

example :
  ∅ ≠ MySet.pair ∅ (MySet.singleton ∅) := by
  sorry

example :
  MySet.singleton ∅ ≠ MySet.singleton (MySet.singleton ∅) := by
  sorry

example :
  MySet.singleton ∅ ≠ MySet.pair ∅ (MySet.singleton ∅) := by
  sorry

example :
  MySet.singleton (MySet.singleton ∅) ≠ MySet.pair ∅ (MySet.singleton ∅) := by
  sorry

-- Axiom 3.5
axiom MySet.union (A B : Type) : Type
infixl:65 " ∪ " => MySet.union

axiom MySet.mem_union (A B : Type) :
  ∀ (x : Type), x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

-- Remark 3.1.11
example (A B : Type) (h : A = A') :
  A ∪ B = A' ∪ B := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A B]
  rw [MySet.mem_union A' B]
  rw [h]

example (A B : Type) (h : B = B') :
  A ∪ B = A ∪ B' := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A B]
  rw [MySet.mem_union A B']
  rw [h]

-- Lemma 3.1.12
theorem MySet.pair_eq_union_singleton (a b : Type) :
  MySet.pair a b = MySet.singleton a ∪ MySet.singleton b := by
  sorry

theorem MySet.union_comm (A B : Type) :
  A ∪ B = B ∪ A := by
  sorry

theorem MySet.union_assoc (A B C : Type) :
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

theorem MySet.union_idem (A : Type) :
  A ∪ A = A := by
  sorry

theorem MySet.union_empty (A : Type) :
  A ∪ ∅ = A := by
  sorry

theorem MySet.empty_union (A : Type) :
  ∅ ∪ A = A := by
  sorry

-- Definition 3.1.14
axiom MySet.subset : Type → Type → Prop
infix:50 " ⊆ " => MySet.subset
notation A:50 " ⊊ " B:50 => A ⊆ B ∧ A ≠ B

axiom MySet.subset_def (A B : Type) :
  A ⊆ B ↔ ∀ (x : Type), x ∈ A → x ∈ B

-- Remark 3.1.15
example (A B : Type) (h : A = A') :
  A ⊆ B ↔ A' ⊆ B := by
  rw [h]

-- Example 3.1.16
example (A : Type) :
  A ⊆ A := by
  rw [MySet.subset_def]
  intro x h
  exact h

example (A : Type) :
  ∅ ⊆ A := by
  rw [MySet.subset_def]
  intro x h
  have : x ∉ ∅ := MySet.not_mem_empty x
  exact False.elim (this h)

-- Proposition 3.1.17
theorem MySet.subset_trans (A B C : Type) :
  A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAB hBC
  rw [MySet.subset_def A B] at hAB
  rw [MySet.subset_def B C] at hBC
  rw [MySet.subset_def A C]
  intro x hxA
  have : x ∈ B := hAB x hxA
  have : x ∈ C := hBC x this
  exact this

theorem MySet.subset_antisymm (A B : Type) :
  A ⊆ B → B ⊆ A → A = B := by
  sorry

theorem MySet.proper_ss_of_proper_ss_of_proper_ss (A B C : Type) :
  A ⊊ B → B ⊊ C → A ⊊ C := by
  sorry

-- Axiom 3.6
axiom MySet.spec (A : Type) (P : Type → Prop) : Type

axiom MySet.mem_spec (A : Type) (P : Type → Prop) :
  ∀ (y : Type), y ∈ MySet.spec A P ↔ y ∈ A ∧ P y

theorem MySet.spec_ss (A : Type) (P : Type → Prop) :
  MySet.spec A P ⊆ A := by
  rw [MySet.subset_def]
  intro x h
  rw [MySet.mem_spec A P] at h
  exact h.left

theorem MySet.spec_eq_spec_of_eq
  {A A' : Type} (P : Type → Prop) (h : A = A') :
  MySet.spec A P = MySet.spec A' P := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_spec A P]
  rw [MySet.mem_spec A' P]
  rw [h]

-- Definition 3.1.22
def MySet.inter (S₁ S₂ : Type) : Type :=
  MySet.spec S₁ (fun x => x ∈ S₂)
infixl:70 " ∩ " => MySet.inter

theorem MySet.mem_inter (S₁ S₂ : Type) :
  ∀ (x : Type), x ∈ S₁ ∩ S₂ ↔ x ∈ S₁ ∧ x ∈ S₂ := by
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec S₁ (fun x => x ∈ S₂)]

def MySet.disjoint (A B : Type) : Prop :=
  A ∩ B = ∅

example : MySet.disjoint ∅ ∅ := by
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec ∅ (fun x => x ∈ ∅)]
  rw [and_self (x ∈ ∅)]

-- Definition 3.1.26
def MySet.diff (A B : Type) : Type :=
  MySet.spec A (fun x => x ∉ B)
infix:70 " \\ " => MySet.diff

-- Proposition 3.1.27
-- (a)
-- See Lemma 3.1.12
-- theorem MySet.union_empty (A : Type) :
--   A ∪ ∅ = A := by
--   sorry

theorem MySet.inter_empty (A : Type) :
  A ∩ ∅ = ∅ := by
  sorry

-- (b)
theorem MySet.union_superset
  (X A : Type) (hA : A ⊆ X) :
  A ∪ X = X := by
  sorry

theorem MySet.inter_superset
  (X A : Type) (hA : A ⊆ X) :
  A ∩ X = A := by
  sorry

-- (c)
theorem MySet.inter_self (A : Type) :
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

theorem MySet.inter_comm (A B : Type) :
  A ∩ B = B ∩ A := by
  sorry

-- (e)
-- See Lemma 3.1.12
-- theorem MySet.union_assoc (A B C : Type) :
--   (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
--   sorry

theorem MySet.inter_assoc (A B C : Type) :
  (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  sorry

-- (f)
theorem MySet.inter_union_distrib (A B C : Type) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  sorry

theorem MySet.union_inter_distrib (A B C : Type) :
  A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry

-- (g)
theorem MySet.union_diff_superset
  (X A : Type) (hA : A ⊆ X) :
  A ∪ (X \ A) = X := by
  sorry

theorem MySet.inter_diff_superset
  (X A : Type) (hA : A ⊆ X) :
  A ∩ (X \ A) = ∅ := by
  sorry

theorem MySet.superset_diff_union
  (X A B : Type) (hA : A ⊆ X) (hB : B ⊆ X) :
  X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  sorry

theorem MySet.superset_diff_inter
  (X A B : Type) (hA : A ⊆ X) (hB : B ⊆ X) :
  X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  sorry

-- Axiom 3.7
axiom MySet.replace
  (A : Type) (P : Type → Type → Prop)
  (hP : ∀ (x : Type), x ∈ A →
    (∃ (y : Type), (P x y ∧ (∀ (z : Type), P x z → z = y)))) :
  Type

axiom MySet.mem_replace
  (A : Type) (P : Type → Type → Prop)
  (hP : ∀ (x : Type), x ∈ A →
    ∃ (y : Type), P x y ∧ (∀ (z : Type), P x z → z = y)) :
  ∀ (z : Type),
    z ∈ MySet.replace A P hP ↔ (∃ (x : Type), x ∈ A ∧ P x z)

-- Example 3.1.30
-- TODO

-- Axiom 3.8
-- TODO

section Exercises

-- Exercise 3.1.1
example (a b c d : Type)
  (h : MySet.pair a b = MySet.pair c d) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  sorry

-- Exercise 3.1.5
example (A B : Type) :
  ((A ⊆ B) ↔ (A ∪ B = B))
  ∧ ((A ⊆ B) ↔ (A ∩ B = A)) := by
  sorry

-- Exercise 3.1.7
example (A B : Type) :
  A ∩ B ⊆ A := by
  sorry

example (A B : Type) :
  A ∩ B ⊆ B := by
  sorry

example (A B C : Type) :
  C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B := by
  sorry

example (A B : Type) :
  A ⊆ A ∪ B := by
  sorry

example (A B : Type) :
  B ⊆ A ∪ B := by
  sorry

example (A B C : Type) :
  A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  sorry

-- Exercise 3.1.8
example (A B : Type) :
  A ∩ (A ∪ B) = A := by
  sorry

example (A B : Type) :
  A ∪ (A ∩ B) = A := by
  sorry

-- Exercise 3.1.9
example (A B X : Type)
  (hu : A ∪ B = X) (hi : A ∩ B = ∅) :
  A = X \ B := by
  sorry

example (A B X : Type)
  (hu : A ∪ B = X) (hi : A ∩ B = ∅) :
  B = X \ A := by
  sorry

-- Exercise 3.1.10
example (A B : Type) :
  MySet.disjoint (A \ B) (A ∩ B) := by
  sorry

example (A B : Type) :
  MySet.disjoint (A \ B) (B \ A) := by
  sorry

example (A B : Type) :
  MySet.disjoint (A ∩ B) (B \ A) := by
  sorry

example (A B : Type) :
  (A \ B) ∪ (A ∩ B) ∪ (B \ A) = A ∪ B := by
  sorry

-- Exercise 3.1.11
-- TODO

-- Exercise 3.1.12
-- (a)
example (A B A' B' : Type)
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  A' ∪ B' ⊆ A ∪ B := by
  sorry

example (A B A' B' : Type)
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  A' ∩ B' ⊆ A ∩ B := by
  sorry

-- (b)
example (A B A' B' : Type)
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  ¬ (A' \ B' ⊆ A \ B) := by
  sorry

-- Exercise 3.1.13
example (A : Type) (hA : MySet.nonempty A) :
  ¬ (∃ (B : Type), B ⊊ A) ↔ (∃ (x : Type), A = MySet.singleton x) := by
  sorry

end Exercises
