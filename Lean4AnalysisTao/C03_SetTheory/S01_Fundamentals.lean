import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

-- Definition 3.1.1
axiom MySet.mem {α γ : Type} : γ → α → Prop
notation:50 x:50 " ∈ " S:50 => MySet.mem S x
notation:50 x:50 " ∉ " S:50 => ¬ (x ∈ S)

-- Axiom 3.1
axiom MySet (α : Type) : Type

-- Axiom 3.2
axiom MySet.ext {α γ : Type} {A B : γ} :
  A = B ↔ (∀ (x : α), x ∈ A ↔ x ∈ B)

-- Axiom 3.3
axiom MySet.empty {γ : Type} : γ
notation:max "∅" => MySet.empty

axiom MySet.not_mem_empty {α γ : Type} :
  ∀ {x : α}, x ∉ (∅ : γ)

def MySet.nonempty (S : MySet α) : Prop :=
  S ≠ ∅

-- Lemma 3.1.5
theorem MySet.single_choice {A : MySet α} (h : A.nonempty) :
  ∃ (x : α), x ∈ A := by
  by_contra hxnA
  push_neg at hxnA
  have hxnemp : ∀ (x : α), ¬x ∈ (∅ : MySet α) := by
    intro x
    exact MySet.not_mem_empty
  have : ∀ (x : α), x ∈ A ↔ x ∈ (∅ : MySet α) := by
    intro x
    exact iff_of_false (hxnA x) (hxnemp x)
  have : A = ∅ := MySet.ext.mpr this
  exact h this

-- Axiom 3.4
axiom MySet.singleton {α γ : Type} (a : α) : γ
notation:max "⦃" a:max "⦄" => MySet.singleton a

axiom MySet.mem_singleton {α γ : Type} (a : α) :
  ∀ (y : α), y ∈ (⦃a⦄ : γ) ↔ y = a

axiom MySet.pair {α γ : Type} (a b : α) : γ
notation:max "⦃" a:max ", " b:max "⦄" => MySet.pair a b

axiom MySet.mem_pair {α γ : Type} (a b : α) :
  ∀ (y : α), y ∈ (⦃a, b⦄ : γ) ↔ y = a ∨ y = b

-- Remarks 3.1.8
example (a : α) :
  ∀ (S : MySet α),
    (∀ (y : α), y ∈ S ↔ y = a) → S = ⦃a⦄ := by
  sorry


example (a b : α) :
  (⦃a, b⦄ : MySet α) = ⦃b, a⦄ := by
  sorry

example (a : α) :
  (⦃a, a⦄ : MySet α) = ⦃a⦄ := by
  sorry

-- Example 3.1.9
example :
  (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
  sorry

example :
  (∅ : γ) ≠ ⦃(⦃(∅ : γ)⦄ : γ)⦄ := by
  sorry

example :
  (∅ : γ) ≠ ⦃(∅ : γ), (⦃(∅ : γ)⦄ : γ)⦄ := by
  sorry

example :
  (⦃(∅ : γ)⦄ : γ) ≠ ⦃(⦃(∅ : γ)⦄ : γ)⦄ := by
  sorry

example :
  (⦃(∅ : γ)⦄ : γ) ≠ ⦃(∅ : γ), ⦃(∅ : γ)⦄⦄ := by
  sorry

example :
  (⦃(⦃(∅ : γ)⦄ : γ)⦄ : γ) ≠ ⦃(∅ : γ), (⦃(∅ : γ)⦄ : γ)⦄ := by
  sorry

-- Axiom 3.5
axiom MySet.union {γ : Type} (A B : γ) : γ
infixl:65 " ∪ " => MySet.union

axiom MySet.mem_union {γ : Type} (A B : γ) :
  ∀ {α : Type} (x : α), x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

-- Remark 3.1.11
example (A A' B : MySet α) (h : A = A') :
  A ∪ B = A' ∪ B := by
  -- Use Axiom 3.2 and Axiom 3.5
  sorry

example (A B B' : MySet α) (h : B = B') :
  A ∪ B = A ∪ B' := by
  -- Use Axiom 3.2 and Axiom 3.5
  sorry

-- Lemma 3.1.12
theorem MySet.pair_eq_union_singleton (a b : α) :
  (⦃a, b⦄ : MySet α) = ⦃a⦄ ∪ ⦃b⦄ := by
  sorry

theorem MySet.union_comm (A B : MySet α) :
  A ∪ B = B ∪ A := by
  sorry

theorem MySet.union_assoc (A B C : MySet α) :
  (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  have : ∀ (x : α), x ∈ (A ∪ B) ∪ C ↔ x ∈ A ∪ (B ∪ C) := by
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
  exact MySet.ext.mpr this

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
def MySet.subset {α : Type} (A B : MySet α) :=
  ∀ (x : α), x ∈ A → x ∈ B
infix:50 " ⊆ " => MySet.subset
notation A:50 " ⊊ " B:50 => A ⊆ B ∧ A ≠ B

-- Remark 3.1.15
example (A A' B : MySet α) (h : A = A') :
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
axiom MySet.spec {α γ : Type} (A : γ) (P : α → Prop) : γ
notation "⦃" S:max " | " P:max "⦄" => MySet.spec S P

axiom MySet.mem_spec {α : Type} (A : MySet α) (P : α → Prop) :
  ∀ (y : α), y ∈ MySet.spec A P ↔ y ∈ A ∧ P y

theorem MySet.spec_ss {A : MySet α} {P : α → Prop} :
  ⦃A | P⦄ ⊆ A := by
  sorry

theorem MySet.spec_eq_spec_of_eq
  {A A' : MySet α} {P : α → Prop} (h : A = A') :
  ⦃A | P⦄ = ⦃A' | P⦄ := by
  sorry

-- Example 3.1.21
namespace Example_3_1_21

noncomputable def S : MySet ℕ := ⦃1⦄ ∪ ⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄ ∪ ⦃5⦄

example :
  ⦃S | fun (x : ℕ) => x < 4⦄
    = ⦃1⦄ ∪ ⦃2⦄ ∪ ⦃3⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_spec]
  rw [S]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄) ⦃5⦄]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄ ∪ ⦃3⦄) ⦃4⦄]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄) ⦃3⦄]
  rw [MySet.mem_union ⦃1⦄ ⦃2⦄]
  constructor
  · intro h
    rcases h with ⟨hxS, hx4⟩
    rcases hxS with (hxS | hxS)
    · rcases hxS with (hxS | hxS)
      · rcases hxS with (hxS | hxS)
        · rcases hxS with (hxS | hxS)
          · exact Or.inl (Or.inl hxS)
          · exact Or.inl (Or.inr hxS)
        · exact Or.inr hxS
      · rw [MySet.mem_singleton 4 x] at hxS
        by_contra
        exact Nat.ne_of_lt hx4 hxS
    · rw [MySet.mem_singleton 5 x] at hxS
      by_contra
      rw [hxS] at hx4
      have : 5 ≥ 4 := Nat.le_of_ble_eq_true rfl
      exact Nat.not_lt_of_ge this hx4
  · intro h
    rcases h with (h | h)
    · rcases h with (h | h)
      · constructor
        · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
        · rw [MySet.mem_singleton] at h
          rw [h]
          exact Nat.lt_of_sub_eq_succ rfl
      · constructor
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
        · rw [MySet.mem_singleton] at h
          rw [h]
          exact Nat.lt_of_sub_eq_succ rfl
    · constructor
      · exact Or.inl (Or.inl (Or.inr h))
      · rw [MySet.mem_singleton] at h
        rw [h]
        exact Nat.lt_of_sub_eq_succ rfl

example :
  ⦃S | fun (x : ℕ) => x < 7⦄ = S := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_spec]
  rw [S]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄) ⦃5⦄]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄ ∪ ⦃3⦄) ⦃4⦄]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄) ⦃3⦄]
  rw [MySet.mem_union ⦃1⦄ ⦃2⦄]
  constructor
  · intro h
    rcases h with ⟨hxS, hx7⟩
    rcases hxS with (hxS | hxS)
    · rcases hxS with (hxS | hxS)
      · rcases hxS with (hxS | hxS)
        · rcases hxS with (hxS | hxS)
          · exact Or.inl (Or.inl (Or.inl (Or.inl hxS)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr hxS)))
        · exact Or.inl (Or.inl (Or.inr hxS))
      · exact Or.inl (Or.inr hxS)
    · exact Or.inr hxS
  · intro h
    constructor
    · exact h
    · rcases h with (h | h)
      · rcases h with (h | h)
        · rcases h with (h | h)
          · rcases h with (h | h)
            · rw [MySet.mem_singleton] at h
              rw [h]
              exact Nat.lt_of_sub_eq_succ rfl
            · rw [MySet.mem_singleton] at h
              rw [h]
              exact Nat.lt_of_sub_eq_succ rfl
          · rw [MySet.mem_singleton] at h
            rw [h]
            exact Nat.lt_of_sub_eq_succ rfl
        · rw [MySet.mem_singleton] at h
          rw [h]
          exact Nat.lt_of_sub_eq_succ rfl
      · rw [MySet.mem_singleton] at h
        rw [h]
        exact Nat.lt_of_sub_eq_succ rfl

example :
  ⦃S | fun (x : ℕ) => x < 1⦄ = ∅ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_spec]
  rw [S]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄ ∪ ⦃3⦄ ∪ ⦃4⦄) ⦃5⦄]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄ ∪ ⦃3⦄) ⦃4⦄]
  rw [MySet.mem_union (⦃1⦄ ∪ ⦃2⦄) ⦃3⦄]
  rw [MySet.mem_union ⦃1⦄ ⦃2⦄]
  constructor
  · intro h
    rcases h with ⟨hxS, hx1⟩
    rcases hxS with (hxS | hxS)
    · rcases hxS with (hxS | hxS)
      · rcases hxS with (hxS | hxS)
        · rcases hxS with (hxS | hxS)
          · rw [MySet.mem_singleton] at hxS
            by_contra
            exact Nat.ne_of_lt hx1 hxS
          · rw [MySet.mem_singleton] at hxS
            by_contra
            rw [hxS] at hx1
            have : 2 ≥ 1 := Nat.le_of_ble_eq_true rfl
            exact Nat.not_lt_of_ge this hx1
        · rw [MySet.mem_singleton] at hxS
          by_contra
          rw [hxS] at hx1
          have : 3 ≥ 1 := Nat.le_of_ble_eq_true rfl
          exact Nat.not_lt_of_ge this hx1
      · rw [MySet.mem_singleton] at hxS
        by_contra
        rw [hxS] at hx1
        have : 4 ≥ 1 := Nat.le_of_ble_eq_true rfl
        exact Nat.not_lt_of_ge this hx1
    · rw [MySet.mem_singleton] at hxS
      by_contra
      rw [hxS] at hx1
      have : 5 ≥ 1 := Nat.le_of_ble_eq_true rfl
      exact Nat.not_lt_of_ge this hx1
  · intro h
    by_contra
    exact MySet.not_mem_empty h

end Example_3_1_21

-- Definition 3.1.22
noncomputable def MySet.inter {α : Type} (S₁ S₂ : MySet α) : MySet α :=
  ⦃ S₁ | fun x => (x : α) ∈ S₂ ⦄
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
noncomputable def MySet.diff {α : Type} (A B : MySet α) : MySet α :=
  ⦃ A | fun x => (x : α) ∉ B ⦄
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

theorem MySet.inter_diff (X A : MySet α) :
  A ∩ (X \ A) = ∅ := by
  sorry

theorem MySet.diff_union (X A B : MySet α) :
  X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  sorry

theorem MySet.diff_inter (X A B : MySet α) :
  X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  sorry

-- Axiom 3.7
axiom MySet.replace {α β : Type}
  (A : MySet α) {P : α → β → Prop}
  (hP : ∀ (x : α), x ∈ A →
    (∃ (y : β), (P x y ∧ (∀ (z : β), P x z → z = y)))) :
  MySet β
notation
  "⦃" A:max " ← " hP:max "⦄" => MySet.replace A hP

axiom MySet.mem_replace {α β : Type}
  (A : MySet α) {P : α → β → Prop}
  (hP : ∀ (x : α), x ∈ A →
    (∃ (y : β), (P x y ∧ (∀ (z : β), P x z → z = y)))) :
  ∀ (z : β),
    z ∈ ⦃A ← hP⦄ ↔ (∃ (x : α), x ∈ A ∧ P x z)

-- Example 3.1.30
namespace Example_3_1_30

noncomputable def A : MySet ℕ := ⦃3⦄ ∪ ⦃5⦄ ∪ ⦃9⦄

def P (x : ℕ) (y : ℕ) : Prop := y = x + 1

lemma hP :
  ∀ (x : ℕ), x ∈ A →
    (∃ (y : ℕ), (P x y ∧ (∀ (z : ℕ), P x z → z = y))) := by
  intro x hxA
  use (x + 1)
  constructor
  · rw [P]
  · intro z hz
    rw [P] at hz
    rw [hz]

example :
  ⦃A ← hP⦄ = ⦃4⦄ ∪ ⦃6⦄ ∪ ⦃10⦄ := by
  sorry

end Example_3_1_30

-- Example 3.1.31
namespace Example_3_1_31

noncomputable def A : MySet ℕ := ⦃3⦄ ∪ ⦃5⦄ ∪ ⦃9⦄

def P (x : ℕ) (y : ℕ) : Prop := y = 1

lemma hP :
  ∀ (x : ℕ), x ∈ A →
    (∃ (y : ℕ), (P x y ∧ (∀ (z : ℕ), P x z → z = y))) := by
  intro x hxA
  use 1
  constructor
  · rw [P]
  · intro z hz
    rw [P] at hz
    rw [hz]

example :
  ⦃A ← hP⦄ = ⦃1⦄ := by
  rw [MySet.ext]
  intro y
  rw [MySet.mem_replace A hP]
  rw [MySet.mem_singleton 1 y]
  constructor
  · intro h
    rcases h with ⟨x, hxA, hPxy⟩
    rw [P] at hPxy
    exact hPxy
  · intro h
    use 9
    constructor
    · rw [A]
      rw [MySet.mem_union (⦃3⦄ ∪ ⦃5⦄) ⦃9⦄]
      rw [MySet.mem_singleton 9 9]
      exact Or.inr rfl
    · rw [P]
      exact h

end Example_3_1_31

-- Axiom 3.8
axiom MySet.Nat.set : MySet ℕ

axiom MySet.Nat.is_nat :
  ∀ (n : ℕ), n ∈ MySet.Nat.set

-- axiom MySet.Nat.type : Type

-- axiom MySet.Nat.set : MySet MySet.Nat.type

-- axiom MySet.Nat.zero : MySet.Nat.type

-- axiom MySet.Nat.succ : MySet.Nat.type → MySet.Nat.type

-- axiom MySet.Nat.zero_is_nat :
--   MySet.Nat.zero ∈ MySet.Nat.set

-- axiom MySet.Nat.succ_is_nat :
--   ∀ (n : MySet.Nat.type),
--     n ∈ MySet.Nat.set → MySet.Nat.succ n ∈ MySet.Nat.set

-- axiom MySet.Nat.succ_ne_zero :
--   ∀ (n : MySet.Nat.type),
--     n ∈ MySet.Nat.set → MySet.Nat.succ n ≠ MySet.Nat.zero

-- axiom MySet.Nat.succ_inj :
--   ∀ (n : MySet.Nat.type), n ∈ MySet.Nat.set →
--     ∀ (m : MySet.Nat.type), m ∈ MySet.Nat.set →
--       MySet.Nat.succ n = MySet.Nat.succ m → n = m

-- axiom MySet.Nat.induction :
--   ∀ (P : MySet.Nat.type → Prop),
--     P MySet.Nat.zero →
--     (∀ (n : MySet.Nat.type), n ∈ MySet.Nat.set →
--       P n → P (MySet.Nat.succ n)) →
--     (∀ (n : MySet.Nat.type), n ∈ MySet.Nat.set → P n)

section Exercises

-- Exercise 3.1.1
example (a b c d : α)
  (h : (⦃a, b⦄ : MySet ℕ) = ⦃c, d⦄) :
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
example {α : Type}
  (hrep : ∀ (A : MySet α) {β : Type} (P : α → β → Prop),
    (∀ (x : α), x ∈ A →
      (∃ (y : β), P x y ∧ (∀ (z : β), P x z → y = z))) →
    (∃ (S : MySet β),
      ∀ (y : β), y ∈ S ↔ ∃ (x : α), x ∈ A ∧ P x y)) :
  ∀ (A : MySet α) (P : α → Prop),
    ∃ (S : MySet α),
      ∀ (x : α), x ∈ S ↔ x ∈ A ∧ P x := by
  sorry

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
example : ∃ (A B A' B' : MySet ℕ),
  A' ⊆ A ∧ B' ⊆ B ∧ ¬ (A' \ B' ⊆ A \ B) := by
  sorry

-- Exercise 3.1.13
example (A : MySet α) (hA : A.nonempty) :
  ¬ (∃ (B : MySet α), B.nonempty ∧ B ⊊ A) ↔ (∃ (x : α), A = ⦃x⦄) := by
  sorry

end Exercises
