import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

-- Definition 3.1.1
axiom MySet.mem.{u, v} {α : Type u} {γ : Type v} : γ → α → Prop
notation:50 x:50 " ∈ " S:50 => MySet.mem S x
notation:50 x:50 " ∉ " S:50 => ¬ (x ∈ S)

-- Axiom 3.1
axiom MySet.{u} (α : Type u) : Type u

-- Axiom 3.2
axiom MySet.ext.{u, v} {α : Type u} {γ : Type v} {A B : γ} :
  A = B ↔ (∀ (x : α), x ∈ A ↔ x ∈ B)

-- Axiom 3.3
axiom MySet.empty.{u} {γ : Type u} : γ
notation:max "∅" => MySet.empty

axiom MySet.not_mem_empty.{u} {α γ : Type u} :
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
axiom MySet.singleton.{u, v} {α : Type u} {γ : Type v} (a : α) : γ
notation:max "⦃" a:max "⦄" => MySet.singleton a

axiom MySet.mem_singleton.{u, v} {α : Type u} {γ : Type v} (a : α) :
  ∀ (y : α), y ∈ (⦃a⦄ : γ) ↔ y = a

-- axiom MySet.mem_union.{u, v} {γ : Type v} (A B : γ) :
--   ∀ {α : Type u} (x : α), x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

axiom MySet.pair.{u, v} {α : Type u} {γ : Type v} (a b : α) : γ
notation:max "⦃" a:max ", " b:max "⦄" => MySet.pair a b

axiom MySet.mem_pair.{u, v} {α : Type u} {γ : Type v} (a b : α) :
  ∀ (y : α), y ∈ (⦃a, b⦄ : γ) ↔ y = a ∨ y = b

-- Remarks 3.1.8
example (a : α) :
  ∀ (S : MySet α),
    (∀ (y : α), y ∈ S ↔ y = a) → S = ⦃a⦄ := by
  intro S h
  rw [MySet.ext]
  intro x
  rw [h x]
  rw [MySet.mem_singleton a]

example (a b : α) :
  (⦃a, b⦄ : MySet α) = ⦃b, a⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_pair a b]
  rw [MySet.mem_pair b a]
  exact Or.comm

example (a : α) :
  (⦃a, a⦄ : MySet α) = ⦃a⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_pair a a]
  rw [MySet.mem_singleton a]
  rw [or_self (x = a)]

-- Example 3.1.9
example :
  (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
  intro h
  have : (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
    rw [MySet.mem_singleton ∅ ∅]
  have : ∅ ∈ ∅ := (MySet.ext.mp h ∅).mpr this
  exact MySet.not_mem_empty this

example :
  (∅ : γ) ≠ ⦃(⦃(∅ : γ)⦄ : γ)⦄ := by
  intro h
  have : (⦃(∅ : γ)⦄ : γ) ∈ (⦃(⦃(∅ : γ)⦄ : γ)⦄ : γ) := by
    rw [MySet.mem_singleton ⦃∅⦄ ⦃∅⦄]
  have : ⦃∅⦄ ∈ ∅ := (MySet.ext.mp h ⦃∅⦄).mpr this
  exact MySet.not_mem_empty this

example :
  (∅ : γ) ≠ ⦃(∅ : γ), (⦃(∅ : γ)⦄ : γ)⦄ := by
  intro h
  have :
    (⦃(∅ : γ)⦄ : γ) ∈ (⦃(∅ : γ), (⦃(∅ : γ)⦄ : γ)⦄ : γ) := by
    rw [MySet.mem_pair ∅ ⦃∅⦄]
    exact Or.inr rfl
  have : ⦃∅⦄ ∈ ∅ := (MySet.ext.mp h ⦃∅⦄).mpr this
  exact MySet.not_mem_empty this

example :
  (⦃(∅ : γ)⦄ : γ) ≠ ⦃(⦃(∅ : γ)⦄ : γ)⦄ := by
  intro h
  have : (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
    rw [MySet.mem_singleton ∅ ∅]
  have h' : ∅ ∈ ⦃⦃∅⦄⦄ := (MySet.ext.mp h ∅).mp this
  rw [MySet.mem_singleton ⦃∅⦄ ∅] at h'
  have : (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
    intro h
    have : (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
      rw [MySet.mem_singleton ∅ ∅]
    have : ∅ ∈ ∅ := (MySet.ext.mp h ∅).mpr this
    exact MySet.not_mem_empty this
  exact this h'

example :
  (⦃(∅ : γ)⦄ : γ) ≠ ⦃(∅ : γ), ⦃(∅ : γ)⦄⦄ := by
  intro h
  have : (⦃(∅ : γ)⦄ : γ) ∈ (⦃(∅ : γ), ⦃(∅ : γ)⦄⦄ : γ) := by
    rw [MySet.mem_pair ∅ ⦃∅⦄]
    exact Or.inr rfl
  have h' : ⦃∅⦄ ∈ ⦃∅⦄ := (MySet.ext.mp h ⦃∅⦄).mpr this
  rw [MySet.mem_singleton ∅ ⦃∅⦄] at h'
  have : (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
    intro h
    have : (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
      rw [MySet.mem_singleton ∅ ∅]
    have : ∅ ∈ ∅ := (MySet.ext.mp h ∅).mpr this
    exact MySet.not_mem_empty this
  exact this.symm h'

example :
  (⦃(⦃(∅ : γ)⦄ : γ)⦄ : γ) ≠ ⦃(∅ : γ), (⦃(∅ : γ)⦄ : γ)⦄ := by
  intro h
  have : (∅ : γ) ∈ (⦃(∅ : γ), ⦃(∅ : γ)⦄⦄ : γ) := by
    rw [MySet.mem_pair ∅ ⦃∅⦄]
    exact Or.inl rfl
  have h' : ∅ ∈ ⦃⦃∅⦄⦄ := (MySet.ext.mp h ∅).mpr this
  rw [MySet.mem_singleton ⦃∅⦄ ∅] at h'
  have : (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
    intro h
    have : (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
      rw [MySet.mem_singleton ∅ ∅]
    have : ∅ ∈ ∅ := (MySet.ext.mp h ∅).mpr this
    exact MySet.not_mem_empty this
  exact this h'

-- Axiom 3.5
axiom MySet.union.{v} {γ : Type v} (A B : γ) : γ
infixl:65 " ∪ " => MySet.union

axiom MySet.mem_union.{u, v} {γ : Type v} (A B : γ) :
  ∀ {α : Type u} (x : α), x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B

-- Remark 3.1.11
example (A A' B : MySet α) (h : A = A') :
  A ∪ B = A' ∪ B := by
  -- Use Axiom 3.2 and Axiom 3.5
  have : ∀ (x : α), x ∈ A ∪ B ↔ x ∈ A' ∪ B := by
    intro x
    rw [MySet.mem_union A B]
    rw [MySet.mem_union A' B]
    rw [h]
  exact MySet.ext.mpr this

example (A B B' : MySet α) (h : B = B') :
  A ∪ B = A ∪ B' := by
  -- Use Axiom 3.2 and Axiom 3.5
  have : ∀ (x : α), x ∈ A ∪ B ↔ x ∈ A ∪ B' := by
    intro x
    rw [MySet.mem_union A B]
    rw [MySet.mem_union A B']
    rw [h]
  exact MySet.ext.mpr this

-- Lemma 3.1.12
theorem MySet.pair_eq_union_singleton (a b : α) :
  (⦃a, b⦄ : MySet α) = ⦃a⦄ ∪ ⦃b⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_pair a b]
  rw [MySet.mem_union ⦃a⦄ ⦃b⦄]
  rw [MySet.mem_singleton a]
  rw [MySet.mem_singleton b]

theorem MySet.union_comm (A B : MySet α) :
  A ∪ B = B ∪ A := by
  have : ∀ (x : α), x ∈ A ∪ B ↔ x ∈ B ∪ A := by
    intro x
    rw [MySet.mem_union A B]
    rw [MySet.mem_union B A]
    exact Or.comm
  exact MySet.ext.mpr this

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
  have : ∀ (x : α), x ∈ A ∪ A ↔ x ∈ A := by
    intro x
    rw [MySet.mem_union A A]
    rw [or_self (x ∈ A)]
  exact MySet.ext.mpr this

theorem MySet.union_empty (A : MySet α) :
  A ∪ ∅ = A := by
  have : ∀ (x : α), x ∈ A ∪ ∅ ↔ x ∈ A := by
    intro x
    rw [MySet.mem_union A ∅]
    constructor
    · intro h
      rcases h with (h | h)
      · exact h
      · exact False.elim (MySet.not_mem_empty h)
    · intro h
      exact Or.inl h
  exact MySet.ext.mpr this

theorem MySet.empty_union (A : MySet α) :
  ∅ ∪ A = A := by
  rw [MySet.union_comm]
  rw [MySet.union_empty]

-- Definition 3.1.14
def MySet.subset.{u} {α : Type u} (A B : MySet α) :=
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
  rw [MySet.subset]
  intro x h
  exact h

example (A : MySet α) :
  ∅ ⊆ A := by
  rw [MySet.subset]
  intro x h
  exact False.elim (MySet.not_mem_empty h)

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
  intro hAB hBA
  rw [MySet.subset] at hAB
  rw [MySet.subset] at hBA
  rw [MySet.ext]
  intro x
  constructor
  · exact hAB x
  · exact hBA x

theorem MySet.proper_ss_of_proper_ss_of_proper_ss (A B C : MySet α) :
  A ⊊ B → B ⊊ C → A ⊊ C := by
  intro hAB hBC
  constructor
  · exact MySet.subset_trans A B C hAB.left hBC.left
  · intro hAC
    have : C ⊆ B := by
      rw [hAC] at hAB
      exact hAB.left
    have : B = C :=
      MySet.subset_antisymm B C hBC.left this
    exact hBC.right this

-- Axiom 3.6
axiom MySet.spec.{u, v} {α : Type u} {γ : Type v} (A : γ) (P : α → Prop) : γ
notation "⦃" S:max " | " P:max "⦄" => MySet.spec S P

axiom MySet.mem_spec.{u} {α : Type u} (A : MySet α) (P : α → Prop) :
  ∀ (y : α), y ∈ MySet.spec A P ↔ y ∈ A ∧ P y

theorem MySet.spec_ss {A : MySet α} {P : α → Prop} :
  ⦃A | P⦄ ⊆ A := by
  rw [MySet.subset]
  intro x h
  rw [MySet.mem_spec A P x] at h
  exact h.left

theorem MySet.spec_eq_spec_of_eq
  {A A' : MySet α} {P : α → Prop} (h : A = A') :
  ⦃A | P⦄ = ⦃A' | P⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_spec A P x]
  rw [MySet.mem_spec A' P x]
  rw [h]

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
noncomputable def MySet.inter.{u} {α : Type u} (S₁ S₂ : MySet α) : MySet α :=
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
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec ∅ (fun x => x ∈ ∅)]
  rw [and_self (x ∈ ∅)]

-- Definition 3.1.26
noncomputable def MySet.diff.{u} {α : Type u} (A B : MySet α) : MySet α :=
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
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ ∅)]
  constructor
  · intro h
    exact False.elim (MySet.not_mem_empty h.right)
  · intro h
    exact False.elim (MySet.not_mem_empty h)

-- (b)
theorem MySet.union_superset
  (X A : MySet α) (hA : A ⊆ X) :
  A ∪ X = X := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A X]
  constructor
  · intro h
    rcases h with (h | h)
    · rw [MySet.subset] at hA
      exact hA x h
    · exact h
  · intro h
    exact Or.inr h

theorem MySet.inter_superset
  (X A : MySet α) (hA : A ⊆ X) :
  A ∩ X = A := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ X)]
  constructor
  · intro h
    exact h.left
  · intro h
    constructor
    · exact h
    · rw [MySet.subset] at hA
      exact hA x h

-- (c)
theorem MySet.inter_self (A : MySet α) :
  A ∩ A = A := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ A)]
  rw [and_self (x ∈ A)]

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
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec B (fun x => x ∈ A)]
  exact and_comm

-- (e)
-- See Lemma 3.1.12
-- theorem MySet.union_assoc (A B C : Type) :
--   (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
--   sorry

theorem MySet.inter_assoc (A B C : MySet α) :
  (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec (A ∩ B) (fun x => x ∈ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B ∩ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec B (fun x => x ∈ C)]
  exact and_assoc

-- (f)
theorem MySet.inter_union_distrib (A B C : MySet α) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B ∪ C)]
  rw [MySet.mem_union B C]
  rw [MySet.mem_union (A ∩ B) (A ∩ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ C)]
  exact and_or_left

theorem MySet.union_inter_distrib (A B C : MySet α) :
  A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A (B ∩ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec B (fun x => x ∈ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec (A ∪ B) (fun x => x ∈ A ∪ C)]
  rw [MySet.mem_union A B]
  rw [MySet.mem_union A C]
  exact or_and_left

-- (g)
theorem MySet.union_diff_superset
  (X A : MySet α) (hA : A ⊆ X) :
  A ∪ (X \ A) = X := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A (X \ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  constructor
  · intro h
    rcases h with (h | h)
    · rw [MySet.subset] at hA
      exact hA x h
    · exact h.left
  · intro h
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr ⟨h, hxA⟩

theorem MySet.inter_diff (X A : MySet α) :
  A ∩ (X \ A) = ∅ := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ X \ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  constructor
  · intro h
    exact False.elim (h.right.right h.left)
  · intro h
    exact False.elim (MySet.not_mem_empty h)

theorem MySet.diff_union (X A B : MySet α) :
  X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  rw [MySet.ext]
  intro x
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A ∪ B)]
  rw [MySet.mem_union A B]
  rw [MySet.inter]
  rw [MySet.mem_spec (X \ A) (fun x => x ∈ X \ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ B)]
  constructor
  · intro h
    constructor
    · constructor
      · exact h.left
      · rw [not_or] at h
        exact h.right.left
    · constructor
      · exact h.left
      · rw [not_or] at h
        exact h.right.right
  · intro h
    constructor
    · exact h.left.left
    · rw [not_or]
      constructor
      · exact h.left.right
      · exact h.right.right

theorem MySet.diff_inter (X A B : MySet α) :
  X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  rw [MySet.ext]
  intro x
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A ∩ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.mem_union (X \ A) (X \ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ B)]
  constructor
  · intro h
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B
      · rcases h with ⟨hxX, hxAB⟩
        rw [not_and] at hxAB
        exact Or.inr ⟨hxX, hxAB hxA⟩
      · exact Or.inr ⟨h.left, hxB⟩
    · exact Or.inl ⟨h.left, hxA⟩
  · intro h
    rcases h with (h | h)
    · rcases h with ⟨hxX, hxA⟩
      constructor
      · exact hxX
      · rw [not_and_or]
        exact Or.inl hxA
    · rcases h with ⟨hxX, hxB⟩
      constructor
      · exact hxX
      · rw [not_and_or]
        exact Or.inr hxB

-- Axiom 3.7
axiom MySet.replace.{u, v} {α : Type u} {β : Type v}
  (A : MySet α) {P : α → β → Prop}
  (hP : ∀ (x : α), x ∈ A →
    (∃ (y : β), (P x y ∧ (∀ (z : β), P x z → z = y)))) :
  MySet β
notation
  "⦃" A:max " ← " hP:max "⦄" => MySet.replace A hP

axiom MySet.mem_replace.{u, v} {α : Type u} {β : Type v}
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
  rw [MySet.ext]
  intro y
  rw [MySet.mem_replace A hP]
  rw [MySet.mem_union (⦃4⦄ ∪ ⦃6⦄) ⦃10⦄]
  rw [MySet.mem_union ⦃4⦄ ⦃6⦄]
  rw [MySet.mem_singleton 4 y]
  rw [MySet.mem_singleton 6 y]
  rw [MySet.mem_singleton 10 y]
  constructor
  · intro h
    rcases h with ⟨x, hxA, hPxy⟩
    rw [P] at hPxy
    rw [A] at hxA
    rw [MySet.mem_union (⦃3⦄ ∪ ⦃5⦄) ⦃9⦄] at hxA
    rw [MySet.mem_union ⦃3⦄ ⦃5⦄] at hxA
    rcases hxA with (hxA | hxA)
    · rcases hxA with (hxA | hxA)
      · rw [MySet.mem_singleton 3 x] at hxA
        rw [hxA] at hPxy
        exact Or.inl (Or.inl hPxy)
      · rw [MySet.mem_singleton 5 x] at hxA
        rw [hxA] at hPxy
        exact Or.inl (Or.inr hPxy)
    · rw [MySet.mem_singleton 9 x] at hxA
      rw [hxA] at hPxy
      exact Or.inr hPxy
  · intro h
    rcases h with (h | h)
    · rcases h with (h | h)
      · use 3
        constructor
        · rw [A]
          rw [MySet.mem_union (⦃3⦄ ∪ ⦃5⦄) ⦃9⦄]
          rw [MySet.mem_union ⦃3⦄ ⦃5⦄]
          rw [MySet.mem_singleton 3 3]
          exact Or.inl (Or.inl rfl)
        · rw [P]
          exact h
      · use 5
        constructor
        · rw [A]
          rw [MySet.mem_union (⦃3⦄ ∪ ⦃5⦄) ⦃9⦄]
          rw [MySet.mem_union ⦃3⦄ ⦃5⦄]
          rw [MySet.mem_singleton 5 5]
          exact Or.inl (Or.inr rfl)
        · rw [P]
          exact h
    · use 9
      constructor
      · rw [A]
        rw [MySet.mem_union (⦃3⦄ ∪ ⦃5⦄) ⦃9⦄]
        rw [MySet.mem_singleton 9 9]
        exact Or.inr rfl
      · rw [P]
        exact h

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
axiom MySet.nat.{u} :
  ∃ (ν : Type u) (N : MySet ν) (zero : ν) (succ : ν → ν),
    (zero ∈ N)
    ∧ (∀ (n : ν), n ∈ N → succ n ∈ N)
    ∧ (∀ (n : ν), n ∈ N → succ n ≠ zero)
    ∧ (∀ (n : ν), n ∈ N → (∀ (m : ν), m ∈ N → succ n = succ m → n = m))
    ∧ (∀ (P : ν → Prop),
        P zero →
        (∀ (n : ν), n ∈ N → P n → P (succ n)) →
        (∀ (n : ν), n ∈ N → P n))

section Exercises

-- Exercise 3.1.1
example (a b c d : α)
  (h : (⦃a, b⦄ : MySet ℕ) = ⦃c, d⦄) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [MySet.ext] at h
  by_cases ha : a = c
  · have : b = d := by
      have : b ∈ (⦃a, b⦄ : MySet ℕ) := by
        rw [MySet.mem_pair a b]
        exact Or.inr rfl
      have := (h b).mp this
      rw [MySet.mem_pair c d] at this
      rcases this with (hbc | hbd)
      · rw [← hbc] at ha
        have : d ∈ (⦃c, d⦄ : MySet ℕ) := by
          rw [MySet.mem_pair c d]
          exact Or.inr rfl
        have := (h d).mpr this
        rw [MySet.mem_pair a b] at this
        rcases this with (hac | hbd)
        · rw [hac]
          exact ha.symm
        · exact hbd.symm
      · exact hbd
    exact Or.inl ⟨ha, this⟩
  · have haeqd : a = d := by
      have : a ∈ (⦃a, b⦄ : MySet ℕ) := by
        rw [MySet.mem_pair a b]
        exact Or.inl rfl
      have := (h a).mp this
      rw [MySet.mem_pair c d] at this
      rcases this with (hac | had)
      · rw [hac]
        exact False.elim (ha hac)
      · exact had
    have hbeqc : b = c := by
      have : c ∈ (⦃c, d⦄ : MySet ℕ) := by
        rw [MySet.mem_pair c d]
        exact Or.inl rfl
      have := (h c).mpr this
      rw [MySet.mem_pair a b] at this
      rcases this with (hac | hbc)
      · exact False.elim (ha hac.symm)
      · exact hbc.symm
    exact Or.inr ⟨haeqd, hbeqc⟩

-- Exercise 3.1.5
example (A B : MySet α) :
  ((A ⊆ B) ↔ (A ∪ B = B))
  ∧ ((A ⊆ B) ↔ (A ∩ B = A)) := by
  constructor
  · constructor
    · intro h
      exact MySet.union_superset B A h
    · intro h
      rw [MySet.subset]
      intro x hxA
      rw [MySet.ext] at h
      have : x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inl hxA
      exact (h x).mp this
  · constructor
    · intro h
      exact MySet.inter_superset B A h
    · intro h
      rw [MySet.subset]
      intro x hxA
      rw [MySet.ext] at h
      have : x ∈ A ∩ B := (h x).mpr hxA
      rw [MySet.inter] at this
      rw [MySet.mem_spec A (fun x => x ∈ B)] at this
      exact this.right

-- Exercise 3.1.7
example (A B : MySet α) :
  A ∩ B ⊆ A := by
  rw [MySet.subset]
  intro x hxAB
  rw [MySet.inter] at hxAB
  rw [MySet.mem_spec A (fun x => x ∈ B)] at hxAB
  exact hxAB.left

example (A B : MySet α) :
  A ∩ B ⊆ B := by
  rw [MySet.subset]
  intro x hxAB
  rw [MySet.inter] at hxAB
  rw [MySet.mem_spec A (fun x => x ∈ B)] at hxAB
  exact hxAB.right

example (A B C : MySet α) :
  C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B := by
  constructor
  · intro h
    rw [MySet.subset]
    intro x hxC
    rw [MySet.inter]
    rw [MySet.mem_spec A (fun x => x ∈ B)]
    constructor
    · rw [MySet.subset] at h
      exact h.left x hxC
    · rw [MySet.subset] at h
      exact h.right x hxC
  · intro h
    constructor
    · rw [MySet.subset]
      intro x hxC
      rw [MySet.subset] at h
      have : x ∈ A ∩ B := h x hxC
      rw [MySet.inter] at this
      rw [MySet.mem_spec A (fun x => x ∈ B)] at this
      exact this.left
    · rw [MySet.subset]
      intro x hxC
      rw [MySet.subset] at h
      have : x ∈ A ∩ B := h x hxC
      rw [MySet.inter] at this
      rw [MySet.mem_spec A (fun x => x ∈ B)] at this
      exact this.right

example (A B : MySet α) :
  A ⊆ A ∪ B := by
  rw [MySet.subset]
  intro x hxA
  rw [MySet.mem_union A B]
  exact Or.inl hxA

example (A B : MySet α) :
  B ⊆ A ∪ B := by
  rw [MySet.subset]
  intro x hxB
  rw [MySet.mem_union A B]
  exact Or.inr hxB

example (A B C : MySet α) :
  A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  constructor
  · intro h
    rw [MySet.subset]
    intro x hxAB
    rw [MySet.mem_union A B] at hxAB
    rcases hxAB with (hxA | hxB)
    · rw [MySet.subset] at h
      exact h.left x hxA
    · rw [MySet.subset] at h
      exact h.right x hxB
  · intro h
    constructor
    · rw [MySet.subset]
      intro x hxA
      rw [MySet.subset] at h
      have : x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inl hxA
      exact h x this
    · rw [MySet.subset]
      intro x hxB
      rw [MySet.subset] at h
      have : x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inr hxB
      exact h x this

-- Exercise 3.1.8
example (A B : MySet α) :
  A ∩ (A ∪ B) = A := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ A ∪ B)]
  rw [MySet.mem_union A B]
  constructor
  · intro h
    exact h.left
  · intro h
    constructor
    · exact h
    · exact Or.inl h

example (A B : MySet α) :
  A ∪ (A ∩ B) = A := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A (A ∩ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  constructor
  · intro h
    rcases h with (h | h)
    · exact h
    · exact h.left
  · intro h
    exact Or.inl h

-- Exercise 3.1.9
example (A B X : MySet α)
  (hu : A ∪ B = X) (hi : A ∩ B = ∅) :
  A = X \ B := by
  rw [MySet.ext]
  intro x
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ B)]
  rw [MySet.ext] at hu
  constructor
  · intro h
    constructor
    · have : x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inl h
      have := (hu x).mp this
      exact this
    · intro hxB
      have : x ∈ A ∩ B := by
        rw [MySet.inter]
        rw [MySet.mem_spec A (fun x => x ∈ B)]
        exact ⟨h, hxB⟩
      rw [hi] at this
      exact MySet.not_mem_empty this
  · intro h
    have : x ∈ A ∪ B := (hu x).mpr h.left
    rw [MySet.mem_union A B] at this
    rcases this with (hxA | hxB)
    · exact hxA
    · exact False.elim (h.right hxB)

example (A B X : MySet α)
  (hu : A ∪ B = X) (hi : A ∩ B = ∅) :
  B = X \ A := by
  rw [MySet.ext]
  intro x
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  rw [MySet.ext] at hu
  constructor
  · intro h
    constructor
    · have : x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inr h
      have := (hu x).mp this
      exact this
    · intro hxA
      have : x ∈ A ∩ B := by
        rw [MySet.inter]
        rw [MySet.mem_spec A (fun x => x ∈ B)]
        exact ⟨hxA, h⟩
      rw [hi] at this
      exact MySet.not_mem_empty this
  · intro h
    have : x ∈ A ∪ B := (hu x).mpr h.left
    rw [MySet.mem_union A B] at this
    rcases this with (hxA | hxB)
    · exact False.elim (h.right hxA)
    · exact hxB

-- Exercise 3.1.10
example (A B : MySet α) :
  MySet.disjoint (A \ B) (A ∩ B) := by
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec (A \ B) (fun x => x ∈ A ∩ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec A (fun x => x ∉ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  constructor
  · intro h
    exact False.elim (h.left.right h.right.right)
  · intro h
    exact False.elim (MySet.not_mem_empty h)

example (A B : MySet α) :
  MySet.disjoint (A \ B) (B \ A) := by
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec (A \ B) (fun x => x ∈ B \ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec A (fun x => x ∉ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec B (fun x => x ∉ A)]
  constructor
  · intro h
    exact False.elim (h.right.right h.left.left)
  · intro h
    exact False.elim (MySet.not_mem_empty h)

example (A B : MySet α) :
  MySet.disjoint (A ∩ B) (B \ A) := by
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec (A ∩ B) (fun x => x ∈ B \ A)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec B (fun x => x ∉ A)]
  constructor
  · intro h
    exact False.elim (h.right.right h.left.left)
  · intro h
    exact False.elim (MySet.not_mem_empty h)

example (A B : MySet α) :
  (A \ B) ∪ (A ∩ B) ∪ (B \ A) = A ∪ B := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union ((A \ B) ∪ (A ∩ B)) (B \ A)]
  rw [MySet.mem_union (A \ B) (A ∩ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec A (fun x => x ∉ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec B (fun x => x ∉ A)]
  rw [MySet.mem_union A B]
  constructor
  · intro h
    rcases h with (h | h)
    · rcases h with (h | h)
      · exact Or.inl h.left
      · exact Or.inr h.right
    · exact Or.inr h.left
  · intro h
    rcases h with (h | h)
    · by_cases hxB : x ∈ B
      · exact Or.inl (Or.inr ⟨h, hxB⟩)
      · exact Or.inl (Or.inl ⟨h, hxB⟩)
    · by_cases hxA : x ∈ A
      · exact Or.inl (Or.inr ⟨hxA, h⟩)
      · exact Or.inr ⟨h, hxA⟩

-- Exercise 3.1.11
example {α : Type u}
  (hrep : ∀ (A : MySet α) {β : Type u} (P : α → β → Prop),
    (∀ (x : α), x ∈ A →
      (∃ (y : β), P x y ∧ (∀ (z : β), P x z → y = z))) →
    (∃ (S : MySet β),
      ∀ (y : β), y ∈ S ↔ ∃ (x : α), x ∈ A ∧ P x y)) :
  ∀ (A : MySet α) (P : α → Prop),
    ∃ (S : MySet α),
      ∀ (x : α), x ∈ S ↔ x ∈ A ∧ P x := by
  intro A P
  by_cases h : ∃ (x : α), x ∈ A ∧ P x
  · rcases h with ⟨x', hx'A, hPx'⟩
    let P' : α → α → Prop :=
      fun x y => (P x ∧ y = x) ∨ (¬ P x ∧ y = x')
    have : ∀ (x : α), x ∈ A →
      (∃ (y : α), P' x y ∧ (∀ (z : α), P' x z → y = z)) := by
      intro x hxA
      by_cases hPx : P x
      · use x
        constructor
        · exact Or.inl ⟨hPx, rfl⟩
        · intro z hP'zx
          rcases hP'zx with (hP'zx | hP'zx)
          · rcases hP'zx with ⟨hPxz, hzx⟩
            exact hzx.symm
          · rcases hP'zx with ⟨hPxz, hzx'⟩
            by_contra
            exact hPxz hPx
      · use x'
        constructor
        · exact Or.inr ⟨hPx, rfl⟩
        · intro z hP'zx
          rcases hP'zx with (hP'zx | hP'zx)
          · rcases hP'zx with ⟨hPxz, hzx⟩
            by_contra
            exact hPx hPxz
          · rcases hP'zx with ⟨hPxz, hzx'⟩
            exact hzx'.symm
    rcases hrep A P' this with ⟨S, hS⟩
    use S
    intro x
    constructor
    · intro hxS
      rcases (hS x).mp hxS with ⟨y, hyA, hP'yx⟩
      rcases hP'yx with (hP'yx | hP'yx)
      · rcases hP'yx with ⟨hPy, hxy⟩
        rw [hxy]
        constructor
        · exact hyA
        · exact hPy
      · rcases hP'yx with ⟨hPy, hxy'⟩
        rw [hxy']
        constructor
        · exact hx'A
        · exact hPx'
    · intro hxA
      rcases hxA with ⟨hxA, hPx⟩
      have : x ∈ S := (hS x).mpr ⟨x, hxA, Or.inl ⟨hPx, rfl⟩⟩
      exact this
  · push_neg at h
    use ∅
    intro x
    constructor
    · intro hxS
      by_contra
      exact MySet.not_mem_empty hxS
    · intro h'
      rcases h' with ⟨hxA, hPx⟩
      by_contra
      have : ¬ P x := h x hxA
      exact this hPx

-- Exercise 3.1.12
-- (a)
example (A B A' B' : MySet α)
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  A' ∪ B' ⊆ A ∪ B := by
  rw [MySet.subset]
  intro x hxAB'
  rw [MySet.mem_union A' B'] at hxAB'
  rcases hxAB' with (hxA' | hxB')
  · rw [MySet.subset] at hA
    rw [MySet.mem_union A B]
    exact Or.inl (hA x hxA')
  · rw [MySet.subset] at hB
    rw [MySet.mem_union A B]
    exact Or.inr (hB x hxB')

example (A B A' B' : MySet α)
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  A' ∩ B' ⊆ A ∩ B := by
  rw [MySet.subset]
  intro x hxAB'
  rw [MySet.inter] at hxAB'
  rw [MySet.mem_spec A' (fun x => x ∈ B')] at hxAB'
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  constructor
  · rw [MySet.subset] at hA
    exact hA x hxAB'.left
  · rw [MySet.subset] at hB
    exact hB x hxAB'.right

-- (b)
example : ∃ (A B A' B' : MySet ℕ),
  A' ⊆ A ∧ B' ⊆ B ∧ ¬ (A' \ B' ⊆ A \ B) := by
  use ⦃1, 2⦄, ⦃1⦄, ⦃1⦄, ∅
  constructor
  · rw [MySet.subset]
    intro x hx
    rw [MySet.mem_pair 1 2]
    rw [MySet.mem_singleton 1 x] at hx
    exact Or.inl hx
  · constructor
    · rw [MySet.subset]
      intro x hx
      exact False.elim (MySet.not_mem_empty hx)
    · intro h
      rw [MySet.subset] at h
      have h1 : 1 ∈ (⦃1⦄ : MySet ℕ) \ ∅ := by
        rw [MySet.diff]
        rw [MySet.mem_spec ⦃1⦄ (fun x => x ∉ ∅)]
        constructor
        · rw [MySet.mem_singleton 1 1]
        · intro h'
          exact False.elim (MySet.not_mem_empty h')
      have h2 : 1 ∉ (⦃1, 2⦄ : MySet ℕ) \ ⦃1⦄ := by
        rw [MySet.diff]
        rw [MySet.mem_spec ⦃1, 2⦄ (fun x => x ∉ ⦃1⦄)]
        push_neg
        intro h'
        rw [MySet.mem_pair 1 2] at h'
        rw [MySet.mem_singleton 1 1]
      exact h2 (h 1 h1)

-- Exercise 3.1.13
example (A : MySet α) (hA : A.nonempty) :
  ¬ (∃ (B : MySet α), B.nonempty ∧ B ⊊ A) ↔ (∃ (x : α), A = ⦃x⦄) := by
  constructor
  · intro h
    push_neg at h
    rcases MySet.single_choice hA with ⟨x, hxA⟩
    use x
    have h' : (⦃x⦄ : MySet α).nonempty := by
      rw [MySet.nonempty]
      intro h'
      rw [MySet.ext] at h'
      have : x ∈ (⦃x⦄ : MySet α) := by
        rw [MySet.mem_singleton x x]
      have : x ∈ ∅ := (h' x).mp this
      exact MySet.not_mem_empty this
    have h'' : ⦃x⦄ ⊆ A := by
      rw [MySet.subset]
      intro y hy
      rw [MySet.mem_singleton x y] at hy
      rw [hy]
      exact hxA
    exact (h ⦃x⦄ h' h'').symm
  · intro h
    rcases h with ⟨x, hA⟩
    push_neg
    intro B hB hss
    rw [MySet.ext]
    intro y
    constructor
    · intro hy
      have : ∀ (y : α), y ∈ B → y = x := by
        intro y hy
        have : y ∈ A := hss y hy
        rw [hA] at this
        rw [MySet.mem_singleton x y] at this
        exact this
      have : y = x := this y hy
      rw [this]
      rw [hA]
      rw [MySet.mem_singleton x x]
    · intro hy
      rw [hA] at hy
      rw [MySet.mem_singleton x y] at hy
      rw [hy]
      rcases MySet.single_choice hB with ⟨z, hzB⟩
      rw [MySet.subset] at hss
      have : z ∈ A := hss z hzB
      rw [hA] at this
      rw [MySet.mem_singleton x z] at this
      rw [← this]
      exact hzB

end Exercises
