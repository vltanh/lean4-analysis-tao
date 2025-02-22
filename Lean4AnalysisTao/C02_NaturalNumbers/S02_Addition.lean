import Mathlib.Tactic

import Lean4AnalysisTao.C02_NaturalNumbers.S01_PeanoAxioms

axiom MyNat.add : MyNat → MyNat → MyNat
infixl:65 " + " => MyNat.add

axiom MyNat.zero_add :
  ∀ (m : MyNat), 𝟘 + m = m

axiom MyNat.succ_add :
  ∀ (n m : MyNat), n++ + m = (n + m)++

-- Lemma 2.2.2
theorem MyNat.add_zero :
  ∀ (n : MyNat), n + 𝟘 = n := by
  have hbase : 𝟘 + 𝟘 = 𝟘 := by
    rw [MyNat.zero_add 𝟘]
  have hind : ∀ {n : MyNat},
    n + 𝟘 = n → n++ + 𝟘 = n++ := by
    intro n hn
    rw [MyNat.succ_add n 𝟘]
    rw [hn]
  exact MyNat.induction hbase hind

-- Lemma 2.2.3
theorem MyNat.add_succ :
  ∀ (n m : MyNat), n + m++ = (n + m)++ := by
  have hbase : ∀ (m : MyNat), 𝟘 + m++ = (𝟘 + m)++ := by
    intro m
    rw [MyNat.zero_add]
    rw [MyNat.zero_add]
  have hind : ∀ {n : MyNat},
    (∀ (m : MyNat), n + m++ = (n + m)++) →
    ∀ (m : MyNat), n++ + m++ = (n++ + m)++ := by
    intro n hn
    intro m
    rw [MyNat.succ_add]
    rw [MyNat.succ_add]
    rw [hn m]
  exact MyNat.induction hbase hind

-- Proposition 2.2.4
theorem MyNat.add_comm :
  ∀ (n m : MyNat), n + m = m + n := by
  have hbase : ∀ (m : MyNat), 𝟘 + m = m + 𝟘 := by
    intro m
    rw [MyNat.zero_add]
    rw [MyNat.add_zero]
  have hind : ∀ {n : MyNat},
    (∀ (m : MyNat), n + m = m + n) →
    ∀ (m : MyNat), n++ + m = m + n++ := by
    intro n hn
    intro m
    rw [MyNat.succ_add]
    rw [MyNat.add_succ]
    rw [hn m]
  exact MyNat.induction hbase hind

-- Proposition 2.2.5
theorem MyNat.add_assoc :
  ∀ (a b c : MyNat), (a + b) + c = a + (b + c) := by
  sorry

-- Proposition 2.2.6
theorem MyNat.add_left_cancel :
  ∀ {a b c : MyNat}, a + b = a + c → b = c := by
  have hbase : ∀ {b c : MyNat}, 𝟘 + b = 𝟘 + c → b = c := by
    intro b c h
    rw [MyNat.zero_add] at h
    rw [MyNat.zero_add] at h
    exact h
  have hind : ∀ {a : MyNat},
    (∀ {b c : MyNat}, a + b = a + c → b = c) →
    ∀ {b c : MyNat}, a++ + b = a++ + c → b = c := by
    intro a ha
    intro b c h
    rw [MyNat.succ_add] at h
    rw [MyNat.succ_add] at h
    exact ha (MyNat.succ_inj h)
  exact MyNat.induction hbase hind

-- Definition 2.2.7
def MyNat.is_positive : MyNat → Prop :=
  fun n => n ≠ 𝟘

-- Proposition 2.2.8
theorem MyNat.pos_add {a : MyNat} (ha : a.is_positive) (b : MyNat) :
  (a + b).is_positive := by
  have : ∀ (b : MyNat), (a + b).is_positive := by
    have hbase : (a + 𝟘).is_positive := by
      rw [MyNat.add_zero]
      exact ha
    have hind : ∀ {b : MyNat},
      (a + b).is_positive →
      (a + b++).is_positive := by
      intro b hb
      rw [MyNat.add_succ]
      exact MyNat.succ_ne_zero (a + b)
    exact MyNat.induction hbase hind
  exact this b

theorem MyNat.pos_add' {a : MyNat} (ha : a.is_positive) (b : MyNat) :
  (b + a).is_positive := by
  rw [MyNat.add_comm]
  exact MyNat.pos_add ha b

-- Corollary 2.2.9
theorem MyNat.zero_zero_of_add_zero :
  ∀ (a b : MyNat), a + b = 𝟘 → a = 𝟘 ∧ b = 𝟘 := by
  intro a b hab
  by_contra h
  rw [not_and_or] at h
  rcases h with (ha | hb)
  · have : (a + b).is_positive := MyNat.pos_add ha b
    exact this hab
  · have : (a + b).is_positive := MyNat.pos_add' hb a
    exact this hab

-- Lemma 2.2.10
theorem MyNat.unique_pred_of_pos {a : MyNat} (ha : a.is_positive) :
  ∃ (b : MyNat), b++ = a ∧ (∃ (c : MyNat), c++ = a → b = c) := by
  sorry

-- Definition 2.2.11
def MyNat.ge : MyNat → MyNat → Prop :=
  fun n m => ∃ (a : MyNat), n = m + a
infixl:50 " ≥ " => MyNat.ge

def MyNat.le : MyNat → MyNat → Prop :=
  fun n m => m ≥ n
infixl:50 " ≤ " => MyNat.le

def MyNat.gt : MyNat → MyNat → Prop :=
  fun n m => n ≥ m ∧ n ≠ m
infixl:50 " > " => MyNat.gt

def MyNat.lt : MyNat → MyNat → Prop :=
  fun n m => m > n
infixl:50 " < " => MyNat.lt

-- Proposition 2.2.12
-- (a)
theorem MyNat.ge_refl :
  ∀ (a : MyNat), a ≥ a := by
  sorry

-- (b)
theorem MyNat.ge_trans :
  ∀ {a b c : MyNat}, a ≥ b → b ≥ c → a ≥ c := by
  sorry

-- (c)
theorem MyNat.ge_antisymm :
  ∀ {a b : MyNat}, a ≥ b → b ≥ a → a = b := by
  sorry

-- (d)
theorem MyNat.ge_iff_add_ge :
  ∀ {a b : MyNat} (c : MyNat), a ≥ b ↔ a + c ≥ b + c := by
  sorry

-- (e)
theorem MyNat.lt_iff_succ_le :
  ∀ {a b : MyNat}, a < b ↔ a++ ≤ b := by
  sorry

-- (f)
theorem MyNat.lt_iff_eq_add :
  ∀ {a b : MyNat}, a < b ↔ ∃ (d : MyNat), d.is_positive ∧ b = a + d := by
  sorry

-- Proposition 2.2.13
theorem MyNat.order_trichotomy (a b : MyNat) :
  ((a < b) ∧ ¬(a = b) ∧ ¬(a > b))
  ∨ (¬(a < b) ∧ (a = b) ∧ ¬(a > b))
  ∨ (¬(a < b) ∧ ¬(a = b) ∧ (a > b)) := by
  have h12 : ¬((a < b) ∧ (a = b)) := by
    rintro ⟨h1, h2⟩
    rw [MyNat.lt] at h1
    rw [MyNat.gt] at h1
    exact h1.right.symm h2
  have h23 : ¬((a = b) ∧ (a > b)) := by
    rintro ⟨h2, h3⟩
    rw [MyNat.gt] at h3
    exact h3.right h2
  have h13 : ¬((a < b) ∧ (a > b)) := by
    rintro ⟨h1, h3⟩
    rw [MyNat.lt] at h1
    rw [MyNat.gt] at h1
    rw [MyNat.gt] at h3
    have : a = b := MyNat.ge_antisymm h3.left h1.left
    exact h3.right this
  have h123 : ∀ (a b : MyNat), (a < b) ∨ (a = b) ∨ (a > b) := by
    have hbase : ∀ (b : MyNat), (𝟘 < b) ∨ (𝟘 = b) ∨ (𝟘 > b) := by
      have : ∀ (b : MyNat), 𝟘 ≤ b := by
        sorry
      intro b
      have : 𝟘 = b ∨ 𝟘 < b := by
        by_cases h : 𝟘 = b
        · exact Or.inl h
        · rw [← Ne.eq_def] at h
          exact Or.inr ⟨this b, h.symm⟩
      rcases this with (h1 | h2)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h2
    have hind : ∀ {a : MyNat},
      (∀ (b : MyNat), (a < b) ∨ (a = b) ∨ (a > b)) →
      ∀ (b : MyNat), (a++ < b) ∨ (a++ = b) ∨ (a++ > b) := by
      intro a ha
      intro b
      rcases ha b with (h1 | h2 | h3)
      · have := MyNat.lt_iff_succ_le.mp h1
        by_cases h : a++ = b
        · exact Or.inr (Or.inl h)
        · rw [← Ne.eq_def] at h
          exact Or.inl ⟨this, h.symm⟩
      · have : a++ > b := by
          sorry
        exact Or.inr (Or.inr this)
      · have : a++ > b := by
          sorry
        exact Or.inr (Or.inr this)
    exact MyNat.induction hbase hind
  rcases h123 a b with (h1 | h2 | h3)
  · have h2 : ¬(a = b) := by
      rw [not_and] at h12
      exact h12 h1
    have h3 : ¬(a > b) := by
      rw [not_and] at h13
      exact h13 h1
    exact Or.inl ⟨h1, h2, h3⟩
  · have h1 : ¬(a < b) := by
      rw [not_and'] at h12
      exact h12 h2
    have h3 : ¬(a > b) := by
      rw [not_and] at h23
      exact h23 h2
    exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  · have h1 : ¬(a < b) := by
      rw [not_and'] at h13
      exact h13 h3
    have h2 : ¬(a = b) := by
      rw [not_and'] at h23
      exact h23 h3
    exact Or.inr (Or.inr ⟨h1, h2, h3⟩)

-- Proposition 2.2.14
theorem MyNat.strong_induction {m₀ : MyNat} {P : MyNat → Prop}
  (hind : ∀ (m : MyNat), m ≥ m₀ → ((∀ (m' : MyNat), m₀ ≤ m' → m' < m → P m') → P m)) :
  ∀ {m : MyNat}, m ≥ m₀ → P m := by
  sorry

section Exercises

-- Exercise 2.2.6
example {n : MyNat} {P : MyNat → Prop}
  (hind : ∀ (m : MyNat), P m++ → P m) (hbase : P n) :
  ∀ (m : MyNat), m ≤ n → P m := by
  sorry

-- Exercise 2.2.7
example {n : MyNat} {P : MyNat → Prop}
  (hind : ∀ (m : MyNat), P m++ → P m) :
  P n → (∀ (m : MyNat), m ≥ n → P m) := by
  sorry

end Exercises
