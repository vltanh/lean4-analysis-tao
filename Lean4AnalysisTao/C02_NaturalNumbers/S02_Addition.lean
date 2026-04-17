import Lean4AnalysisTao.Util
import Lean4AnalysisTao.C02_NaturalNumbers.S01_PeanoAxioms

-- Definition 2.2.1
axiom MyNat.add : MyNat → MyNat → MyNat
infixl:65 " + " => MyNat.add

axiom MyNat.zero_add
    (m : MyNat) :
    𝟘 + m = m

axiom MyNat.succ_add
    (n m : MyNat) :
    n++ + m = (n + m)++

-- Lemma 2.2.2
theorem MyNat.add_zero
    (n : MyNat) :
    n + 𝟘 = n := by
  have hbase :
      𝟘 + 𝟘 = 𝟘 := by
    rw [MyNat.zero_add 𝟘]
  have hind
      (n : MyNat)
      (hn : n + 𝟘 = n) :
      n++ + 𝟘 = n++ := by
    rw [MyNat.succ_add n 𝟘]
    rw [hn]
  exact MyNat.induction (fun n => n + 𝟘 = n) hbase hind n

-- Lemma 2.2.3
theorem MyNat.add_succ
    (n m : MyNat) :
    n + m++ = (n + m)++ := by
  have hbase
      (m : MyNat) :
      𝟘 + m++ = (𝟘 + m)++ := by
    rw [MyNat.zero_add m]
    rw [MyNat.zero_add (m++)]
  have hind
      (n : MyNat)
      (hn : ∀ (m : MyNat), n + m++ = (n + m)++)
      (m : MyNat) :
      n++ + m++ = (n++ + m)++ := by
    rw [MyNat.succ_add n m]
    rw [MyNat.succ_add n (m++)]
    rw [hn m]
  exact MyNat.induction (fun n => ∀ (m : MyNat), n + m++ = (n + m)++) hbase hind n m

-- Proposition 2.2.4
theorem MyNat.add_comm
    (n m : MyNat) :
    n + m = m + n := by
  have hbase
      (m : MyNat) :
      𝟘 + m = m + 𝟘 := by
    rw [MyNat.zero_add m]
    rw [MyNat.add_zero m]
  have hind
      (n : MyNat)
      (hn : ∀ (m : MyNat), n + m = m + n)
      (m : MyNat) :
      n++ + m = m + n++ := by
    rw [MyNat.succ_add n m]
    rw [MyNat.add_succ m n]
    rw [hn m]
  exact MyNat.induction (fun n => ∀ (m : MyNat), n + m = m + n) hbase hind n m

-- Proposition 2.2.5
theorem MyNat.add_assoc
    (a b c : MyNat) :
    (a + b) + c = a + (b + c) := by
  sorry

-- Proposition 2.2.6
theorem MyNat.add_left_cancel
    (a b c : MyNat)
    (h : a + b = a + c) :
    b = c := by
  have hbase
      (b c : MyNat)
      (h : 𝟘 + b = 𝟘 + c) :
      b = c := by
    rw [MyNat.zero_add b] at h
    rw [MyNat.zero_add c] at h
    exact h
  have hind
      (a : MyNat)
      (ha : ∀ (b c : MyNat), a + b = a + c → b = c)
      (b c : MyNat)
      (h : a++ + b = a++ + c) :
      b = c := by
    rw [MyNat.succ_add a b] at h
    rw [MyNat.succ_add a c] at h
    exact ha b c (MyNat.succ_inj (a + b) (a + c) h)
  exact MyNat.induction (fun a => ∀ (b c : MyNat), a + b = a + c → b = c) hbase hind a b c h

-- Definition 2.2.7
def MyNat.is_positive
    (n : MyNat) :
    Prop :=
  n ≠ 𝟘

-- Proposition 2.2.8
theorem MyNat.pos_add
    (a : MyNat)
    (ha : MyNat.is_positive a)
    (b : MyNat) :
    (MyNat.is_positive (a + b)) := by
  have hall
      (b : MyNat) :
      (MyNat.is_positive (a + b)) := by
    have hbase :
        (MyNat.is_positive (a + 𝟘)) := by
      rw [MyNat.add_zero a]
      exact ha
    have hind
        (b : MyNat)
        (hb : (MyNat.is_positive (a + b))) :
        (MyNat.is_positive (a + b++)) := by
      rw [MyNat.add_succ a b]
      exact MyNat.succ_ne_zero (a + b)
    exact MyNat.induction (fun b => (MyNat.is_positive (a + b))) hbase hind b
  exact hall b

theorem MyNat.pos_add'
    (a : MyNat)
    (ha : MyNat.is_positive a)
    (b : MyNat) :
    (MyNat.is_positive (b + a)) := by
  rw [MyNat.add_comm b a]
  exact MyNat.pos_add a ha b

-- Corollary 2.2.9
theorem MyNat.zero_zero_of_add_zero
    (a b : MyNat)
    (hab : a + b = 𝟘) :
    a = 𝟘 ∧ b = 𝟘 := by
  by_contra hne
  rw [not_and_or (a = 𝟘) (b = 𝟘)] at hne
  rcases hne with (ha | hb)
  · have hpos : (MyNat.is_positive (a + b)) := MyNat.pos_add a ha b
    exact hpos hab
  · have hpos : (MyNat.is_positive (a + b)) := MyNat.pos_add' b hb a
    exact hpos hab

-- Lemma 2.2.10
theorem MyNat.unique_pred_of_pos
    (a : MyNat)
    (ha : MyNat.is_positive a) :
    ∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c) := by
  sorry

-- Definition 2.2.11
def MyNat.ge
    (n m : MyNat) :
    Prop :=
  ∃ (a : MyNat), n = m + a
infixl:50 " ≥ " => MyNat.ge

def MyNat.le
    (n m : MyNat) :
    Prop :=
  m ≥ n
infixl:50 " ≤ " => MyNat.le

def MyNat.gt
    (n m : MyNat) :
    Prop :=
  n ≥ m ∧ n ≠ m
infixl:50 " > " => MyNat.gt

def MyNat.lt
    (n m : MyNat) :
    Prop :=
  m > n
infixl:50 " < " => MyNat.lt

-- Proposition 2.2.12
-- (a)
theorem MyNat.ge_refl
    (a : MyNat) :
    a ≥ a := by
  sorry

-- (b)
theorem MyNat.ge_trans
    (a b c : MyNat)
    (hab : a ≥ b)
    (hbc : b ≥ c) :
    a ≥ c := by
  sorry

-- (c)
theorem MyNat.ge_antisymm
    (a b : MyNat)
    (hab : a ≥ b)
    (hba : b ≥ a) :
    a = b := by
  sorry

-- (d)
theorem MyNat.ge_iff_add_ge
    (a b c : MyNat) :
    a ≥ b ↔ a + c ≥ b + c := by
  sorry

-- (e)
theorem MyNat.lt_iff_succ_le
    (a b : MyNat) :
    a < b ↔ a++ ≤ b := by
  sorry

-- (f)
theorem MyNat.lt_iff_eq_add
    (a b : MyNat) :
    a < b ↔ ∃ (d : MyNat), MyNat.is_positive d ∧ b = a + d := by
  sorry

-- Proposition 2.2.13
theorem MyNat.order_trichotomy
    (a b : MyNat) :
    ((a < b) ∧ ¬(a = b) ∧ ¬(a > b))
    ∨ (¬(a < b) ∧ (a = b) ∧ ¬(a > b))
    ∨ (¬(a < b) ∧ ¬(a = b) ∧ (a > b)) := by
  have h12 :
      ¬((a < b) ∧ (a = b)) := by
    intro ⟨h1, h2⟩
    dsimp only [MyNat.lt] at h1
    dsimp only [MyNat.gt] at h1
    exact Ne.symm (And.right h1) h2
  have h23 :
      ¬((a = b) ∧ (a > b)) := by
    intro ⟨h2, h3⟩
    dsimp only [MyNat.gt] at h3
    exact And.right h3 h2
  have h13 :
      ¬((a < b) ∧ (a > b)) := by
    intro ⟨h1, h3⟩
    dsimp only [MyNat.lt] at h1
    dsimp only [MyNat.gt] at h1
    dsimp only [MyNat.gt] at h3
    have heq :
        a = b :=
      MyNat.ge_antisymm a b (And.left h3) (And.left h1)
    exact And.right h3 heq
  have h123
      (a b : MyNat) :
      (a < b) ∨ (a = b) ∨ (a > b) := by
    have hbase
        (b : MyNat) :
        (𝟘 < b) ∨ (𝟘 = b) ∨ (𝟘 > b) := by
      have hle
          (b : MyNat) :
          𝟘 ≤ b := by
        sorry
      have heq_or_lt :
          𝟘 = b ∨ 𝟘 < b := by
        by_cases heq : 𝟘 = b
        · exact Or.inl heq
        · rw [← Ne.eq_def] at heq
          exact Or.inr (And.intro (hle b) (Ne.symm heq))
      rcases heq_or_lt with (h1 | h2)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h2
    have hind
        (a : MyNat)
        (ha : ∀ (b : MyNat), (a < b) ∨ (a = b) ∨ (a > b))
        (b : MyNat) :
        (a++ < b) ∨ (a++ = b) ∨ (a++ > b) := by
      rcases ha b with (h1 | h2 | h3)
      · have hle : a++ ≤ b := Iff.mp (MyNat.lt_iff_succ_le a b) h1
        by_cases heq : a++ = b
        · exact Or.inr (Or.inl heq)
        · rw [← Ne.eq_def] at heq
          exact Or.inl (And.intro hle (Ne.symm heq))
      · have hgt : a++ > b := by
          sorry
        exact Or.inr (Or.inr hgt)
      · have hgt : a++ > b := by
          sorry
        exact Or.inr (Or.inr hgt)
    exact MyNat.induction (fun a => ∀ (b : MyNat), (a < b) ∨ (a = b) ∨ (a > b)) hbase hind a b
  rcases h123 a b with (h1 | h2 | h3)
  · have h2 : ¬(a = b) := by
      rw [@not_and (a < b) (a = b)] at h12
      exact h12 h1
    have h3 :
        ¬(a > b) := by
      rw [@not_and (a < b) (a > b)] at h13
      exact h13 h1
    exact Or.inl (And.intro h1 (And.intro h2 h3))
  · have h1 : ¬(a < b) := by
      rw [@not_and' (a < b) (a = b)] at h12
      exact h12 h2
    have h3 :
        ¬(a > b) := by
      rw [@not_and (a = b) (a > b)] at h23
      exact h23 h2
    exact Or.inr (Or.inl (And.intro h1 (And.intro h2 h3)))
  · have h1 : ¬(a < b) := by
      rw [@not_and' (a < b) (a > b)] at h13
      exact h13 h3
    have h2 :
        ¬(a = b) := by
      rw [@not_and' (a = b) (a > b)] at h23
      exact h23 h3
    exact Or.inr (Or.inr (And.intro h1 (And.intro h2 h3)))

-- Proposition 2.2.14
theorem MyNat.strong_induction
    (m₀ : MyNat)
    (P : MyNat → Prop)
    (hind : ∀ (m : MyNat), m ≥ m₀ →
    ((∀ (m' : MyNat), m₀ ≤ m' → m' < m → P m') → P m)) :
    ∀ (m : MyNat), m ≥ m₀ → P m := by
  sorry

section Exercises

-- Exercise 2.2.6
example
    (n : MyNat)
    (P : MyNat → Prop)
    (hbase : P n)
    (hind : ∀ (m : MyNat), P m++ → P m) :
    ∀ (m : MyNat), m ≤ n → P m := by
  sorry

-- Exercise 2.2.7
example
    (n : MyNat)
    (P : MyNat → Prop)
    (hind : ∀ (m : MyNat), P m → P m++)
    (hn : P n) :
    ∀ (m : MyNat), m ≥ n → P m := by
  sorry

end Exercises
