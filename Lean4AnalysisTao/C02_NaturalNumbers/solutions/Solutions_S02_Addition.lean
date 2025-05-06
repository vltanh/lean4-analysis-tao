import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Constructor

import Lean4AnalysisTao.C02_NaturalNumbers.S01_PeanoAxioms

-- Definition 2.2.1
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
    rw [MyNat.zero_add m]
    rw [MyNat.zero_add (m++)]
  have hind : ∀ {n : MyNat},
    (∀ (m : MyNat), n + m++ = (n + m)++) →
    ∀ (m : MyNat), n++ + m++ = (n++ + m)++ := by
    intro n hn
    intro m
    rw [MyNat.succ_add n m]
    rw [MyNat.succ_add n (m++)]
    rw [hn m]
  exact MyNat.induction hbase hind

-- Proposition 2.2.4
theorem MyNat.add_comm :
  ∀ (n m : MyNat), n + m = m + n := by
  have hbase : ∀ (m : MyNat), 𝟘 + m = m + 𝟘 := by
    intro m
    rw [MyNat.zero_add m]
    rw [MyNat.add_zero m]
  have hind : ∀ {n : MyNat},
    (∀ (m : MyNat), n + m = m + n) →
    ∀ (m : MyNat), n++ + m = m + n++ := by
    intro n hn
    intro m
    rw [MyNat.succ_add n m]
    rw [MyNat.add_succ m n]
    rw [hn m]
  exact MyNat.induction hbase hind

-- Proposition 2.2.5
theorem MyNat.add_assoc :
  ∀ (a b c : MyNat), (a + b) + c = a + (b + c) := by
  have hbase : ∀ (b c : MyNat), (𝟘 + b) + c = 𝟘 + (b + c) := by
    intro b c
    rw [MyNat.zero_add b]
    rw [MyNat.zero_add (b + c)]
  have hind : ∀ {a : MyNat},
    (∀ (b c : MyNat), (a + b) + c = a + (b + c)) →
    ∀ (b c : MyNat), (a++ + b) + c = a++ + (b + c) := by
    intro a ha
    intro b c
    rw [MyNat.succ_add a b]
    rw [MyNat.succ_add (a + b) c]
    rw [MyNat.succ_add a (b + c)]
    rw [ha b c]
  exact MyNat.induction hbase hind

-- Proposition 2.2.6
theorem MyNat.add_left_cancel :
  ∀ {a b c : MyNat}, a + b = a + c → b = c := by
  have hbase : ∀ {b c : MyNat}, 𝟘 + b = 𝟘 + c → b = c := by
    intro b c h
    rw [MyNat.zero_add b] at h
    rw [MyNat.zero_add c] at h
    exact h
  have hind : ∀ {a : MyNat},
    (∀ {b c : MyNat}, a + b = a + c → b = c) →
    ∀ {b c : MyNat}, a++ + b = a++ + c → b = c := by
    intro a ha
    intro b c h
    rw [MyNat.succ_add a b] at h
    rw [MyNat.succ_add a c] at h
    exact ha (MyNat.succ_inj h)
  exact MyNat.induction hbase hind

-- Definition 2.2.7
def MyNat.is_positive (n : MyNat) : Prop :=
  n ≠ 𝟘

-- Proposition 2.2.8
theorem MyNat.pos_add {a : MyNat} (ha : a.is_positive) (b : MyNat) :
  (a + b).is_positive := by
  have : ∀ (b : MyNat), (a + b).is_positive := by
    have hbase : (a + 𝟘).is_positive := by
      rw [MyNat.add_zero a]
      exact ha
    have hind : ∀ {b : MyNat},
      (a + b).is_positive →
      (a + b++).is_positive := by
      intro b hb
      rw [MyNat.add_succ a b]
      exact MyNat.succ_ne_zero (a + b)
    exact MyNat.induction hbase hind
  exact this b

theorem MyNat.pos_add' {a : MyNat} (ha : a.is_positive) (b : MyNat) :
  (b + a).is_positive := by
  rw [MyNat.add_comm b a]
  exact MyNat.pos_add ha b

-- Corollary 2.2.9
theorem MyNat.zero_zero_of_add_zero :
  ∀ {a b : MyNat}, a + b = 𝟘 → a = 𝟘 ∧ b = 𝟘 := by
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
  ∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c) := by
  have : ∀ (a : MyNat), a.is_positive →
    (∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c)) := by
    have hbase : 𝟘.is_positive →
      ∃ (b : MyNat), b++ = 𝟘 ∧ (∀ (c : MyNat), c++ = 𝟘 → b = c) := by
      intro h
      rw [MyNat.is_positive] at h
      exact False.elim (h rfl)
    have hind : ∀ {a : MyNat},
      (a.is_positive →
        (∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c))) →
      ((a++).is_positive →
        (∃ (b : MyNat), b++ = a++ ∧ (∀ (c : MyNat), c++ = a++ → b = c))) := by
      intro a ha
      intro has
      use a
      constructor
      · exact rfl
      · intro c hc
        exact MyNat.succ_inj hc.symm
    exact MyNat.induction hbase hind
  exact this a ha

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
  intro a
  rw [MyNat.ge]
  use 𝟘
  rw [MyNat.add_zero a]

-- (b)
theorem MyNat.ge_trans :
  ∀ {a b c : MyNat}, a ≥ b → b ≥ c → a ≥ c := by
  intro a b c
  intro hab hbc
  rcases hab with ⟨d, hd⟩
  rcases hbc with ⟨e, he⟩
  rw [MyNat.ge]
  use d + e
  rw [hd]
  rw [he]
  rw [MyNat.add_assoc c e d]
  rw [MyNat.add_comm e d]

-- (c)
theorem MyNat.ge_antisymm :
  ∀ {a b : MyNat}, a ≥ b → b ≥ a → a = b := by
  intro a b
  intro hab hba
  rcases hab with ⟨d, hd⟩
  rcases hba with ⟨e, he⟩
  have : 𝟘 = e + d := by
    rw [he] at hd
    rw [← MyNat.add_zero a] at hd
    rw [MyNat.add_assoc a 𝟘 e] at hd
    rw [MyNat.zero_add e] at hd
    rw [MyNat.add_assoc a e d] at hd
    exact MyNat.add_left_cancel hd
  have : e = 𝟘 ∧ d = 𝟘 := by
    exact MyNat.zero_zero_of_add_zero this.symm
  rw [this.right] at hd
  rw [MyNat.add_zero b] at hd
  exact hd

-- (d)
theorem MyNat.ge_iff_add_ge :
  ∀ {a b : MyNat} (c : MyNat), a ≥ b ↔ a + c ≥ b + c := by
  intro a b c
  constructor
  · intro hd
    rcases hd with ⟨d, hd⟩
    rw [MyNat.ge]
    use d
    rw [hd]
    rw [MyNat.add_assoc b c d]
    rw [MyNat.add_comm c d]
    rw [MyNat.add_assoc b d c]
  · intro hd
    rcases hd with ⟨d, hd⟩
    rw [MyNat.ge]
    use d
    rw [MyNat.add_comm a c] at hd
    rw [MyNat.add_comm b c] at hd
    rw [MyNat.add_assoc c b d] at hd
    exact MyNat.add_left_cancel hd

-- (e)
theorem MyNat.lt_iff_succ_le :
  ∀ {a b : MyNat}, a < b ↔ a++ ≤ b := by
  intro a b
  constructor
  · rw [MyNat.lt]
    rw [MyNat.gt]
    intro hba
    rcases hba with ⟨hba, hne⟩
    rw [MyNat.ge] at hba
    rcases hba with ⟨d, hd⟩
    have : d ≠ 𝟘 := by
      by_contra h
      rw [h] at hd
      rw [MyNat.add_zero a] at hd
      exact hne hd
    rcases MyNat.unique_pred_of_pos this with ⟨e, he, huniq⟩
    rw [MyNat.le]
    rw [MyNat.ge]
    use e
    rw [MyNat.succ_add a e]
    rw [← MyNat.add_succ a e]
    rw [he]
    exact hd
  · intro hasb
    rw [MyNat.le] at hasb
    rcases hasb with ⟨d, hd⟩
    rw [MyNat.lt]
    rw [MyNat.gt]
    constructor
    · rw [MyNat.ge]
      use (d++)
      rw [hd]
      rw [MyNat.succ_add a d]
      rw [MyNat.add_succ a d]
    · by_contra h
      rw [h] at hd
      rw [MyNat.succ_add a] at hd
      rw [← MyNat.add_zero a] at hd
      rw [MyNat.add_assoc a 𝟘 d] at hd
      rw [MyNat.zero_add d] at hd
      rw [← MyNat.add_succ a d] at hd
      have := MyNat.add_left_cancel hd
      exact MyNat.succ_ne_zero d this.symm

-- (f)
theorem MyNat.lt_iff_eq_add :
  ∀ {a b : MyNat}, a < b ↔ ∃ (d : MyNat), d.is_positive ∧ b = a + d := by
  intro a b
  constructor
  · intro hba
    rw [MyNat.lt] at hba
    rcases hba with ⟨hba, hne⟩
    rw [MyNat.ge] at hba
    rcases hba with ⟨d, hd⟩
    have : d ≠ 𝟘 := by
      by_contra h
      rw [h] at hd
      rw [MyNat.add_zero a] at hd
      exact hne hd
    use d
    constructor
    · exact this
    · exact hd
  · intro hd
    rcases hd with ⟨d, hd, hd'⟩
    rw [MyNat.lt]
    rw [MyNat.gt]
    constructor
    · rw [MyNat.ge]
      use d
    · by_contra h
      rw [← MyNat.add_zero b] at hd'
      rw [h] at hd'
      have : 𝟘 = d :=
        MyNat.add_left_cancel hd'
      exact hd this.symm

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
        intro b
        rw [MyNat.le]
        rw [MyNat.ge]
        use b
        rw [MyNat.zero_add b]
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
          rw [MyNat.gt]
          constructor
          · rw [MyNat.ge]
            use (𝟘++)
            rw [MyNat.add_succ b 𝟘]
            rw [MyNat.add_zero b]
            rw [h2]
          · rw [h2]
            by_contra h
            rw [← MyNat.add_zero b] at h
            rw [← MyNat.add_succ b 𝟘] at h
            have : 𝟘++ = 𝟘 := MyNat.add_left_cancel h
            exact MyNat.succ_ne_zero 𝟘 this
        exact Or.inr (Or.inr this)
      · have : a++ > b := by
          rcases MyNat.lt_iff_eq_add.mp h3 with ⟨d, hd, hd'⟩
          rw [MyNat.gt] at h3
          rcases h3 with ⟨hge, hne⟩
          rw [MyNat.gt]
          constructor
          · rw [MyNat.ge]
            use (d++)
            rw [MyNat.add_succ b d]
            rw [hd']
          · by_contra h
            rw [← MyNat.add_zero b] at h
            rw [hd'] at h
            rw [← MyNat.add_succ b d] at h
            have : d++ = 𝟘 := MyNat.add_left_cancel h
            exact MyNat.succ_ne_zero d this
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
  (hind : ∀ {m : MyNat}, m ≥ m₀ →
    ((∀ (m' : MyNat), m₀ ≤ m' → m' < m → P m') → P m)) :
  ∀ {m : MyNat}, m ≥ m₀ → P m := by
  let Q : MyNat → Prop :=
    fun n => (∀ (m : MyNat), m₀ ≤ m → m < n → P m)
  have : ∀ (n : MyNat), Q n := by
    have hbase : Q 𝟘 := by
      dsimp [Q]
      intro m hm hm'
      rw [MyNat.lt] at hm'
      rw [MyNat.gt] at hm'
      rcases hm' with ⟨hm', hne⟩
      rw [MyNat.ge] at hm'
      rcases hm' with ⟨d, hd⟩
      have : m + d ≠ 𝟘 :=
        MyNat.pos_add hne.symm d
      exact False.elim (this hd.symm)
    have hind : ∀ {n : MyNat}, Q n → Q n++ := by
      intro n hn
      dsimp [Q]
      dsimp [Q] at hn
      intro m hm hm'
      rcases MyNat.order_trichotomy m n with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        exact hn m hm hlt
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        rw [heq] at hm
        rw [MyNat.le] at hm
        exact hind hm hn
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        by_contra h
        rw [MyNat.lt] at hm'
        rw [MyNat.gt] at hm'
        rcases hm' with ⟨hm', hne⟩
        have : n++ ≤ m := MyNat.lt_iff_succ_le.mp hgt
        have : n++ = m := ge_antisymm hm' this
        exact hne this
    exact MyNat.induction hbase hind
  intro m hm
  exact hind hm (this m)

section Exercises

-- Exercise 2.2.6
example {n : MyNat} {P : MyNat → Prop}
  (hbase : P n) (hind : ∀ {m : MyNat}, P m++ → P m) :
  ∀ {m : MyNat}, m ≤ n → P m := by
  have : ∀ {n : MyNat},
    P n → ∀ {m : MyNat}, m ≤ n → P m := by
    have hbase :
      P 𝟘 → ∀ {m : MyNat}, m ≤ 𝟘 → P m := by
      intro hbase
      intro m hm
      have : m = 𝟘 := by
        rw [MyNat.le] at hm
        rw [MyNat.ge] at hm
        rcases hm with ⟨d, hd⟩
        rcases MyNat.zero_zero_of_add_zero hd.symm with ⟨hd, hd'⟩
        exact hd
      rw [this]
      exact hbase
    have hind : ∀ {n : MyNat},
      (P n → ∀ {m : MyNat}, m ≤ n → P m) →
      (P n++ → ∀ {m : MyNat}, m ≤ n++ → P m) := by
      intro n hn
      intro hbase
      intro m hm
      rcases MyNat.order_trichotomy m (n++) with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        have : m ≤ n := by
          have := MyNat.lt_iff_succ_le.mp hlt
          rw [MyNat.le] at this
          rw [MyNat.ge] at this
          rcases this with ⟨d, hd⟩
          rw [MyNat.le]
          rw [MyNat.ge]
          use d
          rw [MyNat.succ_add m d] at hd
          exact MyNat.succ_inj hd
        exact hn (hind hbase) this
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        exact hbase
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        by_contra h
        rw [MyNat.gt] at hgt
        rcases hgt with ⟨hge, hne⟩
        have : m = n++ := MyNat.ge_antisymm hge hm
        exact hne this
    exact MyNat.induction hbase hind
  intro m
  exact this hbase

-- Exercise 2.2.7
example {n : MyNat} {P : MyNat → Prop}
  (hind : ∀ {m : MyNat}, P m → P m++) :
  P n → (∀ {m : MyNat}, m ≥ n → P m) := by
  intro hn
  have : ∀ {m : MyNat}, m ≥ n → P m := by
    have hbase : 𝟘 ≥ n → P 𝟘 := by
      intro hn'
      have : n = 𝟘 := by
        rw [MyNat.ge] at hn'
        rcases hn' with ⟨d, hd⟩
        rcases MyNat.zero_zero_of_add_zero hd.symm with ⟨hd, hd'⟩
        exact hd
      rw [this] at hn
      exact hn
    have hind : ∀ {m : MyNat}, (m ≥ n → P m) → (m++ ≥ n → P m++) := by
      intro m hm
      intro hge
      rcases MyNat.order_trichotomy (m++) n with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        rw [MyNat.lt] at hlt
        rw [MyNat.gt] at hlt
        rcases hlt with ⟨hle, hne⟩
        have : m++ = n := MyNat.ge_antisymm hge hle
        rw [this]
        exact hn
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        exact hn
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        rw [← MyNat.lt] at hgt
        have : m ≥ n := by
          have := MyNat.lt_iff_succ_le.mp hgt
          rw [MyNat.le] at this
          rw [MyNat.ge] at this
          rcases this with ⟨d, hd⟩
          rw [MyNat.ge]
          use d
          rw [MyNat.succ_add n d] at hd
          exact MyNat.succ_inj hd
        have : P m := hm this
        exact hind this
    exact MyNat.induction hbase hind
  intro m hmn
  exact this hmn

end Exercises
