import Lean4AnalysisTao.C02_NaturalNumbers.S03_Multiplication

-- Lemma 2.3.2
example
    (n : MyNat) :
    n * 𝟘 = 𝟘 := by
  have hbase : 𝟘 * 𝟘 = 𝟘 := by
    rw [MyNat.zero_mul 𝟘]
  have hind
      (n : MyNat)
      (hn : n * 𝟘 = 𝟘) :
      n++ * 𝟘 = 𝟘 := by
    rw [MyNat.succ_mul n 𝟘]
    rw [hn]
    rw [MyNat.add_zero 𝟘]
  exact MyNat.induction (fun n => n * 𝟘 = 𝟘) hbase hind n

example
    (n m : MyNat) :
    n * m++ = n * m + n := by
  have hbase
      (m : MyNat) :
      𝟘 * m++ = 𝟘 * m + 𝟘 := by
    rw [MyNat.zero_mul m]
    rw [MyNat.zero_mul (m++)]
    rw [MyNat.zero_add 𝟘]
  have hind
      (n : MyNat)
      (hn : ∀ (m : MyNat), n * m++ = n * m + n)
      (m : MyNat) :
      n++ * m++ = n++ * m + n++ := by
    rw [MyNat.succ_mul n m]
    rw [MyNat.succ_mul n (m++)]
    rw [hn m]
    rw [MyNat.add_assoc (n * m) n (m++)]
    rw [MyNat.add_assoc (n * m) m (n++)]
    rw [MyNat.add_succ n m]
    rw [MyNat.add_comm m (n++)]
    rw [MyNat.succ_add n m]
  exact MyNat.induction (fun n => ∀ (m : MyNat), n * m++ = n * m + n) hbase hind n m

example
    (n m : MyNat) :
    n * m = m * n := by
  have hbase
      (m : MyNat) :
      𝟘 * m = m * 𝟘 := by
    rw [MyNat.zero_mul m]
    rw [MyNat.mul_zero m]
  have hind
      (n : MyNat)
      (hn : ∀ (m : MyNat), n * m = m * n)
      (m : MyNat) :
      n++ * m = m * n++ := by
    rw [MyNat.succ_mul n m]
    rw [MyNat.mul_succ m n]
    rw [hn m]
  exact MyNat.induction (fun n => ∀ (m : MyNat), n * m = m * n) hbase hind n m

-- Lemma 2.3.3
example
    (n m : MyNat)
    (hn : MyNat.is_positive n)
    (hm : MyNat.is_positive m) :
    (MyNat.is_positive (n * m)) := by
  have hall
      (n : MyNat)
      (hn : MyNat.is_positive n)
      (m : MyNat)
      (hm : MyNat.is_positive m) :
      (MyNat.is_positive (n * m)) := by
    have hbase
        (h : 𝟘.is_positive)
        (m : MyNat)
        (hm : MyNat.is_positive m) :
        (MyNat.is_positive (𝟘 * m)) := by
      rw [MyNat.zero_mul m]
      exact h
    have hind
        (n : MyNat)
        (hn : MyNat.is_positive n →
          ∀ (m : MyNat), MyNat.is_positive m → (MyNat.is_positive (n * m)))
        (hnspos : (MyNat.is_positive (n++)))
        (m : MyNat)
        (hmpos : MyNat.is_positive m) :
        (MyNat.is_positive (n++ * m)) := by
      rw [MyNat.succ_mul n m]
      exact MyNat.pos_add' m hmpos (n * m)
    exact MyNat.induction
      (fun n => MyNat.is_positive n →
        ∀ (m : MyNat), MyNat.is_positive m → (MyNat.is_positive (n * m))) hbase hind n hn m hm
  exact hall n hn m hm

example
    (n m : MyNat) :
    n * m = 𝟘 ↔ n = 𝟘 ∨ m = 𝟘 := by
  constructor
  · intro hnm
    by_contra hor
    have hn : n ≠ 𝟘 :=
      fun heq => hor (Or.inl heq)
    have hm : m ≠ 𝟘 :=
      fun heq => hor (Or.inr heq)
    have hpos : n * m ≠ 𝟘 :=
      MyNat.mul_pos n m hn hm
    exact hpos hnm
  · intro hnm
    rcases hnm with (hn | hm)
    · rw [hn]
      rw [MyNat.zero_mul m]
    · rw [hm]
      rw [MyNat.mul_zero n]

-- Proposition 2.3.5
example
    (a b c : MyNat) :
    (a * b) * c = a * (b * c) := by
  have hbase
      (b c : MyNat) :
      (𝟘 * b) * c = 𝟘 * (b * c) := by
    rw [MyNat.zero_mul b]
    rw [MyNat.zero_mul (b * c)]
    rw [MyNat.zero_mul c]
  have hind
      (a : MyNat)
      (ha : ∀ (b c : MyNat), (a * b) * c = a * (b * c))
      (b c : MyNat) :
      (a++ * b) * c = a++ * (b * c) := by
    rw [MyNat.succ_mul a b]
    rw [MyNat.mul_distrib' c (a * b) b]
    rw [MyNat.succ_mul a (b * c)]
    rw [ha b c]
  exact MyNat.induction (fun a => ∀ (b c : MyNat), (a * b) * c = a * (b * c)) hbase hind a b c

-- Proposition 2.3.9
example
    (n : MyNat)
    (q : MyNat)
    (hqpos : MyNat.is_positive q) :
    ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n = m * q + r := by
  have hall
      (n : MyNat) :
      ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n = m * q + r := by
    have hbase : ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ 𝟘 = m * q + r := by
      use 𝟘, 𝟘
      constructor
      · dsimp only [MyNat.le]
        exact MyNat.ge_refl 𝟘
      · constructor
        · dsimp only [MyNat.lt]
          dsimp only [MyNat.gt]
          constructor
          · dsimp only [MyNat.ge]
            use q
            rw [MyNat.zero_add q]
          · exact hqpos
        · rw [MyNat.zero_mul q]
          rw [MyNat.zero_add 𝟘]
    have hind
        (n : MyNat)
        (hn : ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n = m * q + r) :
        ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n++ = m * q + r := by
      rcases hn with ⟨m, r, hr, hrq, h⟩
      rcases Iff.mp (MyNat.lt_iff_eq_add r q) hrq with ⟨d, hdpos, h'⟩
      by_cases h'' : d = 𝟙
      · rw [h''] at hdpos
        use m++, 𝟘
        constructor
        · dsimp only [MyNat.le]
          exact MyNat.ge_refl 𝟘
        · constructor
          · dsimp only [MyNat.lt]
            dsimp only [MyNat.gt]
            constructor
            · dsimp only [MyNat.ge]
              use q
              rw [MyNat.zero_add q]
            · exact hqpos
          · rw [MyNat.add_zero (m++ * q)]
            rw [h''] at h'
            rw [MyNat.succ_mul m q]
            rw [h]
            rw [h']
            rw [MyNat.mul_distrib m r 𝟙]
            dsimp only [MyNat.one]
            rw [MyNat.add_succ r 𝟘]
            rw [MyNat.add_zero r]
            rw [MyNat.add_succ (m * r + m * 𝟘++) r]
      · use m, (r++)
        constructor
        · dsimp only [MyNat.le]
          dsimp only [MyNat.ge]
          use (r++)
          rw [MyNat.zero_add (r++)]
        · constructor
          · dsimp only [MyNat.lt]
            dsimp only [MyNat.gt]
            constructor
            · dsimp only [MyNat.ge]
              rcases MyNat.unique_pred_of_pos d hdpos with ⟨r', hr', huniq⟩
              use r'
              rw [MyNat.succ_add r r']
              rw [← MyNat.add_succ r r']
              rw [hr']
              exact h'
            · have hexists : ∃ (d : MyNat), MyNat.is_positive d ∧ q = (r++) + d := by
                rcases MyNat.unique_pred_of_pos d hdpos with ⟨r', hr', huniq⟩
                use r'
                rw [MyNat.succ_add r r']
                rw [← MyNat.add_succ r r']
                rw [hr']
                constructor
                · dsimp only [MyNat.is_positive]
                  by_contra hr'npos
                  rw [hr'npos] at hr'
                  exact h'' (Eq.symm hr')
                · exact h'
              have hlt : (r++) < q :=
                Iff.mpr (MyNat.lt_iff_eq_add (r++) q) hexists
              dsimp only [MyNat.lt] at hlt
              dsimp only [MyNat.gt] at hlt
              exact And.right hlt
          · rw [MyNat.add_succ (m * q) r]
            rw [h]
    exact MyNat.induction
      (fun n => ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n = m * q + r) hbase hind n
  exact hall n

section Exercises

-- Exercise 2.3.4
example
    (a b : MyNat) :
    (a + b) ^ 𝟚 = a ^ 𝟚 + 𝟚 * a * b + b ^ 𝟚 := by
  rw [MyNat.exp_two (a + b)]
  rw [MyNat.mul_distrib (a + b) a b]
  rw [MyNat.mul_distrib' a a b]
  rw [MyNat.mul_distrib' b a b]
  rw [MyNat.mul_comm b a]
  rw [MyNat.add_assoc (a * a) (a * b) (a * b + b * b)]
  rw [← MyNat.add_assoc (a * b) (a * b) (b * b)]
  rw [MyNat.exp_two a]
  rw [MyNat.exp_two b]
  dsimp only [MyNat.two]
  rw [MyNat.succ_mul 𝟙 a]
  dsimp only [MyNat.one]
  rw [MyNat.succ_mul 𝟘 a]
  rw [MyNat.zero_mul a]
  rw [MyNat.zero_add a]
  rw [← MyNat.mul_distrib' b a a]
  rw [MyNat.add_assoc (a * a) ((a + a) * b) (b * b)]

end Exercises
