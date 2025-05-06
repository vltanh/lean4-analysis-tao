import Lean4AnalysisTao.C02_NaturalNumbers.S02_Addition

-- Definition 2.3.1
axiom MyNat.mul : MyNat → MyNat → MyNat
infixl:70 " * " => MyNat.mul

axiom MyNat.zero_mul :
  ∀ (m : MyNat), 𝟘 * m = 𝟘

axiom MyNat.succ_mul :
  ∀ (n m : MyNat), (n++) * m = n * m + m

-- Lemma 2.3.2
theorem MyNat.mul_zero :
  ∀ (n : MyNat), n * 𝟘 = 𝟘 := by
  have hbase : 𝟘 * 𝟘 = 𝟘 := by
    rw [MyNat.zero_mul 𝟘]
  have hind : ∀ {n : MyNat},
    n * 𝟘 = 𝟘 → n++ * 𝟘 = 𝟘 := by
    intro n hn
    rw [MyNat.succ_mul n 𝟘]
    rw [hn]
    rw [MyNat.add_zero 𝟘]
  exact MyNat.induction hbase hind

theorem MyNat.mul_succ :
  ∀ (n m : MyNat), n * m++ = n * m + n := by
  have hbase : ∀ (m : MyNat), 𝟘 * m++ = 𝟘 * m + 𝟘 := by
    intro m
    rw [MyNat.zero_mul m]
    rw [MyNat.zero_mul (m++)]
    rw [MyNat.zero_add 𝟘]
  have hind : ∀ {n : MyNat},
    (∀ (m : MyNat), n * m++ = n * m + n) →
    ∀ (m : MyNat), n++ * m++ = n++ * m + n++ := by
    intro n hn
    intro m
    rw [MyNat.succ_mul n m]
    rw [MyNat.succ_mul n (m++)]
    rw [hn m]
    rw [MyNat.add_assoc (n * m) n (m++)]
    rw [MyNat.add_assoc (n * m) m (n++)]
    rw [MyNat.add_succ n m]
    rw [MyNat.add_comm m (n++)]
    rw [MyNat.succ_add n m]
  exact MyNat.induction hbase hind

theorem MyNat.mul_comm :
  ∀ (n m : MyNat), n * m = m * n := by
  have hbase : ∀ (m : MyNat), 𝟘 * m = m * 𝟘 := by
    intro m
    rw [MyNat.zero_mul m]
    rw [MyNat.mul_zero m]
  have hind : ∀ {n : MyNat},
    (∀ (m : MyNat), n * m = m * n) →
    ∀ (m : MyNat), n++ * m = m * n++ := by
    intro n hn
    intro m
    rw [MyNat.succ_mul n m]
    rw [MyNat.mul_succ m n]
    rw [hn m]
  exact MyNat.induction hbase hind

-- Lemma 2.3.3
theorem MyNat.mul_pos {n m : MyNat}
  (hn : n.is_positive) (hm : m.is_positive) :
  (n * m).is_positive := by
  have : ∀ {n : MyNat}, n.is_positive →
    ∀ {m : MyNat}, m.is_positive → (n * m).is_positive := by
    have hbase : 𝟘.is_positive →
      ∀ {m : MyNat}, m.is_positive → (𝟘 * m).is_positive := by
      intro h
      intro m hm
      rw [MyNat.zero_mul m]
      exact h
    have hind : ∀ {n : MyNat},
      (n.is_positive →
        ∀ {m : MyNat}, m.is_positive → (n * m).is_positive) →
      ((n++).is_positive →
        ∀ {m : MyNat}, m.is_positive → (n++ * m).is_positive) := by
      intro n hn
      intro hnspos
      intro m hmpos
      rw [MyNat.succ_mul n m]
      exact MyNat.pos_add' hmpos (n * m)
    exact MyNat.induction hbase hind
  exact this hn hm

theorem MyNat.mul_eq_zero {n m : MyNat} :
  n * m = 𝟘 ↔ n = 𝟘 ∨ m = 𝟘 := by
  constructor
  · intro hnm
    by_contra hnm
    push_neg at hnm
    rcases hnm with ⟨hn, hm⟩
    have : n * m ≠ 𝟘 := MyNat.mul_pos hn hm
    exact this hnm
  · intro hnm
    rcases hnm with (hn | hm)
    · rw [hn]
      rw [MyNat.zero_mul m]
    · rw [hm]
      rw [MyNat.mul_zero n]

-- Proposition 2.3.4
theorem MyNat.mul_distrib (a b c : MyNat) :
  a * (b + c) = a * b + a * c := by
  have : ∀ (c : MyNat), a * (b + c) = a * b + a * c := by
    have hbase : a * (b + 𝟘) = a * b + a * 𝟘 := by
      rw [MyNat.add_zero]
      rw [MyNat.mul_zero]
      rw [MyNat.add_zero]
    have hind : ∀ {c : MyNat},
      a * (b + c) = a * b + a * c →
      a * (b + c++) = a * b + a * (c++) := by
      intro c hc
      rw [MyNat.add_succ b c]
      rw [MyNat.mul_succ a (b + c)]
      rw [MyNat.mul_succ a c]
      rw [← MyNat.add_assoc (a * b) (a * c) a]
      rw [← hc]
    exact MyNat.induction hbase hind
  exact this c

theorem MyNat.mul_distrib' (a b c : MyNat) :
  (b + c) * a = b * a + c * a := by
  rw [MyNat.mul_comm (b + c) a]
  rw [MyNat.mul_distrib a b c]
  rw [MyNat.mul_comm a b]
  rw [MyNat.mul_comm a c]

-- Proposition 2.3.5
theorem MyNat.mul_assoc :
  ∀ (a b c : MyNat), (a * b) * c = a * (b * c) := by
  have hbase : ∀ (b c : MyNat), (𝟘 * b) * c = 𝟘 * (b * c) := by
    intro b c
    rw [MyNat.zero_mul b]
    rw [MyNat.zero_mul (b * c)]
    rw [MyNat.zero_mul c]
  have hind : ∀ {a : MyNat},
    (∀ (b c : MyNat), (a * b) * c = a * (b * c)) →
    ∀ (b c : MyNat), (a++ * b) * c = a++ * (b * c) := by
    intro a ha
    intro b c
    rw [MyNat.succ_mul a b]
    rw [MyNat.mul_distrib' c (a * b) b]
    rw [MyNat.succ_mul a (b * c)]
    rw [ha b c]
  exact MyNat.induction hbase hind

-- Proposition 2.3.6
theorem MyNat.mul_lt_mul_of_pos_right {a b c : MyNat}
  (hab : a < b) (hc : c.is_positive) :
  a * c < b * c := by
  rcases MyNat.lt_iff_eq_add.mp hab with ⟨d, hd, h⟩
  have h' : b * c = a * c + d * c := by
    rw [h]
    rw [MyNat.mul_distrib']
  have hdcpos : (d * c).is_positive :=
    MyNat.mul_pos hd hc
  exact MyNat.lt_iff_eq_add.mpr ⟨d * c, hdcpos, h'⟩

-- Corollary 2.3.7
theorem MyNat.mul_cancel_of_pos (a b : MyNat) {c : MyNat}
  (hc : c ≠ 𝟘) (h : a * c = b * c):
  a = b := by
  rcases MyNat.order_trichotomy a b with (h | h | h)
  · rcases h with ⟨hlt, hne, hngt⟩
    by_contra
    have : a * c < b * c :=
      MyNat.mul_lt_mul_of_pos_right hlt hc
    exact this.right h.symm
  · rcases h with ⟨hngt, heq, hnlt⟩
    exact heq
  · rcases h with ⟨hnlt, hne, hgt⟩
    by_contra
    have : b * c < a * c :=
      MyNat.mul_lt_mul_of_pos_right hgt hc
    exact this.right h

-- Proposition 2.3.9
theorem MyNat.euclid_division (n : MyNat) {q : MyNat} (hqpos : q.is_positive) :
  ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n = m * q + r := by
  have : ∀ (n : MyNat),
    ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n = m * q + r := by
    have hbase : ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ 𝟘 = m * q + r := by
      use 𝟘, 𝟘
      constructor
      · rw [MyNat.le]
        exact ge_refl 𝟘
      · constructor
        · rw [MyNat.lt]
          rw [MyNat.gt]
          constructor
          · rw [MyNat.ge]
            use q
            rw [MyNat.zero_add]
          · exact hqpos
        · rw [MyNat.zero_mul q]
          rw [MyNat.zero_add 𝟘]
    have hind : ∀ {n : MyNat},
      (∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n = m * q + r) →
      ∃ (m r : MyNat), 𝟘 ≤ r ∧ r < q ∧ n++ = m * q + r := by
      intro n hn
      rcases hn with ⟨m, r, hr, hrq, h⟩
      rcases MyNat.lt_iff_eq_add.mp hrq with ⟨d, hdpos, h'⟩
      by_cases h'' : d = 𝟙
      · rw [h''] at hdpos
        use m++, 𝟘
        constructor
        · rw [MyNat.le]
          exact ge_refl 𝟘
        · constructor
          · rw [MyNat.lt]
            rw [MyNat.gt]
            constructor
            · rw [MyNat.ge]
              use q
              rw [MyNat.zero_add]
            · exact hqpos
          · rw [MyNat.add_zero (m++ * q)]
            rw [h''] at h'
            rw [MyNat.succ_mul m q]
            rw [h]
            rw [h']
            rw [MyNat.mul_distrib m r 𝟙]
            rw [MyNat.add_succ r 𝟘]
            rw [MyNat.add_zero r]
            rw [MyNat.add_succ (m * r + m * 𝟘++) r]
      · use m, (r++)
        constructor
        · rw [MyNat.le]
          rw [MyNat.ge]
          use (r++)
          rw [MyNat.zero_add (r++)]
        · constructor
          · rw [MyNat.lt]
            rw [MyNat.gt]
            constructor
            · rw [MyNat.ge]
              rcases MyNat.unique_pred_of_pos hdpos with ⟨r', hr', h''⟩
              use r'
              rw [MyNat.succ_add r r']
              rw [← MyNat.add_succ r r']
              rw [hr']
              exact h'
            · have : ∃ (d : MyNat), d.is_positive ∧ q = (r++) + d := by
                rcases MyNat.unique_pred_of_pos hdpos with ⟨r', hr', h'''⟩
                use r'
                rw [MyNat.succ_add r r']
                rw [← MyNat.add_succ r r']
                rw [hr']
                constructor
                · rw [MyNat.is_positive]
                  by_contra hr'npos
                  rw [hr'npos] at hr'
                  exact h'' hr'.symm
                · exact h'
              have := MyNat.lt_iff_eq_add.mpr this
              rw [MyNat.lt] at this
              rw [MyNat.gt] at this
              exact this.right
          · rw [MyNat.add_succ (m * q) r]
            rw [h]
    exact MyNat.induction hbase hind
  exact this n

-- Definition 2.3.11
axiom MyNat.exp : MyNat → MyNat → MyNat
infixr:80 " ^ " => MyNat.exp

axiom MyNat.exp_zero :
  ∀ (m : MyNat), m ^ 𝟘 = 𝟙

axiom MyNat.exp_succ :
  ∀ (m n : MyNat), m ^ (n++) = m ^ n * m

-- Example 2.3.12
theorem MyNat.exp_one (x : MyNat) : x ^ 𝟙 = x := by
  rw [MyNat.exp_succ x 𝟘]
  rw [MyNat.exp_zero x]
  rw [MyNat.succ_mul 𝟘 x]
  rw [MyNat.zero_mul x]
  rw [MyNat.zero_add x]

theorem MyNat.exp_two (x : MyNat) : x ^ 𝟚 = x * x := by
  rw [MyNat.exp_succ x 𝟙]
  rw [MyNat.exp_one x]

section Exercises

-- Exercise 2.3.4
example (a b : MyNat) :
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
  rw [MyNat.succ_mul 𝟙 a]
  rw [MyNat.succ_mul 𝟘 a]
  rw [MyNat.zero_mul a]
  rw [MyNat.zero_add a]
  rw [← MyNat.mul_distrib' b a a]
  rw [MyNat.add_assoc (a * a)]

end Exercises
