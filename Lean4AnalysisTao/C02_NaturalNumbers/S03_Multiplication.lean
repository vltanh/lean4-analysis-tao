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
  sorry

theorem MyNat.mul_succ :
  ∀ (n m : MyNat), n * m++ = n * m + n := by
  sorry

theorem MyNat.mul_comm :
  ∀ (n m : MyNat), n * m = m * n := by
  sorry

-- Lemma 2.3.3
theorem MyNat.mul_pos {n m : MyNat}
  (hn : n.is_positive) (hm : m.is_positive) :
  (n * m).is_positive := by
  sorry

theorem MyNat.mul_eq_zero {n m : MyNat} :
  n * m = 𝟘 ↔ n = 𝟘 ∨ m = 𝟘 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

end Exercises
