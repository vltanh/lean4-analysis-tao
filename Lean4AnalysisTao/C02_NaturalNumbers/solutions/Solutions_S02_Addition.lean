import Lean4AnalysisTao.C02_NaturalNumbers.S02_Addition

/-!
Solutions for the `sorry`-stubbed theorems in `S02_Addition.lean`.

Each solution is given as an `example` block restating the goal — the
canonical names live in `S02_Addition` (currently with `sorry` placeholders),
and downstream files import that module. The statements here mirror the
`sorry` versions so the reader can compare problem and solution side-by-side.
-/

-- Lemma 2.2.2
example : ∀ (n : MyNat), n + 𝟘 = n := by
  have hbase : 𝟘 + 𝟘 = 𝟘 := by
    rw [@MyNat.zero_add 𝟘]
  have hind : ∀ {n : MyNat},
    n + 𝟘 = n → n++ + 𝟘 = n++ := by
    intro n hn
    rw [@MyNat.succ_add n 𝟘]
    rw [hn]
  exact @MyNat.induction (fun n => n + 𝟘 = n) hbase hind

-- Lemma 2.2.3
example : ∀ (n m : MyNat), n + m++ = (n + m)++ := by
  have hbase : ∀ (m : MyNat), 𝟘 + m++ = (𝟘 + m)++ := by
    intro m
    rw [@MyNat.zero_add m]
    rw [@MyNat.zero_add (m++)]
  have hind : ∀ {n : MyNat},
    (∀ (m : MyNat), n + m++ = (n + m)++) →
    ∀ (m : MyNat), n++ + m++ = (n++ + m)++ := by
    intro n hn
    intro m
    rw [@MyNat.succ_add n m]
    rw [@MyNat.succ_add n (m++)]
    rw [hn m]
  exact @MyNat.induction (fun n => ∀ (m : MyNat), n + m++ = (n + m)++) hbase hind

-- Proposition 2.2.4
example : ∀ (n m : MyNat), n + m = m + n := by
  have hbase : ∀ (m : MyNat), 𝟘 + m = m + 𝟘 := by
    intro m
    rw [@MyNat.zero_add m]
    rw [@MyNat.add_zero m]
  have hind : ∀ {n : MyNat},
    (∀ (m : MyNat), n + m = m + n) →
    ∀ (m : MyNat), n++ + m = m + n++ := by
    intro n hn
    intro m
    rw [@MyNat.succ_add n m]
    rw [@MyNat.add_succ m n]
    rw [hn m]
  exact @MyNat.induction (fun n => ∀ (m : MyNat), n + m = m + n) hbase hind

-- Proposition 2.2.5
example : ∀ (a b c : MyNat), (a + b) + c = a + (b + c) := by
  have hbase : ∀ (b c : MyNat), (𝟘 + b) + c = 𝟘 + (b + c) := by
    intro b c
    rw [@MyNat.zero_add b]
    rw [@MyNat.zero_add (b + c)]
  have hind : ∀ {a : MyNat},
    (∀ (b c : MyNat), (a + b) + c = a + (b + c)) →
    ∀ (b c : MyNat), (a++ + b) + c = a++ + (b + c) := by
    intro a ha
    intro b c
    rw [@MyNat.succ_add a b]
    rw [@MyNat.succ_add (a + b) c]
    rw [@MyNat.succ_add a (b + c)]
    rw [ha b c]
  exact @MyNat.induction (fun a => ∀ (b c : MyNat), (a + b) + c = a + (b + c)) hbase hind

-- Lemma 2.2.10
example {a : MyNat} (ha : a.is_positive) :
  ∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c) := by
  have hall : ∀ (a : MyNat), a.is_positive →
    (∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c)) := by
    have hbase : 𝟘.is_positive →
      ∃ (b : MyNat), b++ = 𝟘 ∧ (∀ (c : MyNat), c++ = 𝟘 → b = c) := by
      intro h
      dsimp only [MyNat.is_positive] at h
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
        exact @MyNat.succ_inj a c hc.symm
    exact @MyNat.induction
      (fun a => a.is_positive →
        (∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c))) hbase hind
  exact hall a ha

-- Proposition 2.2.12
-- (a)
example : ∀ (a : MyNat), a ≥ a := by
  intro a
  dsimp only [MyNat.ge]
  use 𝟘
  rw [@MyNat.add_zero a]

-- (b)
example : ∀ {a b c : MyNat}, a ≥ b → b ≥ c → a ≥ c := by
  intro a b c
  intro hab hbc
  rcases hab with ⟨d, hd⟩
  rcases hbc with ⟨e, he⟩
  dsimp only [MyNat.ge]
  use d + e
  rw [hd]
  rw [he]
  rw [@MyNat.add_assoc c e d]
  rw [@MyNat.add_comm e d]

-- (c)
example : ∀ {a b : MyNat}, a ≥ b → b ≥ a → a = b := by
  intro a b
  intro hab hba
  rcases hab with ⟨d, hd⟩
  rcases hba with ⟨e, he⟩
  have hsum : 𝟘 = e + d := by
    rw [he] at hd
    rw [← @MyNat.add_zero a] at hd
    rw [@MyNat.add_assoc a 𝟘 e] at hd
    rw [@MyNat.zero_add e] at hd
    rw [@MyNat.add_assoc a e d] at hd
    exact @MyNat.add_left_cancel a 𝟘 (e + d) hd
  have hboth : e = 𝟘 ∧ d = 𝟘 :=
    @MyNat.zero_zero_of_add_zero e d hsum.symm
  rw [hboth.right] at hd
  rw [@MyNat.add_zero b] at hd
  exact hd

-- (d)
example : ∀ {a b : MyNat} (c : MyNat), a ≥ b ↔ a + c ≥ b + c := by
  intro a b c
  constructor
  · intro hd
    rcases hd with ⟨d, hd⟩
    dsimp only [MyNat.ge]
    use d
    rw [hd]
    rw [@MyNat.add_assoc b c d]
    rw [@MyNat.add_comm c d]
    rw [@MyNat.add_assoc b d c]
  · intro hd
    rcases hd with ⟨d, hd⟩
    dsimp only [MyNat.ge]
    use d
    rw [@MyNat.add_comm a c] at hd
    rw [@MyNat.add_comm b c] at hd
    rw [@MyNat.add_assoc c b d] at hd
    exact @MyNat.add_left_cancel c a (b + d) hd

-- (e)
example : ∀ {a b : MyNat}, a < b ↔ a++ ≤ b := by
  intro a b
  constructor
  · dsimp only [MyNat.lt]
    dsimp only [MyNat.gt]
    intro hba
    rcases hba with ⟨hba, hne⟩
    dsimp only [MyNat.ge] at hba
    rcases hba with ⟨d, hd⟩
    have hdne : d ≠ 𝟘 := by
      by_contra h
      rw [h] at hd
      rw [@MyNat.add_zero a] at hd
      exact hne hd
    rcases @MyNat.unique_pred_of_pos d hdne with ⟨e, he, huniq⟩
    dsimp only [MyNat.le]
    dsimp only [MyNat.ge]
    use e
    rw [@MyNat.succ_add a e]
    rw [← @MyNat.add_succ a e]
    rw [he]
    exact hd
  · intro hasb
    dsimp only [MyNat.le] at hasb
    rcases hasb with ⟨d, hd⟩
    dsimp only [MyNat.lt]
    dsimp only [MyNat.gt]
    constructor
    · dsimp only [MyNat.ge]
      use (d++)
      rw [hd]
      rw [@MyNat.succ_add a d]
      rw [@MyNat.add_succ a d]
    · by_contra h
      rw [h] at hd
      rw [@MyNat.succ_add a d] at hd
      rw [← @MyNat.add_zero a] at hd
      rw [@MyNat.add_assoc a 𝟘 d] at hd
      rw [@MyNat.zero_add d] at hd
      rw [← @MyNat.add_succ a d] at hd
      have hdzero : 𝟘 = d++ := @MyNat.add_left_cancel a 𝟘 (d++) hd
      exact @MyNat.succ_ne_zero d hdzero.symm

-- (f)
example : ∀ {a b : MyNat}, a < b ↔ ∃ (d : MyNat), d.is_positive ∧ b = a + d := by
  intro a b
  constructor
  · intro hba
    dsimp only [MyNat.lt] at hba
    dsimp only [MyNat.gt] at hba
    rcases hba with ⟨hba, hne⟩
    dsimp only [MyNat.ge] at hba
    rcases hba with ⟨d, hd⟩
    have hdne : d ≠ 𝟘 := by
      by_contra h
      rw [h] at hd
      rw [@MyNat.add_zero a] at hd
      exact hne hd
    use d
    constructor
    · exact hdne
    · exact hd
  · intro hd
    rcases hd with ⟨d, hd, hd'⟩
    dsimp only [MyNat.lt]
    dsimp only [MyNat.gt]
    constructor
    · dsimp only [MyNat.ge]
      use d
    · by_contra h
      rw [← @MyNat.add_zero b] at hd'
      rw [h] at hd'
      have hzd : 𝟘 = d :=
        @MyNat.add_left_cancel a 𝟘 d hd'
      exact hd hzd.symm

-- Proposition 2.2.14
example {m₀ : MyNat} {P : MyNat → Prop}
  (hind : ∀ {m : MyNat}, m ≥ m₀ →
    ((∀ (m' : MyNat), m₀ ≤ m' → m' < m → P m') → P m)) :
  ∀ {m : MyNat}, m ≥ m₀ → P m := by
  let Q : MyNat → Prop :=
    fun n => (∀ (m : MyNat), m₀ ≤ m → m < n → P m)
  have hQall : ∀ (n : MyNat), Q n := by
    have hbase : Q 𝟘 := by
      dsimp only [Q]
      intro m hm hm'
      dsimp only [MyNat.lt] at hm'
      dsimp only [MyNat.gt] at hm'
      rcases hm' with ⟨hm', hne⟩
      dsimp only [MyNat.ge] at hm'
      rcases hm' with ⟨d, hd⟩
      have hpos : m + d ≠ 𝟘 :=
        @MyNat.pos_add m hne.symm d
      exact False.elim (hpos hd.symm)
    have hindQ : ∀ {n : MyNat}, Q n → Q n++ := by
      intro n hn
      dsimp only [Q]
      dsimp only [Q] at hn
      intro m hm hm'
      rcases @MyNat.order_trichotomy m n with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        exact hn m hm hlt
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        rw [heq] at hm
        dsimp only [MyNat.le] at hm
        exact hind hm hn
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        by_contra h
        dsimp only [MyNat.lt] at hm'
        dsimp only [MyNat.gt] at hm'
        rcases hm' with ⟨hm', hne⟩
        have hle : n++ ≤ m := (@MyNat.lt_iff_succ_le n m).mp hgt
        have heq : n++ = m := @MyNat.ge_antisymm (n++) m hm' hle
        exact hne heq
    exact @MyNat.induction Q hbase hindQ
  intro m hm
  exact hind hm (hQall m)

section Exercises

-- Exercise 2.2.6
example {n : MyNat} {P : MyNat → Prop}
  (hbase : P n) (hind : ∀ {m : MyNat}, P m++ → P m) :
  ∀ {m : MyNat}, m ≤ n → P m := by
  have hmain : ∀ {n : MyNat},
    P n → ∀ {m : MyNat}, m ≤ n → P m := by
    have hbase0 :
      P 𝟘 → ∀ {m : MyNat}, m ≤ 𝟘 → P m := by
      intro hbase
      intro m hm
      have hm0 : m = 𝟘 := by
        dsimp only [MyNat.le] at hm
        dsimp only [MyNat.ge] at hm
        rcases hm with ⟨d, hd⟩
        rcases @MyNat.zero_zero_of_add_zero m d hd.symm with ⟨hd, hd'⟩
        exact hd
      rw [hm0]
      exact hbase
    have hindS : ∀ {n : MyNat},
      (P n → ∀ {m : MyNat}, m ≤ n → P m) →
      (P n++ → ∀ {m : MyNat}, m ≤ n++ → P m) := by
      intro n hn
      intro hbase
      intro m hm
      rcases @MyNat.order_trichotomy m (n++) with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        have hle_n : m ≤ n := by
          have hle_succ : m++ ≤ n++ := (@MyNat.lt_iff_succ_le m (n++)).mp hlt
          dsimp only [MyNat.le] at hle_succ
          dsimp only [MyNat.ge] at hle_succ
          rcases hle_succ with ⟨d, hd⟩
          dsimp only [MyNat.le]
          dsimp only [MyNat.ge]
          use d
          rw [@MyNat.succ_add m d] at hd
          exact @MyNat.succ_inj n (m + d) hd
        exact hn (hind hbase) hle_n
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        exact hbase
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        by_contra h
        dsimp only [MyNat.gt] at hgt
        rcases hgt with ⟨hge, hne⟩
        have heq : m = n++ := @MyNat.ge_antisymm m (n++) hge hm
        exact hne heq
    exact @MyNat.induction
      (fun n => P n → ∀ {m : MyNat}, m ≤ n → P m) hbase0 hindS
  intro m
  exact hmain hbase

-- Exercise 2.2.7
example {n : MyNat} {P : MyNat → Prop}
  (hind : ∀ {m : MyNat}, P m → P m++) :
  P n → (∀ {m : MyNat}, m ≥ n → P m) := by
  intro hn
  have hmain : ∀ {m : MyNat}, m ≥ n → P m := by
    have hbase0 : 𝟘 ≥ n → P 𝟘 := by
      intro hn'
      have hn0 : n = 𝟘 := by
        dsimp only [MyNat.ge] at hn'
        rcases hn' with ⟨d, hd⟩
        rcases @MyNat.zero_zero_of_add_zero n d hd.symm with ⟨hd, hd'⟩
        exact hd
      rw [hn0] at hn
      exact hn
    have hindS : ∀ {m : MyNat}, (m ≥ n → P m) → (m++ ≥ n → P m++) := by
      intro m hm
      intro hge
      rcases @MyNat.order_trichotomy (m++) n with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        dsimp only [MyNat.lt] at hlt
        dsimp only [MyNat.gt] at hlt
        rcases hlt with ⟨hle, hne⟩
        have heq : m++ = n := @MyNat.ge_antisymm (m++) n hge hle
        rw [heq]
        exact hn
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        exact hn
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        have hge_mn : m ≥ n := by
          have hle_succ : n++ ≤ m++ := (@MyNat.lt_iff_succ_le n (m++)).mp hgt
          dsimp only [MyNat.le] at hle_succ
          dsimp only [MyNat.ge] at hle_succ
          rcases hle_succ with ⟨d, hd⟩
          dsimp only [MyNat.ge]
          use d
          rw [@MyNat.succ_add n d] at hd
          exact @MyNat.succ_inj m (n + d) hd
        have hPm : P m := hm hge_mn
        exact hind hPm
    exact @MyNat.induction (fun m => m ≥ n → P m) hbase0 hindS
  intro m hmn
  exact hmain hmn

end Exercises
