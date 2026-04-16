import Lean4AnalysisTao.C02_NaturalNumbers.S02_Addition

/-!
Solutions for the `sorry`-stubbed theorems in `S02_Addition.lean`.

Each solution is given as an `example` block restating the goal; the
canonical names live in `S02_Addition` (currently with `sorry` placeholders),
and downstream files import that module. The statements here mirror the
`sorry` versions so the reader can compare problem and solution side-by-side.
-/

-- Lemma 2.2.2
example
    (n : MyNat) :
    n + 𝟘 = n := by
  have hbase : 𝟘 + 𝟘 = 𝟘 := by
    rw [MyNat.zero_add 𝟘]
  have hind
      (n : MyNat)
      (hn : n + 𝟘 = n) :
      n++ + 𝟘 = n++ := by
    rw [MyNat.succ_add n 𝟘]
    rw [hn]
  exact MyNat.induction (fun n => n + 𝟘 = n) hbase hind n

-- Lemma 2.2.3
example
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
example
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
example
    (a b c : MyNat) :
    (a + b) + c = a + (b + c) := by
  have hbase
      (b c : MyNat) :
      (𝟘 + b) + c = 𝟘 + (b + c) := by
    rw [MyNat.zero_add b]
    rw [MyNat.zero_add (b + c)]
  have hind
      (a : MyNat)
      (ha : ∀ (b c : MyNat), (a + b) + c = a + (b + c))
      (b c : MyNat) :
      (a++ + b) + c = a++ + (b + c) := by
    rw [MyNat.succ_add a b]
    rw [MyNat.succ_add (a + b) c]
    rw [MyNat.succ_add a (b + c)]
    rw [ha b c]
  exact MyNat.induction
    (fun a => ∀ (b c : MyNat), (a + b) + c = a + (b + c)) hbase hind a b c

-- Lemma 2.2.10
example
    (a : MyNat)
    (ha : MyNat.is_positive a) :
    ∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c) := by
  have hbase
      (h : 𝟘.is_positive) :
      ∃ (b : MyNat), b++ = 𝟘 ∧ (∀ (c : MyNat), c++ = 𝟘 → b = c) := by
    dsimp only [MyNat.is_positive] at h
    exact False.elim (h rfl)
  have hind
      (a : MyNat)
      (ha : MyNat.is_positive a →
        (∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c)))
      (has : (MyNat.is_positive (a++))) :
      ∃ (b : MyNat), b++ = a++ ∧ (∀ (c : MyNat), c++ = a++ → b = c) := by
    use a
    constructor
    · exact rfl
    · intro c hc
      exact MyNat.succ_inj a c (Eq.symm hc)
  exact MyNat.induction
    (fun a => MyNat.is_positive a →
      (∃ (b : MyNat), b++ = a ∧ (∀ (c : MyNat), c++ = a → b = c))) hbase hind a ha

-- Proposition 2.2.12
-- (a)
example
    (a : MyNat) :
    a ≥ a := by
  dsimp only [MyNat.ge]
  use 𝟘
  rw [MyNat.add_zero a]

-- (b)
example
    (a b c : MyNat)
    (hab : a ≥ b)
    (hbc : b ≥ c) :
    a ≥ c := by
  rcases hab with ⟨d, hd⟩
  rcases hbc with ⟨e, he⟩
  dsimp only [MyNat.ge]
  use d + e
  rw [hd]
  rw [he]
  rw [MyNat.add_assoc c e d]
  rw [MyNat.add_comm e d]

-- (c)
example
    (a b : MyNat)
    (hab : a ≥ b)
    (hba : b ≥ a) :
    a = b := by
  rcases hab with ⟨d, hd⟩
  rcases hba with ⟨e, he⟩
  have hsum : 𝟘 = e + d := by
    rw [he] at hd
    rw [← MyNat.add_zero a] at hd
    rw [MyNat.add_assoc a 𝟘 e] at hd
    rw [MyNat.zero_add e] at hd
    rw [MyNat.add_assoc a e d] at hd
    exact MyNat.add_left_cancel a 𝟘 (e + d) hd
  have hboth : e = 𝟘 ∧ d = 𝟘 :=
    MyNat.zero_zero_of_add_zero e d (Eq.symm hsum)
  rw [And.right hboth] at hd
  rw [MyNat.add_zero b] at hd
  exact hd

-- (d)
example
    (a b c : MyNat) :
    a ≥ b ↔ a + c ≥ b + c := by
  constructor
  · intro hd
    rcases hd with ⟨d, hd⟩
    dsimp only [MyNat.ge]
    use d
    rw [hd]
    rw [MyNat.add_assoc b c d]
    rw [MyNat.add_comm c d]
    rw [MyNat.add_assoc b d c]
  · intro hd
    rcases hd with ⟨d, hd⟩
    dsimp only [MyNat.ge]
    use d
    rw [MyNat.add_comm a c] at hd
    rw [MyNat.add_comm b c] at hd
    rw [MyNat.add_assoc c b d] at hd
    exact MyNat.add_left_cancel c a (b + d) hd

-- (e)
example
    (a b : MyNat) :
    a < b ↔ a++ ≤ b := by
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
      rw [MyNat.add_zero a] at hd
      exact hne hd
    rcases MyNat.unique_pred_of_pos d hdne with ⟨e, he, huniq⟩
    dsimp only [MyNat.le]
    dsimp only [MyNat.ge]
    use e
    rw [MyNat.succ_add a e]
    rw [← MyNat.add_succ a e]
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
      rw [MyNat.succ_add a d]
      rw [MyNat.add_succ a d]
    · by_contra h
      rw [h] at hd
      rw [MyNat.succ_add a d] at hd
      rw [← MyNat.add_zero a] at hd
      rw [MyNat.add_assoc a 𝟘 d] at hd
      rw [MyNat.zero_add d] at hd
      rw [← MyNat.add_succ a d] at hd
      have hdzero : 𝟘 = d++ :=
        MyNat.add_left_cancel a 𝟘 (d++) hd
      exact MyNat.succ_ne_zero d (Eq.symm hdzero)

-- (f)
example
    (a b : MyNat) :
    a < b ↔ ∃ (d : MyNat), MyNat.is_positive d ∧ b = a + d := by
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
      rw [MyNat.add_zero a] at hd
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
      rw [← MyNat.add_zero b] at hd'
      rw [h] at hd'
      have hzd : 𝟘 = d :=
        MyNat.add_left_cancel a 𝟘 d hd'
      exact hd (Eq.symm hzd)

-- Proposition 2.2.14
example
    (m₀ : MyNat)
    (P : MyNat → Prop)
    (hind : ∀ (m : MyNat), m ≥ m₀ →
    ((∀ (m' : MyNat), m₀ ≤ m' → m' < m → P m') → P m))
    (m : MyNat)
    (hm : m ≥ m₀) :
    P m := by
  let Q : MyNat → Prop :=
    fun n => (∀ (m : MyNat), m₀ ≤ m → m < n → P m)
  have hQall
      (n : MyNat) :
      Q n := by
    have hbase : Q 𝟘 := by
      dsimp only [Q]
      intro m hm hm'
      dsimp only [MyNat.lt] at hm'
      dsimp only [MyNat.gt] at hm'
      rcases hm' with ⟨hm', hne⟩
      dsimp only [MyNat.ge] at hm'
      rcases hm' with ⟨d, hd⟩
      have hpos : m + d ≠ 𝟘 :=
        MyNat.pos_add m (Ne.symm hne) d
      exact False.elim (hpos (Eq.symm hd))
    have hindQ
        (n : MyNat)
        (hn : Q n) :
        Q n++ := by
      dsimp only [Q]
      dsimp only [Q] at hn
      intro m hm hm'
      rcases MyNat.order_trichotomy m n with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        exact hn m hm hlt
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        rw [heq] at hm
        dsimp only [MyNat.le] at hm
        exact hind n hm hn
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        by_contra h
        dsimp only [MyNat.lt] at hm'
        dsimp only [MyNat.gt] at hm'
        rcases hm' with ⟨hm', hne⟩
        have hle : n++ ≤ m :=
          Iff.mp (MyNat.lt_iff_succ_le n m) hgt
        have heq : n++ = m :=
          MyNat.ge_antisymm (n++) m hm' hle
        exact hne heq
    exact MyNat.induction Q hbase hindQ n
  exact hind m hm (hQall m)

section Exercises

-- Exercise 2.2.6
example
    (n : MyNat)
    (P : MyNat → Prop)
    (hbase : P n)
    (hind : ∀ (m : MyNat), P m++ → P m)
    (m : MyNat)
    (hmn : m ≤ n) :
    P m := by
  have hmain
      (n : MyNat)
      (hpn : P n)
      (m : MyNat)
      (hm : m ≤ n) :
      P m := by
    have hbase0
        (hbase : P 𝟘)
        (m : MyNat)
        (hm : m ≤ 𝟘) :
        P m := by
      have hm0 : m = 𝟘 := by
        dsimp only [MyNat.le] at hm
        dsimp only [MyNat.ge] at hm
        rcases hm with ⟨d, hd⟩
        rcases MyNat.zero_zero_of_add_zero m d (Eq.symm hd) with ⟨hd, hd'⟩
        exact hd
      rw [hm0]
      exact hbase
    have hindS
        (n : MyNat)
        (hn : P n → ∀ (m : MyNat), m ≤ n → P m)
        (hbase : P n++)
        (m : MyNat)
        (hm : m ≤ n++) :
        P m := by
      rcases MyNat.order_trichotomy m (n++) with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        have hle_n : m ≤ n := by
          have hle_succ : m++ ≤ n++ :=
            Iff.mp (MyNat.lt_iff_succ_le m (n++)) hlt
          dsimp only [MyNat.le] at hle_succ
          dsimp only [MyNat.ge] at hle_succ
          rcases hle_succ with ⟨d, hd⟩
          dsimp only [MyNat.le]
          dsimp only [MyNat.ge]
          use d
          rw [MyNat.succ_add m d] at hd
          exact MyNat.succ_inj n (m + d) hd
        exact hn (hind n hbase) m hle_n
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        exact hbase
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        by_contra h
        dsimp only [MyNat.gt] at hgt
        rcases hgt with ⟨hge, hne⟩
        have heq : m = n++ :=
          MyNat.ge_antisymm m (n++) hge hm
        exact hne heq
    exact MyNat.induction
      (fun n => P n → ∀ (m : MyNat), m ≤ n → P m) hbase0 hindS n hpn m hm
  exact hmain n hbase m hmn

-- Exercise 2.2.7
example
    (n : MyNat)
    (P : MyNat → Prop)
    (hind : ∀ (m : MyNat), P m → P m++)
    (hn : P n)
    (m : MyNat)
    (hmn : m ≥ n) :
    P m := by
  have hmain
      (m : MyNat)
      (hmn : m ≥ n) :
      P m := by
    have hbase0
        (hn' : 𝟘 ≥ n) :
        P 𝟘 := by
      have hn0 : n = 𝟘 := by
        dsimp only [MyNat.ge] at hn'
        rcases hn' with ⟨d, hd⟩
        rcases MyNat.zero_zero_of_add_zero n d (Eq.symm hd) with ⟨hd, hd'⟩
        exact hd
      rw [hn0] at hn
      exact hn
    have hindS
        (m : MyNat)
        (hm : m ≥ n → P m)
        (hge : m++ ≥ n) :
        P m++ := by
      rcases MyNat.order_trichotomy (m++) n with (h1 | h2 | h3)
      · rcases h1 with ⟨hlt, hneq, hngt⟩
        dsimp only [MyNat.lt] at hlt
        dsimp only [MyNat.gt] at hlt
        rcases hlt with ⟨hle, hne⟩
        have heq : m++ = n :=
          MyNat.ge_antisymm (m++) n hge hle
        rw [heq]
        exact hn
      · rcases h2 with ⟨hnlt, heq, hngt⟩
        rw [heq]
        exact hn
      · rcases h3 with ⟨hnlt, hneq, hgt⟩
        have hge_mn : m ≥ n := by
          have hle_succ : n++ ≤ m++ :=
            Iff.mp (MyNat.lt_iff_succ_le n (m++)) hgt
          dsimp only [MyNat.le] at hle_succ
          dsimp only [MyNat.ge] at hle_succ
          rcases hle_succ with ⟨d, hd⟩
          dsimp only [MyNat.ge]
          use d
          rw [MyNat.succ_add n d] at hd
          exact MyNat.succ_inj m (n + d) hd
        have hPm : P m :=
          hm hge_mn
        exact hind m hPm
    exact MyNat.induction (fun m => m ≥ n → P m) hbase0 hindS m hmn
  exact hmain m hmn

end Exercises
