import Lean4AnalysisTao.Util

axiom MyNat : Type

-- Axiom 2.1
axiom MyNat.zero : MyNat
notation "𝟘" => MyNat.zero

-- Axiom 2.2
axiom MyNat.succ : MyNat → MyNat
postfix:max "++" => MyNat.succ

-- Definition 2.1.3
noncomputable def MyNat.one : MyNat := 𝟘++
notation "𝟙" => MyNat.one

noncomputable def MyNat.two : MyNat := 𝟙++
notation "𝟚" => MyNat.two

noncomputable def MyNat.three : MyNat := 𝟚++
notation "𝟛" => MyNat.three

noncomputable def MyNat.four : MyNat := 𝟛++
notation "𝟜" => MyNat.four

noncomputable def MyNat.five : MyNat := 𝟜++
notation "𝟝" => MyNat.five

noncomputable def MyNat.six : MyNat := 𝟝++
notation "𝟞" => MyNat.six

noncomputable def MyNat.seven : MyNat := 𝟞++
notation "𝟟" => MyNat.seven

noncomputable def MyNat.eight : MyNat := 𝟟++
notation "𝟠" => MyNat.eight

noncomputable def MyNat.nine : MyNat := 𝟠++
notation "𝟡" => MyNat.nine

noncomputable def MyNat.ten : MyNat := 𝟡++
notation "𝟙𝟘" => MyNat.ten

-- Example 2.1.4

-- Example 2.1.5
namespace Example_2_1_5

axiom Wrap : Type

axiom Wrap.zero : Wrap
axiom Wrap.one : Wrap
axiom Wrap.two : Wrap
axiom Wrap.three : Wrap

axiom Wrap.succ : Wrap → Wrap

axiom Wrap.succ_zero : Wrap.succ Wrap.zero = Wrap.one
axiom Wrap.succ_one : Wrap.succ Wrap.one = Wrap.two
axiom Wrap.succ_two : Wrap.succ Wrap.two = Wrap.three
axiom Wrap.succ_three : Wrap.succ Wrap.three = Wrap.zero

example : Wrap.succ Wrap.three = Wrap.zero := Wrap.succ_three

end Example_2_1_5

-- Axiom 2.3
axiom MyNat.succ_ne_zero
    (n : MyNat) :
    n++ ≠ 𝟘

-- Proposition 2.1.6
theorem Proposition_2_1_6 :
    𝟜 ≠ 𝟘 :=
  MyNat.succ_ne_zero 𝟛

-- Example 2.1.7
namespace Example_2_1_7

axiom Ceil : Type

axiom Ceil.zero : Ceil
axiom Ceil.one : Ceil
axiom Ceil.two : Ceil
axiom Ceil.three : Ceil
axiom Ceil.four : Ceil

axiom Ceil.succ : Ceil → Ceil

axiom Ceil.succ_zero : Ceil.succ Ceil.zero = Ceil.one
axiom Ceil.succ_one : Ceil.succ Ceil.one = Ceil.two
axiom Ceil.succ_two : Ceil.succ Ceil.two = Ceil.three
axiom Ceil.succ_three : Ceil.succ Ceil.three = Ceil.four
axiom Ceil.succ_four : Ceil.succ Ceil.four = Ceil.four

end Example_2_1_7

-- Axiom 2.4
axiom MyNat.succ_inj
    (n m : MyNat)
    (h : n++ = m++) :
    n = m

theorem MyNat.succ_inj'
    (n m : MyNat)
    (h : n ≠ m) :
    n++ ≠ m++ := by
  by_contra hcontra
  exact h (MyNat.succ_inj n m hcontra)

-- Proposition 2.1.8
example : 𝟞 ≠ 𝟚 := by
  by_contra h62
  dsimp only [MyNat.six] at h62
  dsimp only [MyNat.two] at h62
  have h51 : 𝟝 = 𝟙 := MyNat.succ_inj 𝟝 𝟙 h62
  dsimp only [MyNat.five] at h51
  dsimp only [MyNat.one] at h51
  have h40 : 𝟜 = 𝟘 := MyNat.succ_inj 𝟜 𝟘 h51
  exact Proposition_2_1_6 h40

-- Axiom 2.5
axiom MyNat.induction
    (P : MyNat → Prop)
    (hbase : P 𝟘)
    (hind : ∀ (n : MyNat), P n → P n++) :
    ∀ (n : MyNat), P n

-- Proposition 2.1.16
theorem Proposition_2_1_16
    (f : MyNat → MyNat → MyNat)
    (c : MyNat) :
    ∃ (a : MyNat → MyNat),
      a 𝟘 = c
      ∧ (∀ (n : MyNat), a (n++) = f n (a n))
      ∧ (∀ (a' : MyNat → MyNat),
          a' 𝟘 = c → (∀ (n : MyNat), a' (n++) = f n (a' n)) →
          ∀ (n : MyNat), a' n = a n) := by
  let G : MyNat → MyNat → Prop :=
    fun n v =>
      ∀ (R : MyNat → MyNat → Prop),
        R 𝟘 c → (∀ (m w : MyNat), R m w → R (m++) (f m w)) → R n v
  have hexuniq :
      ∀ (n : MyNat), ∃ (v : MyNat), G n v ∧ (∀ (w : MyNat), G n w → w = v) := by
    refine MyNat.induction
      (fun n => ∃ (v : MyNat), G n v ∧ (∀ (w : MyNat), G n w → w = v)) ?_ ?_
    · refine Exists.intro c (And.intro ?_ ?_)
      · intro R hR0 _hRs
        exact hR0
      · intro w hGw
        let R : MyNat → MyNat → Prop :=
          fun m v => m = 𝟘 → v = c
        have hR0 : R 𝟘 c :=
          fun _ => rfl
        have hRs : ∀ (m w : MyNat), R m w → R (m++) (f m w) := by
          intro m _w _hRmw hsucc
          exact False.elim (MyNat.succ_ne_zero m hsucc)
        exact hGw R hR0 hRs rfl
    · intro n ihn
      rcases ihn with ⟨v, hGv, huniq⟩
      refine Exists.intro (f n v) (And.intro ?_ ?_)
      · intro R hR0 hRs
        exact hRs n v (hGv R hR0 hRs)
      · intro w hGw
        let R : MyNat → MyNat → Prop :=
          fun m u => G m u ∧ (m = n++ → u = f n v)
        have hR0 : R 𝟘 c := by
          refine And.intro ?_ ?_
          · intro R' hR0' _hRs'
            exact hR0'
          · intro h0eq
            exact False.elim (MyNat.succ_ne_zero n (Eq.symm h0eq))
        have hRs : ∀ (m u : MyNat), R m u → R (m++) (f m u) := by
          intro m u hRmu
          rcases hRmu with ⟨hGmu, _⟩
          refine And.intro ?_ ?_
          · intro R' hR0' hRs'
            exact hRs' m u (hGmu R' hR0' hRs')
          · intro hmsucc
            have hmn : m = n := MyNat.succ_inj m n hmsucc
            rw [hmn] at hGmu
            have hun : u = v := huniq u hGmu
            rw [hmn]
            rw [hun]
        exact And.right (hGw R hR0 hRs) rfl
  let a : MyNat → MyNat :=
    fun n => MyClassical.choose (fun v => G n v ∧ (∀ (w : MyNat), G n w → w = v))
      (hexuniq n)
  have ha_spec :
      ∀ (n : MyNat), G n (a n) ∧ (∀ (w : MyNat), G n w → w = a n) :=
    fun n =>
      MyClassical.choose_spec
        (fun v => G n v ∧ (∀ (w : MyNat), G n w → w = v))
        (hexuniq n)
  refine Exists.intro a (And.intro ?_ (And.intro ?_ ?_))
  · exact Eq.symm ((And.right (ha_spec 𝟘)) c (fun _ hR0 _ => hR0))
  · intro n
    have hGsucc : G (n++) (f n (a n)) :=
      fun R hR0 hRs => hRs n (a n) (And.left (ha_spec n) R hR0 hRs)
    exact Eq.symm ((And.right (ha_spec (n++))) (f n (a n)) hGsucc)
  · intro a' ha'0 ha'succ n
    have hGa'n : ∀ (m : MyNat), G m (a' m) := by
      refine MyNat.induction (fun m => G m (a' m)) ?_ ?_
      · intro R hR0 _hRs
        rw [ha'0]
        exact hR0
      · intro m ihm R hR0 hRs
        rw [ha'succ m]
        exact hRs m (a' m) (ihm R hR0 hRs)
    exact (And.right (ha_spec n)) (a' n) (hGa'n n)
