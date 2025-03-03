import Mathlib.Data.Nat.Defs

import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals

-- Definition 3.3.1
structure MyFun (α β : Type) where
  domain : MySet α
  codomain : MySet β
  prop : α → β → Prop
  isValidProp : ∀ (x : α), x ∈ domain →
    ∃ (y : β), y ∈ codomain ∧ prop x y ∧
      (∀ (y' : β), y' ∈ codomain → prop x y' → y = y')

noncomputable def MyFun.eval (f : MyFun α β) :
  (x : α) → x ∈ f.domain → β :=
  fun x hx => (f.isValidProp x hx).choose

theorem MyFun.eval_codomain (f : MyFun α β) {x : α} (hx : x ∈ f.domain) :
  f.eval x hx ∈ f.codomain := by
  exact (f.isValidProp x hx).choose_spec.left

theorem MyFun.def {α β : Type} (f : MyFun α β) :
  ∀ {x : α} {y : β}, (hx : x ∈ f.domain) → y ∈ f.codomain →
    (y = f.eval x hx ↔ f.prop x y) := by
  intro x y hx hy
  have hfxY : f.eval x hx ∈ f.codomain :=
    MyFun.eval_codomain f hx
  have hPxfx : f.prop x (f.eval x hx) := by
    exact (f.isValidProp x hx).choose_spec.right.left
  constructor
  · intro hyfx
    rw [hyfx]
    exact hPxfx
  · intro hPxy
    rcases f.isValidProp x hx with ⟨y', hy', hPxy', hy'!⟩
    have hy'x := hy'! y hy hPxy
    have hy'fx := hy'! (f.eval x hx) hfxY hPxfx
    rw [← hy'fx]
    exact hy'x.symm

def MyFun.from_fun {α β : Type} {X : MySet α} {Y : MySet β}
  {f : (x : α) → x ∈ X → β} (h : ∀ {x : α} (hx : x ∈ X), f x hx ∈ Y) :
  MyFun α β where
  domain := X
  codomain := Y
  prop := fun x y => by
    by_cases hx : x ∈ X
    · exact y = f x hx
    · exact False
  isValidProp := by
    intro x hx
    use f x hx
    constructor
    · exact h hx
    · constructor
      · dsimp only [prop]
        rw [dif_pos hx]
      · intro y' hy' hP
        rw [dif_pos hx] at hP
        exact hP.symm

theorem MyFun.from_fun.eval {α β : Type} {X : MySet α} {Y : MySet β}
  {f : (x : α) → x ∈ X → β} (h : ∀ {x : α} (hx : x ∈ X), f x hx ∈ Y)
  {x : α} (hx : x ∈ X) : (MyFun.from_fun h).eval x hx = f x hx := by
  have : f x hx = (MyFun.from_fun h).eval x hx := by
    rw [MyFun.def (MyFun.from_fun h) hx (h hx)]
    dsimp only [MyFun.from_fun]
    rw [dif_pos hx]
  exact this.symm

-- Example 3.3.3
namespace Example_3_3_3

namespace Example_3_3_3_a

def α := ℕ

def β := ℕ

noncomputable def X : MySet α := MySet.Nat.set

noncomputable def Y : MySet β := MySet.Nat.set

noncomputable def f : MyFun α β where
  domain := X
  codomain := Y
  prop := fun x y => y = Nat.succ x
  isValidProp := by
    intro x hx
    use Nat.succ x
    constructor
    · dsimp only [Y]
      exact MySet.Nat.is_nat (Nat.succ x)
    · constructor
      · dsimp only [MyFun.prop]
      · intro y' hy' h
        exact h.symm

example : ∀ {x : α} (hx : x ∈ X),
  f.eval x hx = Nat.succ x := by
  intro x hx
  have hy : Nat.succ x ∈ Y := by
    rw [Y]
    exact MySet.Nat.is_nat (Nat.succ x)
  have : f.prop x (Nat.succ x) := by
    dsimp [f]
  have := (f.def hx hy).mpr this
  exact this.symm

end Example_3_3_3_a

namespace Example_3_3_3_b

noncomputable def X : MySet ℕ := MySet.Nat.set \ ⦃0⦄

noncomputable def Y : MySet ℕ := MySet.Nat.set

noncomputable def f : MyFun ℕ ℕ where
  domain := X
  codomain := Y
  prop := fun x y => Nat.succ y = x
  isValidProp := by
    intro x hx
    have hxpos : x ≠ (0 : ℕ) := by
      dsimp only [X] at hx
      rw [MySet.diff] at hx
      rw [MySet.mem_spec] at hx
      rw [MySet.mem_singleton] at hx
      intro h
      exact hx.right h
    rcases Nat.exists_eq_succ_of_ne_zero hxpos with ⟨y, hy⟩
    use y
    constructor
    · dsimp only [Y]
      exact MySet.Nat.is_nat y
    · constructor
      · dsimp only [MyFun.prop]
        exact hy.symm
      · intro y' hy' hP
        rw [hy] at hP
        exact Nat.succ_inj.mp hP.symm

lemma aux : 4 ∈ X := by
  rw [X]
  rw [MySet.diff]
  rw [MySet.mem_spec]
  constructor
  · exact MySet.Nat.is_nat 4
  · intro h
    rw [MySet.mem_singleton] at h
    have : 4 ≠ 0 :=
      Nat.succ_ne_zero 3
    exact False.elim (this h)

example : f.eval (4 : ℕ) aux = (3 : ℕ) := by
  have h : 3 ∈ Y := by
    dsimp only [Y]
    exact MySet.Nat.is_nat 3
  have : f.prop (4 : ℕ) (3 : ℕ) := by
    dsimp only [f]
  rw [← f.def aux h] at this
  exact this.symm

end Example_3_3_3_b

end Example_3_3_3

theorem MyFun.substitute (f : MyFun α β) {x x' : α}
  (hx : x ∈ f.domain) (hx' : x' ∈ f.domain) :
  x = x' → f.eval x hx = f.eval x' hx' := by
  -- sorry
  intro hxx'
  rcases f.isValidProp x hx with ⟨y, hy, hPxy, hy!⟩
  rcases f.isValidProp x' hx' with ⟨y', hy', hPx'y', hy'!⟩
  have hPxy' : f.prop x y' := by
      rw [hxx']
      exact hPx'y'
  have hyy' : y = y' := hy! y' hy' hPxy'
  have hy' : y' = f.eval x hx := by
    exact (f.def hx hy').mpr hPxy'
  have hy : y = f.eval x' hx' := by
    have hPx'y : f.prop x' y := by
      rw [← hxx']
      exact hPxy
    have := f.def hx' hy
    exact this.mpr hPx'y
  rw [← hy]
  rw [← hy']
  exact hyy'.symm

-- Example 3.3.5
example : ∃ (α β : Type) (f : MyFun α β) (x x' : α)
  (hx : x ∈ f.domain) (hx' : x' ∈ f.domain),
  ¬ ((x ≠ x') → (f.eval x hx ≠ f.eval x' hx')) := by
  let α := ℕ
  let β := ℕ
  let f : MyFun α β := {
    domain := MySet.Nat.set
    codomain := MySet.Nat.set
    prop := fun x y => y = 7
    isValidProp := by
      intro x hx
      use 7
      constructor
      · exact MySet.Nat.is_nat 7
      · constructor
        · dsimp only [MyFun.prop]
        · intro y' hy' hP
          exact hP.symm
  }
  let x := 0
  let x' := 1
  let hx : x ∈ f.domain := by
    dsimp only [x]
    dsimp only [f]
    exact MySet.Nat.is_nat 0
  let hx' : x' ∈ f.domain := by
    dsimp [x']
    dsimp only [f]
    exact MySet.Nat.is_nat 1
  use α, β
  use f
  use x, x', hx, hx'
  push_neg
  constructor
  · dsimp [x]
    dsimp [x']
    exact Nat.zero_ne_one
  · have : ∀ {x : α} (hx : x ∈ f.domain), f.eval x hx = 7 := by
      intro x hx
      have h7 : 7 ∈ f.codomain := by
        dsimp only [f]
        exact MySet.Nat.is_nat 7
      have : f.prop x 7 := by
        dsimp only [f]
      rw [← f.def hx h7] at this
      exact this.symm
    rw [this hx]
    rw [this hx']

-- Definition 3.3.8
def MyFun.eq {α β : Type} (f g : MyFun α β) :=
  f.domain = g.domain
  ∧ f.codomain = g.codomain
  ∧ ∀ {x : α} (hxf : x ∈ f.domain) (hxg : x ∈ g.domain),
    f.eval x hxf = g.eval x hxg
notation f " ≃ " g => MyFun.eq f g

-- Example 3.3.10
namespace Example_3_3_10

noncomputable def X : MySet ℕ := MySet.Nat.set

noncomputable def Y : MySet ℕ := MySet.Nat.set

lemma aux : ∀ (f : ℕ → ℕ) {x : ℕ}, x ∈ X → f x ∈ Y := by
  intro f x hx
  dsimp only [Y]
  exact MySet.Nat.is_nat (f x)

def _f : ℕ → ℕ := fun n => n ^ 2 + 2 * n + 1

noncomputable def f : MyFun ℕ ℕ := MyFun.from_fun (aux _f)

def _g : ℕ → ℕ := fun n => (n + 1) ^ 2

noncomputable def g : MyFun ℕ ℕ := MyFun.from_fun (aux _g)

example : f ≃ g := by
  dsimp only [MyFun.eq]
  constructor
  · rfl
  · constructor
    · rfl
    · intro x hxf hxg
      rcases f.isValidProp x hxf with ⟨y, hy, hPxy, hy!⟩
      rcases g.isValidProp x hxf with ⟨y', hy', hQxy', hy'!⟩
      have : f.prop x y' := by
        dsimp only [f]
        dsimp only [g] at hQxy'
        dsimp only [MyFun.from_fun]
        dsimp only [_f]
        dsimp only [MyFun.from_fun] at hQxy'
        dsimp only [_g] at hQxy'
        dsimp only [f] at hxf
        dsimp only [MyFun.from_fun] at hxf
        rw [dif_pos hxf]
        rw [dif_pos hxf] at hQxy'
        rw [hQxy']
        rw [Nat.pow_two]
        rw [Nat.mul_add]
        rw [Nat.add_mul]
        rw [Nat.add_mul]
        rw [← Nat.add_assoc]
        rw [Nat.one_mul]
        rw [Nat.mul_one]
        rw [Nat.mul_one]
        rw [Nat.two_mul]
        rw [← Nat.add_assoc]
        rw [Nat.pow_two]
      have := hy! y' hy' this
      have hy : y = f.eval x hxf := by
        rw [← f.def hxf hy] at hPxy
        exact hPxy
      have hy' : y' = g.eval x hxf := by
        rw [← g.def hxf hy'] at hQxy'
        exact hQxy'
      rw [← hy]
      rw [← hy']
      exact this

end Example_3_3_10

-- Example 3.3.11
noncomputable def empty_fun (X : MySet β) : MyFun α β where
  domain := ∅
  codomain := X
  prop := fun x y => True
  isValidProp := by
    intro x hx
    exact False.elim (MySet.not_mem_empty hx)

example : ∀ (X : MySet β),
  ∀ (g : MyFun α β), g.domain = ∅ → g.codomain = X →
    g ≃ empty_fun X := by
  intro X
  intro g hgdom hgcodom
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [empty_fun]
    rw [hgdom]
  · constructor
    · dsimp only [empty_fun]
      rw [hgcodom]
    · intro x hxf hxg
      rw [hgdom] at hxf
      exact False.elim (MySet.not_mem_empty hxf)

-- Definition 3.3.13
noncomputable def MyFun.comp {α β γ : Type}
  (f : MyFun α β) (g : MyFun β γ) (hfg : f.codomain = g.domain) :
  MyFun α γ := by
  have aux : ∀ {x : α} (hx : x ∈ f.domain), f.eval x hx ∈ g.domain := by
    intro x hx
    rw [← hfg]
    exact f.eval_codomain hx
  let gf : (x : α) → x ∈ f.domain → γ :=
    fun x h => g.eval (f.eval x h) (aux h)
  have aux' : ∀ {x : α} (hx : x ∈ f.domain), gf x hx ∈ g.codomain := by
    intro x hx
    exact g.eval_codomain (aux hx)
  exact MyFun.from_fun aux'

theorem MyFun.comp.eval {α β γ : Type}
  (f : MyFun α β) (g : MyFun β γ) (hfg : f.codomain = g.domain)
  {x : α} (hxf : x ∈ f.domain) (hfxg : f.eval x hxf ∈ g.domain)
  (hfgx : x ∈ (f.comp g hfg).domain) :
  (f.comp g hfg).eval x hfgx = g.eval (f.eval x hxf) hfxg := by
  dsimp only [MyFun.comp]
  rw [MyFun.from_fun.eval]

theorem MyFun.comp.eval.domain {α β γ : Type}
  (f : MyFun α β) (g : MyFun β γ) (hfg : f.codomain = g.domain) :
  (f.comp g hfg).domain = f.domain := by
  dsimp only [MyFun.comp]
  dsimp only [MyFun.from_fun]

theorem MyFun.comp.eval.codomain {α β γ : Type}
  (f : MyFun α β) (g : MyFun β γ) (hfg : f.codomain = g.domain) :
  (f.comp g hfg).codomain = g.codomain := by
  dsimp only [MyFun.comp]
  dsimp only [MyFun.from_fun]

-- Example 3.3.14
namespace Example_3_3_14

def _f : ℕ → ℕ := fun n => 2 * n

def _g : ℕ → ℕ := fun n => n + 3

noncomputable def X : MySet ℕ := MySet.Nat.set

noncomputable def Y : MySet ℕ := MySet.Nat.set

noncomputable def Z : MySet ℕ := MySet.Nat.set

lemma aux : ∀ (f : ℕ → ℕ) (X : MySet ℕ)
  {x : ℕ}, x ∈ X → f x ∈ Y := by
  intro f X x hx
  exact MySet.Nat.is_nat (f x)

noncomputable def f : MyFun ℕ ℕ := MyFun.from_fun (aux _f X)

noncomputable def g : MyFun ℕ ℕ := MyFun.from_fun (aux _g Y)

noncomputable def gf : MyFun ℕ ℕ := MyFun.comp f g rfl

example (x : ℕ) : gf.eval x (MySet.Nat.is_nat x) = 2 * x + 3 := by
  dsimp only [gf]
  dsimp only [MyFun.comp]
  rw [MyFun.from_fun.eval]
  dsimp only [g]
  rw [MyFun.from_fun.eval]
  dsimp only [f]
  rw [MyFun.from_fun.eval]
  dsimp only [_f]
  dsimp only [_g]

noncomputable def fg : MyFun ℕ ℕ := MyFun.comp g f rfl

example (x : ℕ) : fg.eval x (MySet.Nat.is_nat x) = 2 * x + 6 := by
  dsimp only [fg]
  dsimp only [MyFun.comp]
  rw [MyFun.from_fun.eval]
  dsimp only [f]
  rw [MyFun.from_fun.eval]
  dsimp only [g]
  rw [MyFun.from_fun.eval]
  dsimp only [_f]
  dsimp only [_g]
  rw [Nat.mul_add]

end Example_3_3_14

-- Lemma 3.3.15
theorem MyFun.comp_assoc {α β γ δ : Type}
  (f : MyFun γ δ) (g : MyFun β γ) (h : MyFun α β)
  (hgh : h.codomain = g.domain) (hfg : g.codomain = f.domain) :
  (h.comp g hgh).comp f hfg ≃ h.comp (g.comp f hfg) hgh := by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
  · constructor
    · dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
    · intro x hxh hxg
      dsimp only [MyFun.comp] at hxh
      dsimp only [MyFun.from_fun] at hxh

      have hf_gh : (h.comp g hgh).codomain = f.domain := by
        rw [MyFun.comp.eval.codomain]
        exact hfg
      have hghxf : (h.comp g hgh).eval x hxh ∈ f.domain := by
        rw [← hfg]
        rw [← MyFun.comp.eval.codomain h g hgh]
        exact MyFun.eval_codomain (h.comp g hgh) hxh
      rw [MyFun.comp.eval (h.comp g hgh) f hf_gh hxh hghxf]

      have hhxg : h.eval x hxh ∈ g.domain := by
        rw [← hgh]
        exact MyFun.eval_codomain h hxh
      have hg_hxf : g.eval (h.eval x hxh) hhxg ∈ f.domain := by
        rw [← hfg]
        exact MyFun.eval_codomain g hhxg
      have : (h.comp g hgh).eval x hxh = g.eval (h.eval x hxh) hhxg := by
        rw [MyFun.comp.eval h g hgh hxh hhxg hxh]
      rw [MyFun.substitute f hghxf hg_hxf this]

      have hfg_h : h.codomain = (g.comp f hfg).domain := by
        rw [MyFun.comp.eval.domain]
        exact hgh
      have hhxfg: h.eval x hxh ∈ (g.comp f hfg).domain := by
        rw [MyFun.comp.eval.domain]
        rw [← hgh]
        exact MyFun.eval_codomain h hxh
      rw [MyFun.comp.eval h (g.comp f hfg) hfg_h hxh hhxfg]

      rw [MyFun.comp.eval g f hfg hhxg hg_hxf]

-- Definition 3.3.17
def MyFun.isInjective {α β : Type} (f : MyFun α β) :=
  ∀ {x x' : α} (hx : x ∈ f.domain) (hx' : x' ∈ f.domain),
    x ≠ x' → f.eval x hx ≠ f.eval x' hx'

def MyFun.isInjective' {α β : Type} (f : MyFun α β) :=
  ∀ {x x' : α} (hx : x ∈ f.domain) (hx' : x' ∈ f.domain),
    f.eval x hx = f.eval x' hx' → x = x'

theorem MyFun.isInjective_iff {α β : Type} (f : MyFun α β) :
  f.isInjective ↔ f.isInjective' := by
  constructor
  · intro h
    dsimp only [MyFun.isInjective] at h
    dsimp only [MyFun.isInjective']
    intro x x' hx hx' hff'
    by_contra h'
    exact h hx hx' h' hff'
  · intro h
    dsimp only [MyFun.isInjective'] at h
    dsimp only [MyFun.isInjective]
    intro x x' hx hx' hxx' hff'
    exact hxx' (h hx hx' hff')

-- Example 3.3.18
namespace Example_3_3_18

def _f : ℕ → ℕ := fun n => n ^ 2

noncomputable def X : MySet ℕ := MySet.Nat.set

noncomputable def Y : MySet ℕ := MySet.Nat.set

lemma aux : ∀ (f : ℕ → ℕ) (X : MySet ℕ)
  {x : ℕ}, x ∈ X → f x ∈ Y := by
  intro f X x hx
  exact MySet.Nat.is_nat (f x)

noncomputable def f : MyFun ℕ ℕ :=
  MyFun.from_fun (aux _f X)

example : f.isInjective := by
  intro x x' hx hx' hxx'
  dsimp only [f]
  rw [MyFun.from_fun.eval]
  rw [MyFun.from_fun.eval]
  dsimp only [_f]
  intro hx2x'2
  rw [Nat.lt_or_gt] at hxx'
  rcases hxx' with (hlt | hgt)
  · rw [← Nat.mul_self_lt_mul_self_iff] at hlt
    rw [← Nat.pow_two] at hlt
    rw [← Nat.pow_two] at hlt
    rw [Nat.lt_iff_le_and_ne] at hlt
    exact hlt.right hx2x'2
  · rw [← Nat.mul_self_lt_mul_self_iff] at hgt
    rw [← Nat.pow_two] at hgt
    rw [← Nat.pow_two] at hgt
    rw [Nat.lt_iff_le_and_ne] at hgt
    exact hgt.right hx2x'2.symm

end Example_3_3_18

-- Definition 3.3.20
def MyFun.isSurjective {α β : Type} (f : MyFun α β) :=
  ∀ (y : β), y ∈ f.codomain →
    ∃ (x : α) (hx : x ∈ f.domain), f.eval x hx = y

-- Example 3.3.21
namespace Example_3_3_21

noncomputable def X : MySet ℕ := MySet.Nat.set

def _f : ℕ → ℕ := fun n => n ^ 2

def P : ℕ → ℕ → Prop := fun x y => y = x ^ 2

lemma hP : ∀ (x : ℕ), x ∈ X →
  (∃ (y : ℕ), P x y ∧ (∀ (z : ℕ), P x z → z = y)) := by
  intro x hx
  use _f x
  constructor
  · dsimp only [P]
    dsimp only [_f]
  · intro z hP
    dsimp only [P] at hP
    dsimp only [_f]
    exact hP

noncomputable def Y : MySet ℕ := ⦃ MySet.Nat.set ← hP ⦄

lemma aux : ∀ {x : ℕ}, x ∈ X → _f x ∈ Y := by
  intro x hx
  dsimp only [Y]
  rw [MySet.mem_replace]
  use x
  constructor
  · dsimp only [P]
    exact MySet.Nat.is_nat x
  · dsimp only [P]
    dsimp only [_f]

noncomputable def f : MyFun ℕ ℕ := MyFun.from_fun aux

example : f.isSurjective := by
  dsimp only [MyFun.isSurjective]
  intro y hy
  dsimp only [f] at hy
  dsimp only [MyFun.from_fun] at hy
  dsimp only [Y] at hy
  rw [MySet.mem_replace] at hy
  rcases hy with ⟨x, hx, hPxy⟩
  dsimp only [P] at hPxy
  use x, hx
  dsimp only [f]
  rw [MyFun.from_fun.eval]
  dsimp only [_f]
  exact hPxy.symm

end Example_3_3_21

-- Definition 3.3.23
def MyFun.isBijective {α β : Type} (f : MyFun α β) :=
  f.isInjective ∧ f.isSurjective

-- Example 3.3.25
namespace Example_3_3_25

noncomputable def X : MySet ℕ := MySet.Nat.set

noncomputable def Y : MySet ℕ := MySet.Nat.set \ ⦃0⦄

def _f : ℕ → ℕ := fun n => n.succ

lemma aux : ∀ {x : ℕ}, x ∈ X → _f x ∈ Y := by
  intro x hx
  dsimp only [Y]
  dsimp only [_f]
  rw [MySet.diff]
  rw [MySet.mem_spec]
  constructor
  · exact MySet.Nat.is_nat (x.succ)
  · intro h
    rw [MySet.mem_singleton] at h
    exact Nat.succ_ne_zero x h

noncomputable def f : MyFun ℕ ℕ := MyFun.from_fun aux

example : f.isBijective := by
  dsimp only [MyFun.isBijective]
  constructor
  · dsimp only [MyFun.isInjective]
    intro x x' hx hx' hxx'
    dsimp only [f]
    rw [MyFun.from_fun.eval]
    rw [MyFun.from_fun.eval]
    dsimp only [_f]
    exact Nat.succ_ne_succ.mpr hxx'
  · dsimp only [MyFun.isSurjective]
    intro y hy
    dsimp only [f] at hy
    dsimp only [MyFun.from_fun] at hy
    dsimp only [Y] at hy
    rw [MySet.diff] at hy
    rw [MySet.mem_spec] at hy
    rcases hy with ⟨hy, hny⟩
    rw [MySet.mem_singleton] at hny
    rcases Nat.exists_eq_succ_of_ne_zero hny with ⟨x, hx⟩
    use x, MySet.Nat.is_nat x
    dsimp only [f]
    rw [MyFun.from_fun.eval]
    dsimp only [_f]
    exact hx.symm

end Example_3_3_25

-- Remark 3.3.27
theorem MyFun.exists_unique_of_bijective {α β : Type} (f : MyFun α β)
  (h : f.isBijective) :
  ∀ (y : β), y ∈ f.codomain →
    ∃ (x : α) (hx : x ∈ f.domain), f.eval x hx = y ∧
      ∀ (x' : α) (hx' : x' ∈ f.domain), f.eval x' hx' = y → x = x' := by
  intro y hy
  dsimp only [MyFun.isBijective] at h
  rcases h with ⟨hinj, hsurj⟩
  dsimp only [MyFun.isSurjective] at hsurj
  rcases hsurj y hy with ⟨x, hx, hxy⟩
  use x, hx, hxy
  intro x' hx' hxy'
  rw [MyFun.isInjective_iff] at hinj
  dsimp only [MyFun.isInjective'] at hinj
  rw [← hxy'] at hxy
  exact hinj hx hx' hxy

def MyFun.inv {α β : Type} (f : MyFun α β) (h : f.isBijective) :
  MyFun β α := by
  let X : MySet β := f.codomain
  let Y : MySet α := f.domain
  let finv (y : β) (hy : y ∈ X) : α :=
    (MyFun.exists_unique_of_bijective f h y hy).choose
  let aux : ∀ {y : β} (hy : y ∈ X), finv y hy ∈ Y := by
    intro y hy
    dsimp only [Y]
    dsimp only [finv]
    rcases (MyFun.exists_unique_of_bijective f h y hy).choose_spec with ⟨hx, h⟩
    exact hx
  exact MyFun.from_fun aux
