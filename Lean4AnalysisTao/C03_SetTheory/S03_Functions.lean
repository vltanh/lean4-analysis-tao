import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals
import Mathlib

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

theorem MyFun.def {α β : Type} (f : MyFun α β) :
  ∀ {x : α} {y : β}, (hx : x ∈ f.domain) → y ∈ f.codomain →
    (y = f.eval x hx ↔ f.prop x y) := by
  intro x y hx hy
  have : f.eval x hx ∈ f.codomain ∧ f.prop x (f.eval x hx) := by
    have := (f.isValidProp x hx).choose_spec
    dsimp [MyFun.eval]
    constructor
    · exact this.left
    · exact this.right.left
  rcases this with ⟨hfxY, hPxfx⟩
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

def MyFun.from_fun {α β : Type} (X : MySet α) {Y : MySet β}
  (hY : ∀ (y : β), y ∈ Y) (f : α → β) :
  MyFun α β where
  domain := X
  codomain := Y
  prop := fun x y => y = f x
  isValidProp := by
    intro x hx
    use f x
    constructor
    · exact hY (f x)
    · constructor
      · dsimp only [prop]
      · intro y' hy' hP
        exact hP.symm

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

noncomputable def α := ℕ

noncomputable def β := ℕ

noncomputable def X : MySet α := MySet.Nat.set \ ⦃0⦄

noncomputable def Y : MySet β := MySet.Nat.set

noncomputable def f : MyFun α β where
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

example (f : MyFun α β) {x x' : α}
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
        · dsimp only [prop]
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
axiom MyFun.eq {α β : Type} (f g : MyFun α β) :
  f = g ↔
    f.domain = g.domain
    ∧ f.codomain = g.codomain
    ∧ ∀ {x : α} (hxf : x ∈ f.domain) (hxg : x ∈ g.domain),
      f.eval x hxf = g.eval x hxg

-- Example 3.3.10
namespace Example_3_3_10

noncomputable def X : MySet ℕ := MySet.Nat.set

noncomputable def Y : MySet ℕ := MySet.Nat.set

def _f : ℕ → ℕ := fun n => n ^ 2 + 2 * n + 1

noncomputable def f : MyFun ℕ ℕ := MyFun.from_fun X MySet.Nat.is_nat _f

def _g : ℕ → ℕ := fun n => (n + 1) ^ 2

noncomputable def g : MyFun ℕ ℕ := MyFun.from_fun X MySet.Nat.is_nat _g

example : f = g := by
  rw [MyFun.eq f g]
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
    g = empty_fun X := by
  intro X
  intro g hgdom hgcodom
  rw [MyFun.eq]
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
  MyFun α γ := sorry
  -- (by
  --   intro x hx

  --   have hfxgdom : f.eval x hx ∈ g.domain := by
  --     rcases f.isValidProp x hx with ⟨y, hy, hPxy, hy!⟩
  --     rw [← f.def hx hy] at hPxy
  --     rw [← hPxy]
  --     rw [← hfg]
  --     exact hy

  --   have : g.eval (f.eval x hx) hfxgdom ∈ g.codomain := by
  --     rcases g.isValidProp (f.eval x hx) hfxgdom with ⟨y, hy, hPxy, hy!⟩
  --     rw [← g.def hfxgdom hy] at hPxy
  --     rw [← hPxy]
  --     exact hy

  --   have : ∀ {x : α}, x ∈ f.domain

  --   let _g_f : α → γ := fun x => g.eval (f.eval x (by sorry)) (by sorry)
  --   have : _g_f x ∈ g.codomain := by sorry
  --   exact this
  -- )
notation g " ∘ " f => MyFun.comp f g

-- Example 3.3.14
namespace Example_3_3_14

def _f : ℕ → ℕ := fun n => 2 * n

def _g : ℕ → ℕ := fun n => n + 3

def _h : ℕ → ℕ := fun n => 2 * n + 3

def _k : ℕ → ℕ := fun n => 2 * n + 6

noncomputable def X : MySet ℕ := MySet.Nat.set

noncomputable def Y : MySet ℕ := MySet.Nat.set

noncomputable def Z : MySet ℕ := MySet.Nat.set

end Example_3_3_14
