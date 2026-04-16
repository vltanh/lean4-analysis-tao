import Lean4AnalysisTao.Util
import Lean4AnalysisTao.C02_NaturalNumbers.S03_Multiplication
import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals

-- Definition 3.3.1
structure MyFun (α β : Type) where
  domain : MySet α
  codomain : MySet β
  prop : α → β → Prop
  isValidProp : ∀ (x : α), x ∈ domain →
    ∃ (y : β), y ∈ codomain ∧ prop x y ∧
      (∀ (y' : β), y' ∈ codomain → prop x y' → y = y')

noncomputable def MyFun.eval
    (f : MyFun α β) :
    (x : α) → x ∈ MyFun.domain f → β :=
  fun x hx => MyClassical.choose
    (fun y => y ∈ MyFun.codomain f ∧ MyFun.prop f x y ∧
      (∀ (y' : β), y' ∈ MyFun.codomain f → MyFun.prop f x y' → y = y'))
    ((MyFun.isValidProp f) x hx)

theorem MyFun.eval_codomain
    (f : MyFun α β)
    (x : α)
    (hx : x ∈ MyFun.domain f) :
    MyFun.eval f x hx ∈ MyFun.codomain f := by
  exact And.left (MyClassical.choose_spec
    (fun y => y ∈ MyFun.codomain f ∧ MyFun.prop f x y ∧
      (∀ (y' : β), y' ∈ MyFun.codomain f → MyFun.prop f x y' → y = y'))
    ((MyFun.isValidProp f) x hx))

theorem MyFun.def
    {α β : Type}
    (f : MyFun α β)
    (x : α)
    (y : β)
    (hx : x ∈ MyFun.domain f)
    (hy : y ∈ MyFun.codomain f) :
    y = MyFun.eval f x hx ↔ MyFun.prop f x y := by
  have hfxY :
      MyFun.eval f x hx ∈ MyFun.codomain f :=
    MyFun.eval_codomain f x hx
  have hPxfx :
      MyFun.prop f x (MyFun.eval f x hx) := by
    exact And.left (And.right (MyClassical.choose_spec
      (fun y => y ∈ MyFun.codomain f ∧ MyFun.prop f x y ∧
        (∀ (y' : β), y' ∈ MyFun.codomain f → MyFun.prop f x y' → y = y'))
      ((MyFun.isValidProp f) x hx)))
  constructor
  · intro hyfx
    rw [hyfx]
    exact hPxfx
  · intro hPxy
    rcases (MyFun.isValidProp f) x hx with ⟨y', hy', hPxy', hy'!⟩
    have hy'x : y' = y :=
      hy'! y hy hPxy
    have hy'fx : y' = MyFun.eval f x hx :=
      hy'! (MyFun.eval f x hx) hfxY hPxfx
    rw [← hy'fx]
    exact Eq.symm hy'x

def MyFun.from_fun
    {α β : Type}
    (X : MySet α)
    (Y : MySet β)
    (f : (x : α) → x ∈ X → β)
    (h : ∀ (x : α) (hx : x ∈ X), f x hx ∈ Y) :
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
    · exact h x hx
    · constructor
      · dsimp only [prop]
        rw [dif_pos hx]
      · intro y' hy' hP
        rw [dif_pos hx] at hP
        exact Eq.symm hP

theorem MyFun.from_fun.eval
    {α β : Type}
    (X : MySet α)
    (Y : MySet β)
    (f : (x : α) → x ∈ X → β)
    (h : ∀ (x : α) (hx : x ∈ X), f x hx ∈ Y)
    (x : α)
    (hx : x ∈ X) :
    (MyFun.eval (MyFun.from_fun X Y f h)) x hx = f x hx := by
  have heq :
      f x hx = (MyFun.eval (MyFun.from_fun X Y f h)) x hx := by
    rw [MyFun.def (MyFun.from_fun X Y f h) x (f x hx) hx (h x hx)]
    dsimp only [MyFun.from_fun]
    rw [dif_pos hx]
  exact Eq.symm heq

-- Example 3.3.3
namespace Example_3_3_3

namespace Example_3_3_3_a

noncomputable def X : MySet MyNat :=
  MySet.Nat.set

noncomputable def Y : MySet MyNat :=
  MySet.Nat.set

noncomputable def f : MyFun MyNat MyNat where
  domain := X
  codomain := Y
  prop := fun x y => y = (x++)
  isValidProp := by
    intro x _hx
    use (x++)
    constructor
    · dsimp only [Y]
      exact MySet.Nat.is_nat (x++)
    · constructor
      · dsimp only [MyFun.prop]
      · intro y' _hy' h
        exact Eq.symm h

example
    (x : MyNat)
    (hx : x ∈ X) :
    MyFun.eval f x hx = x++ := by
  have hy :
      x++ ∈ Y := by
    dsimp only [Y]
    exact MySet.Nat.is_nat (x++)
  have hPx :
      MyFun.prop f x (x++) := by
    dsimp only [f]
  have hfx :
      x++ = MyFun.eval f x hx :=
    Iff.mpr (MyFun.def f x (x++) hx hy) hPx
  exact Eq.symm hfx

end Example_3_3_3_a

namespace Example_3_3_3_b

noncomputable def X : MySet MyNat :=
  MySet.Nat.set \ ⦃(0 : MyNat)⦄

noncomputable def Y : MySet MyNat :=
  MySet.Nat.set

noncomputable def f : MyFun MyNat MyNat where
  domain := X
  codomain := Y
  prop := fun x y => y++ = x
  isValidProp := by
    intro x hx
    dsimp only [X] at hx
    rw [MySet.diff] at hx
    rw [MySet.mem_spec MySet.Nat.set
      (fun z => ¬ (z ∈ (⦃(0 : MyNat)⦄ : MySet MyNat))) x] at hx
    rw [MySet.mem_singleton (0 : MyNat) x] at hx
    have hxpos :
        (MyNat.is_positive (x : MyNat)) :=
      fun heq => And.right hx heq
    rcases MyNat.unique_pred_of_pos x hxpos with ⟨y, hy, huniq⟩
    use y
    constructor
    · dsimp only [Y]
      exact MySet.Nat.is_nat y
    · constructor
      · exact hy
      · intro y' _hy' hP
        exact huniq y' hP

theorem aux :
    (4 : MyNat) ∈ X := by
  dsimp only [X]
  rw [MySet.diff]
  rw [MySet.mem_spec MySet.Nat.set
    (fun z => ¬ (z ∈ (⦃(0 : MyNat)⦄ : MySet MyNat))) (4 : MyNat)]
  constructor
  · exact MySet.Nat.is_nat (4 : MyNat)
  · rw [MySet.mem_singleton (0 : MyNat) (4 : MyNat)]
    intro h4eq0
    exact MyNat.succ_ne_zero (3 : MyNat) h4eq0

example :
    MyFun.eval f (4 : MyNat) aux = (3 : MyNat) := by
  have h :
      (3 : MyNat) ∈ Y := by
    dsimp only [Y]
    exact MySet.Nat.is_nat (3 : MyNat)
  have hprop :
      MyFun.prop f (4 : MyNat) (3 : MyNat) := by
    dsimp only [f]
    rfl
  rw [← MyFun.def f (4 : MyNat) (3 : MyNat) aux h] at hprop
  exact Eq.symm hprop

end Example_3_3_3_b

end Example_3_3_3

theorem MyFun.substitute
    (f : MyFun α β)
    (x x' : α)
    (hx : x ∈ MyFun.domain f)
    (hx' : x' ∈ MyFun.domain f)
    (hxx' : x = x') :
    MyFun.eval f x hx = MyFun.eval f x' hx' := by
  sorry

-- Example 3.3.5
example : ∃ (α β : Type) (f : MyFun α β) (x x' : α)
  (hx : x ∈ MyFun.domain f) (hx' : x' ∈ MyFun.domain f),
  ¬ ((x ≠ x') → (MyFun.eval f x hx ≠ MyFun.eval f x' hx')) := by
  let α :=
    MyNat
  let β :=
    MyNat
  let f :
      MyFun α β :=
    {
    domain := MySet.Nat.set
    codomain := MySet.Nat.set
    prop := fun _x y => y = (7 : MyNat)
    isValidProp := by
      intro x _hx
      use (7 : MyNat)
      constructor
      · exact MySet.Nat.is_nat (7 : MyNat)
      · constructor
        · dsimp only [MyFun.prop]
        · intro y' _hy' hP
          exact Eq.symm hP
  }
  let x :
      α :=
    (0 : MyNat)
  let x' : α :=
    (1 : MyNat)
  let hx :
      x ∈ MyFun.domain f := by
    dsimp only [x]
    dsimp only [f]
    exact MySet.Nat.is_nat (0 : MyNat)
  let hx' : x' ∈ MyFun.domain f := by
    dsimp only [x']
    dsimp only [f]
    exact MySet.Nat.is_nat (1 : MyNat)
  use α, β
  use f
  use x, x', hx, hx'
  intro himp
  have hne :
      x ≠ x' := by
    dsimp only [x]
    dsimp only [x']
    have hne' : (0 : MyNat) ≠ (1 : MyNat) :=
      fun heq => MyNat.succ_ne_zero (0 : MyNat) (Eq.symm heq)
    exact hne'
  have hall
      (a : α)
      (ha : a ∈ MyFun.domain f) :
      MyFun.eval f a ha = (7 : MyNat) := by
    have h7 :
        (7 : MyNat) ∈ MyFun.codomain f := by
      dsimp only [f]
      exact MySet.Nat.is_nat (7 : MyNat)
    have hPa :
        MyFun.prop f a (7 : MyNat) := by
      dsimp only [f]
    rw [← MyFun.def f a (7 : MyNat) ha h7] at hPa
    exact Eq.symm hPa
  have heval :
      MyFun.eval f x hx = MyFun.eval f x' hx' := by
    rw [hall x hx]
    rw [hall x' hx']
  exact himp hne heval

-- Definition 3.3.8
def MyFun.eq
    {α β : Type}
    (f g : MyFun α β) :=
  MyFun.domain f = MyFun.domain g
  ∧ MyFun.codomain f = MyFun.codomain g
  ∧ ∀ (x : α) (hxf : x ∈ MyFun.domain f) (hxg : x ∈ MyFun.domain g),
    MyFun.eval f x hxf = MyFun.eval g x hxg
notation f " ≃ " g => MyFun.eq f g

-- Example 3.3.10
namespace Example_3_3_10

noncomputable def X : MySet MyNat :=
  MySet.Nat.set

noncomputable def Y : MySet MyNat :=
  MySet.Nat.set

theorem aux
    (f : MyNat → MyNat)
    (x : MyNat)
    (hx : x ∈ X) :
    f x ∈ Y := by
  dsimp only [Y]
  exact MySet.Nat.is_nat (f x)

private noncomputable def _f_fn : (x : MyNat) → x ∈ X → MyNat :=
  fun n _h => n ^ 𝟚 + (𝟚 : MyNat) * n + (1 : MyNat)

private theorem _f_mem
    (x : MyNat)
    (hx : x ∈ X) :
    _f_fn x hx ∈ Y :=
  MySet.Nat.is_nat (_f_fn x hx)

noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun X Y _f_fn _f_mem

private noncomputable def _g_fn : (x : MyNat) → x ∈ X → MyNat :=
  fun n _h => (n + (1 : MyNat)) ^ 𝟚

private theorem _g_mem
    (x : MyNat)
    (hx : x ∈ X) :
    _g_fn x hx ∈ Y :=
  MySet.Nat.is_nat (_g_fn x hx)

noncomputable def g : MyFun MyNat MyNat :=
  MyFun.from_fun X Y _g_fn _g_mem

private theorem sq_eq
    (n : MyNat) :
    n ^ 𝟚 + (𝟚 : MyNat) * n + (1 : MyNat) = (n + (1 : MyNat)) ^ 𝟚 := by
  have hone :
      (1 : MyNat) = 𝟘++ :=
    rfl
  rw [hone]
  rw [MyNat.add_succ n 𝟘]
  rw [MyNat.add_zero n]
  rw [MyNat.exp_two n]
  rw [MyNat.exp_two (n++)]
  rw [MyNat.succ_mul (𝟘++) n]
  rw [MyNat.succ_mul 𝟘 n]
  rw [MyNat.zero_mul n]
  rw [MyNat.zero_add n]
  rw [MyNat.succ_mul n (n++)]
  rw [MyNat.mul_succ n n]
  rw [MyNat.add_succ (n * n + (n + n)) 𝟘]
  rw [MyNat.add_zero (n * n + (n + n))]
  rw [MyNat.add_succ (n * n + n) n]
  rw [MyNat.add_assoc (n * n) n n]

example :
    f ≃ g := by
  dsimp only [MyFun.eq]
  refine And.intro rfl (And.intro rfl ?_)
  intro x hxf hxg
  have hfeval :
      MyFun.eval f x hxf = _f_fn x hxf := by
    dsimp only [f]
    rw [MyFun.from_fun.eval X Y _f_fn _f_mem x hxf]
  have hgeval :
      MyFun.eval g x hxg = _g_fn x hxg := by
    dsimp only [g]
    rw [MyFun.from_fun.eval X Y _g_fn _g_mem x hxg]
  rw [hfeval, hgeval]
  dsimp only [_f_fn]
  dsimp only [_g_fn]
  exact sq_eq x

end Example_3_3_10

-- Example 3.3.11
noncomputable def empty_fun
    (X : MySet β) :
    MyFun α β where
  domain := ∅
  codomain := X
  prop := fun x y => True
  isValidProp := by
    intro x hx
    exact False.elim (MySet.not_mem_empty x hx)

example
    (X : MySet β)
    (g : MyFun α β)
    (hgdom : MyFun.domain g = ∅)
    (hgcodom : MyFun.codomain g = X) :
    g ≃ empty_fun X := by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [empty_fun]
    rw [hgdom]
  · constructor
    · dsimp only [empty_fun]
      rw [hgcodom]
    · intro x hxf hxg
      rw [hgdom] at hxf
      exact False.elim (MySet.not_mem_empty x hxf)

-- Definition 3.3.13
noncomputable def MyFun.comp
    {α β γ : Type}
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g) :
    MyFun α γ := by
  have aux
      (x : α)
      (hx : x ∈ MyFun.domain f) :
      MyFun.eval f x hx ∈ MyFun.domain g := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hx
  let gf :
      (x : α) → x ∈ MyFun.domain f → γ :=
    fun x h => MyFun.eval g (MyFun.eval f x h) (aux x h)
  have aux'
      (x : α)
      (hx : x ∈ MyFun.domain f) :
      gf x hx ∈ MyFun.codomain g :=
    MyFun.eval_codomain g (MyFun.eval f x hx) (aux x hx)
  exact MyFun.from_fun (MyFun.domain f) (MyFun.codomain g) gf aux'

theorem MyFun.comp.eval
    {α β γ : Type}
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (x : α)
    (hxf : x ∈ MyFun.domain f)
    (hfxg : MyFun.eval f x hxf ∈ MyFun.domain g)
    (hfgx : x ∈ (MyFun.domain (MyFun.comp f g hfg))) :
    (MyFun.eval (MyFun.comp f g hfg)) x hfgx = MyFun.eval g (MyFun.eval f x hxf) hfxg := by
  dsimp only [MyFun.comp]
  rw [MyFun.from_fun.eval (X := MyFun.domain f) (Y := MyFun.codomain g) (x := x) (hx := hxf)]

theorem MyFun.comp.eval.domain
    {α β γ : Type}
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g) :
    (MyFun.domain (MyFun.comp f g hfg)) = MyFun.domain f := by
  dsimp only [MyFun.comp]
  dsimp only [MyFun.from_fun]

theorem MyFun.comp.eval.codomain
    {α β γ : Type}
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g) :
    (MyFun.codomain (MyFun.comp f g hfg)) = MyFun.codomain g := by
  dsimp only [MyFun.comp]
  dsimp only [MyFun.from_fun]

-- Example 3.3.14
namespace Example_3_3_14

noncomputable def _f : MyNat → MyNat :=
  fun n => (2 : MyNat) * n

noncomputable def _g : MyNat → MyNat :=
  fun n => n + (3 : MyNat)

noncomputable def X : MySet MyNat :=
  MySet.Nat.set

noncomputable def Y : MySet MyNat :=
  MySet.Nat.set

noncomputable def Z : MySet MyNat :=
  MySet.Nat.set

theorem aux
    (f : MyNat → MyNat)
    (X : MySet MyNat)
    (x : MyNat)
    (hx : x ∈ X) :
    f x ∈ Y := by
  dsimp only [Y]
  exact MySet.Nat.is_nat (f x)

noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun X Y (fun x _ => _f x) (fun x hx => aux _f X x hx)

noncomputable def g : MyFun MyNat MyNat :=
  MyFun.from_fun Y Z (fun x _ => _g x) (fun x hx => aux _g Y x hx)

noncomputable def gf : MyFun MyNat MyNat :=
  MyFun.comp f g rfl

example
    (x : MyNat) :
    MyFun.eval gf x (MySet.Nat.is_nat x) = (2 : MyNat) * x + (3 : MyNat) := by
  dsimp only [gf]
  have hfxg :
      MyFun.eval f x (MySet.Nat.is_nat x) ∈ MyFun.domain g :=
    MyFun.eval_codomain f x (MySet.Nat.is_nat x)
  rw [MyFun.comp.eval f g rfl x (MySet.Nat.is_nat x) hfxg (MySet.Nat.is_nat x)]
  dsimp only [g]
  rw [MyFun.from_fun.eval Y Z (fun x _ => _g x) (fun x hx => aux _g Y x hx)
    (MyFun.eval f x (MySet.Nat.is_nat x)) hfxg]
  dsimp only [f]
  rw [MyFun.from_fun.eval X Y (fun x _ => _f x) (fun x hx => aux _f X x hx)
    x (MySet.Nat.is_nat x)]
  dsimp only [_f]
  dsimp only [_g]

noncomputable def fg : MyFun MyNat MyNat :=
  MyFun.comp g f rfl

example
    (x : MyNat) :
    MyFun.eval fg x (MySet.Nat.is_nat x) = (2 : MyNat) * x + (6 : MyNat) := by
  dsimp only [fg]
  have hgxf :
      MyFun.eval g x (MySet.Nat.is_nat x) ∈ MyFun.domain f :=
    MyFun.eval_codomain g x (MySet.Nat.is_nat x)
  rw [MyFun.comp.eval g f rfl x (MySet.Nat.is_nat x) hgxf (MySet.Nat.is_nat x)]
  dsimp only [f]
  rw [MyFun.from_fun.eval X Y (fun x _ => _f x) (fun x hx => aux _f X x hx)
    (MyFun.eval g x (MySet.Nat.is_nat x)) hgxf]
  dsimp only [g]
  rw [MyFun.from_fun.eval Y Z (fun x _ => _g x) (fun x hx => aux _g Y x hx)
    x (MySet.Nat.is_nat x)]
  dsimp only [_f]
  dsimp only [_g]
  rw [MyNat.mul_distrib (2 : MyNat) x (3 : MyNat)]
  have h23 :
      (2 : MyNat) * (3 : MyNat) = (6 : MyNat) := by
    have h2 :
        (2 : MyNat) = (𝟘++)++ :=
      rfl
    have h3 :
        (3 : MyNat) = ((𝟘++)++)++ :=
      rfl
    have h6 :
        (6 : MyNat) = ((((((𝟘++)++)++)++)++)++) :=
      rfl
    rw [h2]
    rw [h3]
    rw [h6]
    rw [MyNat.mul_succ ((𝟘++)++) ((𝟘++)++)]
    rw [MyNat.mul_succ ((𝟘++)++) (𝟘++)]
    rw [MyNat.mul_succ ((𝟘++)++) 𝟘]
    rw [MyNat.mul_zero ((𝟘++)++)]
    rw [MyNat.zero_add ((𝟘++)++)]
    rw [MyNat.add_succ (((𝟘++)++) + ((𝟘++)++)) (𝟘++)]
    rw [MyNat.add_succ (((𝟘++)++) + ((𝟘++)++)) 𝟘]
    rw [MyNat.add_zero (((𝟘++)++) + ((𝟘++)++))]
    rw [MyNat.add_succ ((𝟘++)++) (𝟘++)]
    rw [MyNat.add_succ ((𝟘++)++) 𝟘]
    rw [MyNat.add_zero ((𝟘++)++)]
  rw [h23]

end Example_3_3_14

-- Lemma 3.3.15
theorem MyFun.comp_assoc
    {α β γ δ : Type}
    (f : MyFun γ δ)
    (g : MyFun β γ)
    (h : MyFun α β)
    (hgh : MyFun.codomain h = MyFun.domain g)
    (hfg : MyFun.codomain g = MyFun.domain f) :
    (MyFun.comp (MyFun.comp h g hgh)) f hfg ≃ MyFun.comp h (MyFun.comp g f hfg) hgh := by
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

      have hf_gh :
          (MyFun.codomain (MyFun.comp h g hgh)) = MyFun.domain f := by
        rw [MyFun.comp.eval.codomain h g hgh]
        exact hfg
      have hghxf :
          (MyFun.eval (MyFun.comp h g hgh)) x hxh ∈ MyFun.domain f := by
        rw [← hfg]
        rw [← MyFun.comp.eval.codomain h g hgh]
        exact MyFun.eval_codomain (MyFun.comp h g hgh) x hxh
      rw [MyFun.comp.eval (MyFun.comp h g hgh) f hf_gh x hxh hghxf hxh]

      have hhxg :
          MyFun.eval h x hxh ∈ MyFun.domain g := by
        rw [← hgh]
        exact MyFun.eval_codomain h x hxh
      have hg_hxf :
          MyFun.eval g (MyFun.eval h x hxh) hhxg ∈ MyFun.domain f := by
        rw [← hfg]
        exact MyFun.eval_codomain g (MyFun.eval h x hxh) hhxg
      have hcompeval :
          (MyFun.eval (MyFun.comp h g hgh)) x hxh = MyFun.eval g (MyFun.eval h x hxh) hhxg := by
        rw [MyFun.comp.eval h g hgh x hxh hhxg hxh]
      rw [MyFun.substitute f
        ((MyFun.eval (MyFun.comp h g hgh)) x hxh) (MyFun.eval g (MyFun.eval h x hxh) hhxg) hghxf hg_hxf hcompeval]

      have hfg_h :
          MyFun.codomain h = (MyFun.domain (MyFun.comp g f hfg)) := by
        rw [MyFun.comp.eval.domain g f hfg]
        exact hgh
      have hhxfg :
          MyFun.eval h x hxh ∈ (MyFun.domain (MyFun.comp g f hfg)) := by
        rw [MyFun.comp.eval.domain g f hfg]
        rw [← hgh]
        exact MyFun.eval_codomain h x hxh
      rw [MyFun.comp.eval h (MyFun.comp g f hfg) hfg_h x hxh hhxfg hxh]

      rw [MyFun.comp.eval g f hfg (MyFun.eval h x hxh) hhxg hg_hxf hhxg]

-- Definition 3.3.17
def MyFun.isInjective
    {α β : Type}
    (f : MyFun α β) :=
  ∀ (x x' : α) (hx : x ∈ MyFun.domain f) (hx' : x' ∈ MyFun.domain f),
    x ≠ x' → MyFun.eval f x hx ≠ MyFun.eval f x' hx'

def MyFun.isInjective'
    {α β : Type}
    (f : MyFun α β) :=
  ∀ (x x' : α) (hx : x ∈ MyFun.domain f) (hx' : x' ∈ MyFun.domain f),
    MyFun.eval f x hx = MyFun.eval f x' hx' → x = x'

theorem MyFun.isInjective_iff
    {α β : Type}
    (f : MyFun α β) :
    MyFun.isInjective f ↔ (MyFun.isInjective' f) := by
  constructor
  · intro h
    dsimp only [MyFun.isInjective] at h
    dsimp only [MyFun.isInjective']
    intro x x' hx hx' hff'
    by_contra h'
    exact h x x' hx hx' h' hff'
  · intro h
    dsimp only [MyFun.isInjective'] at h
    dsimp only [MyFun.isInjective]
    intro x x' hx hx' hxx' hff'
    exact hxx' (h x x' hx hx' hff')

-- Example 3.3.18
namespace Example_3_3_18

private noncomputable def _f_fn : (x : MyNat) → x ∈ MySet.Nat.set → MyNat :=
  fun n _h => n ^ (𝟚 : MyNat)

private theorem _f_mem
    (x : MyNat)
    (hx : x ∈ MySet.Nat.set) :
    _f_fn x hx ∈ MySet.Nat.set :=
  MySet.Nat.is_nat (_f_fn x hx)

noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun MySet.Nat.set MySet.Nat.set _f_fn _f_mem

example :
    MyFun.isInjective f := by
  -- TODO: port; needs strict monotonicity of squaring on MyNat.
  sorry

end Example_3_3_18

-- Definition 3.3.20
def MyFun.isSurjective
    {α β : Type}
    (f : MyFun α β) :=
  ∀ (y : β), y ∈ MyFun.codomain f →
    ∃ (x : α) (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y

-- Example 3.3.21
namespace Example_3_3_21

private def P : MyNat → MyNat → Prop :=
  fun x y => y = x ^ (𝟚 : MyNat)

private theorem hP_unique
    (x : MyNat)
    (_hx : x ∈ MySet.Nat.set) :
    ∃ (y : MyNat), P x y ∧ (∀ (z : MyNat), P x z → z = y) := by
  have huniq
      (z : MyNat)
      (hz : P x z) :
      z = x ^ (𝟚 : MyNat) := by
    dsimp only [P] at hz
    exact hz
  exact Exists.intro (x ^ (𝟚 : MyNat)) (And.intro rfl huniq)

noncomputable def Y : MySet MyNat :=
  ⦃ MySet.Nat.set ← hP_unique ⦄

private theorem _f_mem
    (x : MyNat)
    (hx : x ∈ MySet.Nat.set) :
    x ^ (𝟚 : MyNat) ∈ Y := by
  dsimp only [Y]
  rw [MySet.mem_replace MySet.Nat.set P hP_unique (x ^ (𝟚 : MyNat))]
  exact Exists.intro x (And.intro (MySet.Nat.is_nat x) rfl)

noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun MySet.Nat.set Y (fun x _ => x ^ (𝟚 : MyNat)) _f_mem

example :
    MyFun.isSurjective f := by
  dsimp only [MyFun.isSurjective]
  intro y hy
  dsimp only [f] at hy
  dsimp only [MyFun.from_fun] at hy
  dsimp only [Y] at hy
  rw [MySet.mem_replace MySet.Nat.set P hP_unique y] at hy
  rcases hy with ⟨x, hxnat, hPxy⟩
  dsimp only [P] at hPxy
  have hfxeq :
      MyFun.eval f x (MySet.Nat.is_nat x) = y := by
    dsimp only [f]
    rw [MyFun.from_fun.eval MySet.Nat.set Y (fun x _ => x ^ (𝟚 : MyNat)) _f_mem
      x (MySet.Nat.is_nat x)]
    exact Eq.symm hPxy
  exact Exists.intro x (Exists.intro (MySet.Nat.is_nat x) hfxeq)

end Example_3_3_21

-- Definition 3.3.23
def MyFun.isBijective
    {α β : Type}
    (f : MyFun α β) :=
  MyFun.isInjective f ∧ MyFun.isSurjective f

-- Example 3.3.25
namespace Example_3_3_25

noncomputable def X : MySet MyNat :=
  MySet.Nat.set

noncomputable def Y : MySet MyNat :=
  MySet.Nat.set \ ⦃(𝟘 : MyNat)⦄

private noncomputable def _f_fn : (x : MyNat) → x ∈ X → MyNat :=
  fun n _h => n++

private theorem _f_mem
    (x : MyNat)
    (hx : x ∈ X) :
    _f_fn x hx ∈ Y := by
  dsimp only [Y]
  dsimp only [_f_fn]
  rw [MySet.diff]
  rw [MySet.mem_spec MySet.Nat.set (fun z => z ∉ ⦃(𝟘 : MyNat)⦄) (x++)]
  constructor
  · exact MySet.Nat.is_nat (x++)
  · intro h
    rw [MySet.mem_singleton (γ := MySet MyNat) (𝟘 : MyNat) (x++)] at h
    exact MyNat.succ_ne_zero x h

noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun X Y _f_fn _f_mem

example :
    MyFun.isBijective f := by
  dsimp only [MyFun.isBijective]
  constructor
  · dsimp only [MyFun.isInjective]
    intro x x' hx hx' hxx'
    dsimp only [f]
    rw [MyFun.from_fun.eval X Y _f_fn _f_mem x hx,
      MyFun.from_fun.eval X Y _f_fn _f_mem x' hx']
    dsimp only [_f_fn]
    exact MyNat.succ_inj' x x' hxx'
  · dsimp only [MyFun.isSurjective]
    intro y hy
    dsimp only [f] at hy
    dsimp only [MyFun.from_fun] at hy
    dsimp only [Y] at hy
    rw [MySet.diff] at hy
    have hmem :
        y ∈ MySet.Nat.set ∧ ¬y ∈ ⦃(𝟘 : MyNat)⦄ :=
      Iff.mp (MySet.mem_spec MySet.Nat.set (fun z => ¬z ∈ ⦃(𝟘 : MyNat)⦄) y) hy
    rcases hmem with ⟨_hy, hny⟩
    rw [MySet.mem_singleton (γ := MySet MyNat) (𝟘 : MyNat) y] at hny
    have hpos :
        MyNat.is_positive y :=
      hny
    rcases MyNat.unique_pred_of_pos y hpos with ⟨x, hx, _⟩
    refine Exists.intro x (Exists.intro (MySet.Nat.is_nat x) ?_)
    dsimp only [f]
    rw [MyFun.from_fun.eval X Y _f_fn _f_mem x (MySet.Nat.is_nat x)]
    dsimp only [_f_fn]
    exact hx

end Example_3_3_25

-- Remark 3.3.27
theorem MyFun.exists_unique_of_bijective
    {α β : Type}
    (f : MyFun α β)
    (hf : MyFun.isBijective f)
    (y : β)
    (hy : y ∈ MyFun.codomain f) :
    ∃ (x : α) (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
      ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x' := by
  dsimp only [MyFun.isBijective] at hf
  rcases hf with ⟨hinj, hsurj⟩
  dsimp only [MyFun.isSurjective] at hsurj
  rcases hsurj y hy with ⟨x, hx, hxy⟩
  use x, hx, hxy
  intro x' hx' hxy'
  rw [MyFun.isInjective_iff f] at hinj
  dsimp only [MyFun.isInjective'] at hinj
  rw [← hxy'] at hxy
  exact hinj x x' hx hx' hxy

noncomputable def MyFun.inv
    {α β : Type}
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    MyFun β α := by
  let X :
      MySet β :=
    MyFun.codomain f
  let Y :
      MySet α :=
    MyFun.domain f
  let finv
      (y : β)
      (hy : y ∈ X) :
      α :=
    MyClassical.choose
      (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hy)
  let aux
      (y : β)
      (hy : y ∈ X) :
      finv y hy ∈ Y := by
    dsimp only [Y]
    dsimp only [finv]
    rcases MyClassical.choose_spec
      (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hy) with ⟨hx, h⟩
    exact hx
  exact MyFun.from_fun X Y finv aux

section Exercises

-- Exercise 3.3.1
example
    (f : MyFun α β) :
    f ≃ f := by
  sorry

example
    (f g : MyFun α β)
    (hfg : f ≃ g) :
    g ≃ f := by
  sorry

example
    (f g h : MyFun α β)
    (hfg : f ≃ g)
    (hgh : g ≃ h) :
    f ≃ h := by
  sorry

example
    (f f' : MyFun α β)
    (g g' : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf'g' : MyFun.codomain f' = MyFun.domain g')
    (hff' : f ≃ f')
    (hgg' : g ≃ g') :
    MyFun.comp f g hfg ≃ MyFun.comp f' g' hf'g' := by
  sorry

-- Exercise 3.3.2
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isInjective f)
    (hg : MyFun.isInjective g) :
    (MyFun.isInjective (MyFun.comp f g hfg)) := by
  sorry

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isSurjective f)
    (hg : MyFun.isSurjective g) :
    (MyFun.isSurjective (MyFun.comp f g hfg)) := by
  sorry

-- Exercise 3.3.3
-- TODO: When is the empty function into a given set X injective? surjective? bijective?

-- Exercise 3.3.4
example
    (f f' : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf'g : MyFun.codomain f' = MyFun.domain g)
    (hcomp : MyFun.comp f g hfg ≃ MyFun.comp f' g hf'g)
    (hg : MyFun.isInjective g) :
    f ≃ f' := by
  sorry

-- TODO: Is the same statement true if g is not injective?

example
    (f : MyFun α β)
    (g g' : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hfg' : MyFun.codomain f = MyFun.domain g')
    (hcomp : MyFun.comp f g hfg ≃ MyFun.comp f g' hfg')
    (hf : MyFun.isSurjective f) :
    g ≃ g' := by
  sorry

-- TODO: Is the same statement true if f is not surjective?

-- Exercise 3.3.5
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hcomp : (MyFun.isInjective (MyFun.comp f g hfg))) :
    MyFun.isInjective f := by
  sorry

-- TODO: Is it true that g must also be injective?

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hcomp : (MyFun.isSurjective (MyFun.comp f g hfg))) :
    MyFun.isSurjective g := by
  sorry

-- TODO: Is it true that f must also be surjective?

-- Exercise 3.3.6
section Exercise_3_3_6

example
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    (MyFun.isBijective (MyFun.inv f hf)) := by
  sorry

example
    (f : MyFun α β)
    (hf : MyFun.isBijective f)
    (hfi : (MyFun.isBijective (MyFun.inv f hf))) :
    (MyFun.inv (MyFun.inv f hf)) hfi ≃ f := by
  sorry

end Exercise_3_3_6

-- Exercise 3.3.7
section Exercise_3_3_7

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isBijective f)
    (hg : MyFun.isBijective g) :
    (MyFun.isBijective (MyFun.comp f g hfg)) := by
  sorry

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isBijective f)
    (hg : MyFun.isBijective g)
    (hgf : (MyFun.isBijective (MyFun.comp f g hfg)))
    (hgfinv_cod_finvdom : (MyFun.codomain (MyFun.inv g hg)) = (MyFun.domain (MyFun.inv f hf))) :
    (MyFun.inv (MyFun.comp f g hfg)) hgf ≃
    (MyFun.comp (MyFun.inv g hg)) (MyFun.inv f hf) hgfinv_cod_finvdom := by
  sorry

end Exercise_3_3_7

-- Exercise 3.3.8
section Exercise_3_3_8

private def ι'
    {α : Type}
    (X Y : MySet α)
    (hXY : X ⊆ Y) :
    MyFun α α := by
  let f :
      α → α :=
    fun x => x
  have h
      (x : α)
      (hx : x ∈ X) :
      f x ∈ Y :=
    hXY x hx
  exact MyFun.from_fun X Y (fun x _ => f x) h

private theorem aux'
    {α : Type}
    (X : MySet α) :
    X ⊆ X := by
  have h
      (x : α)
      (hx : x ∈ X) :
      x ∈ X :=
    hx
  exact h

private def ι_id'
    {α : Type}
    (X : MySet α) :=
  ι' X X (aux' X)

example
    {X Y Z : MySet α}
    (hXY : X ⊆ Y)
    (hYZ : Y ⊆ Z)
    (h₁ : (MyFun.codomain (ι' X Y hXY)) = (MyFun.domain (ι' Y Z hYZ)))
    (h₂ : X ⊆ Z) :
    (MyFun.comp (ι' X Y hXY)) (ι' Y Z hYZ) h₁ ≃ ι' X Z h₂ := by
  sorry

example
    (A : MySet α)
    (f : MyFun α β)
    (hfdom : MyFun.domain f = A)
    (h₁ : (MyFun.codomain (ι_id' A)) = MyFun.domain f) :
    f ≃ (MyFun.comp (ι_id' A)) f h₁ := by
  sorry

example
    (B : MySet β)
    (f : MyFun α β)
    (hfcodom : MyFun.codomain f = B)
    (h₁ : MyFun.codomain f = (MyFun.domain (ι_id' B))) :
    f ≃ MyFun.comp f (ι_id' B) h₁ := by
  sorry

example
    (f : MyFun α β)
    (hf : MyFun.isBijective f)
    (h₁ : (MyFun.codomain (MyFun.inv f hf)) = MyFun.domain f)
    (h₂ : MyFun.codomain f = (MyFun.domain (MyFun.inv f hf)))
    (B : MySet β)
    (hfcodom : MyFun.codomain f = B) :
    (MyFun.comp (MyFun.inv f hf)) f h₁ ≃ ι_id' B := by
  sorry

example
    (f : MyFun α β)
    (hf : MyFun.isBijective f)
    (h₁ : MyFun.codomain f = (MyFun.domain (MyFun.inv f hf)))
    (A : MySet α)
    (hfdom : MyFun.domain f = A) :
    MyFun.comp f (MyFun.inv f hf) h₁ ≃ ι_id' A := by
  sorry

example
    (X Y : MySet α)
    (Z : MySet β)
    (hXY : MySet.disjoint X Y)
    (f : MyFun α β)
    (hfdom : MyFun.domain f = X)
    (hfcodom : MyFun.codomain f = Z)
    (g : MyFun α β)
    (hgdom : MyFun.domain g = Y)
    (hgcodom : MyFun.codomain g = Z) :
    ∃ (h : MyFun α β), MyFun.domain h = X ∪ Y ∧ MyFun.codomain h = Z := by
  sorry

end Exercise_3_3_8

end Exercises
