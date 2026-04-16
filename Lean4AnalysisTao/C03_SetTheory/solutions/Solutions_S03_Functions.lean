import Lean4AnalysisTao.C03_SetTheory.S03_Functions

section Exercises

-- Exercise 3.3.1
example
    (f : MyFun α β) :
    f ≃ f := by
  dsimp only [MyFun.eq]
  constructor
  · rfl
  · constructor
    · rfl
    · intro x hxf hxg
      rfl

example
    (f g : MyFun α β)
    (hfg : f ≃ g) :
    g ≃ f := by
  dsimp only [MyFun.eq] at hfg
  rcases hfg with ⟨hdom, hcodom, hfg⟩
  dsimp only [MyFun.eq]
  constructor
  · exact Eq.symm hdom
  · constructor
    · exact Eq.symm hcodom
    · intro x hxg hxf
      exact Eq.symm (hfg x hxf hxg)

example
    (f g h : MyFun α β)
    (hfg : f ≃ g)
    (hgh : g ≃ h) :
    f ≃ h := by
  dsimp only [MyFun.eq] at hfg
  rcases hfg with ⟨hdomfg, hcodomfg, hfg⟩
  dsimp only [MyFun.eq] at hgh
  rcases hgh with ⟨hdomgh, hcodomgh, hgh⟩
  dsimp only [MyFun.eq]
  constructor
  · rw [hdomfg]
    exact hdomgh
  · constructor
    · rw [hcodomfg]
      exact hcodomgh
    · intro x hxf hxh
      have hxg :
          x ∈ MyFun.domain g := by
        rw [← hdomfg]
        exact hxf
      rw [hfg x hxf hxg]
      exact hgh x hxg hxh

example
    (f f' : MyFun α β)
    (g g' : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf'g' : MyFun.codomain f' = MyFun.domain g')
    (hff' : f ≃ f')
    (hgg' : g ≃ g') :
    MyFun.comp f g hfg ≃ MyFun.comp f' g' hf'g' := by
  dsimp only [MyFun.eq] at hff'
  rcases hff' with ⟨hdomff', hcodomff', hff'⟩
  dsimp only [MyFun.eq] at hgg'
  rcases hgg' with ⟨hdomgg', hcodomgg', hgg'⟩
  dsimp only [MyFun.eq]
  constructor
  · rw [MyFun.comp.eval.domain f g hfg]
    rw [MyFun.comp.eval.domain f' g' hf'g']
    exact hdomff'
  · constructor
    · rw [MyFun.comp.eval.codomain f g hfg]
      rw [MyFun.comp.eval.codomain f' g' hf'g']
      exact hcodomgg'
    · intro x hxf hxf'
      dsimp only [MyFun.comp]
      have hauxf
          (x : α)
          (hx : x ∈ MyFun.domain f) :
          MyFun.eval f x hx ∈ MyFun.domain g := by
        rw [← hfg]
        exact MyFun.eval_codomain f x hx
      have hauxf'
          (x : α)
          (hx : x ∈ MyFun.domain f') :
          MyFun.eval f' x hx ∈ MyFun.domain g' := by
        rw [← hf'g']
        exact MyFun.eval_codomain f' x hx
      have hgfcodom
          (x : α)
          (hx : x ∈ MyFun.domain f) :
          MyFun.eval g (MyFun.eval f x hx) (hauxf x hx) ∈ MyFun.codomain g := by
        exact MyFun.eval_codomain g (MyFun.eval f x hx) (hauxf x hx)
      have hg'f'codom
          (x : α)
          (hx : x ∈ MyFun.domain f') :
          MyFun.eval g' (MyFun.eval f' x hx) (hauxf' x hx) ∈ MyFun.codomain g' := by
        exact MyFun.eval_codomain g' (MyFun.eval f' x hx) (hauxf' x hx)
      rw [MyFun.from_fun.eval (MyFun.domain f) (MyFun.codomain g)
        (fun x h => MyFun.eval g (MyFun.eval f x h) (hauxf x h)) hgfcodom x hxf]
      rw [MyFun.from_fun.eval (MyFun.domain f') (MyFun.codomain g')
        (fun x h => MyFun.eval g' (MyFun.eval f' x h) (hauxf' x h)) hg'f'codom x hxf']
      dsimp only [MyFun.comp] at hxf
      dsimp only [MyFun.from_fun] at hxf
      dsimp only [MyFun.comp] at hxf'
      dsimp only [MyFun.from_fun] at hxf'
      have hfxg :
          MyFun.eval f x hxf ∈ MyFun.domain g := by
        rw [← hfg]
        exact MyFun.eval_codomain f x hxf
      have hfxg' : MyFun.eval f x hxf ∈ MyFun.domain g' := by
        rw [← hf'g']
        rw [← hcodomff']
        exact MyFun.eval_codomain f x hxf
      have hfxfx' : MyFun.eval f x hxf = MyFun.eval f' x hxf' :=
        hff' x hxf hxf'
      have hgfxg'fx :
          MyFun.eval g (MyFun.eval f x hxf) hfxg = MyFun.eval g' (MyFun.eval f x hxf) hfxg' :=
        hgg' (MyFun.eval f x hxf) hfxg hfxg'
      rw [hgfxg'fx]
      have hf'xg' : MyFun.eval f' x hxf' ∈ MyFun.domain g' := by
        rw [← hf'g']
        exact MyFun.eval_codomain f' x hxf'
      exact MyFun.substitute g' (MyFun.eval f x hxf) (MyFun.eval f' x hxf')
        hfxg' hf'xg' hfxfx'

-- Exercise 3.3.2
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hfinj : MyFun.isInjective f)
    (hginj : MyFun.isInjective g) :
    (MyFun.isInjective (MyFun.comp f g hfg)) := by
  dsimp only [MyFun.isInjective] at hfinj
  dsimp only [MyFun.isInjective] at hginj
  dsimp only [MyFun.isInjective]
  intro x x' hxgfdom hx'gfdom hxx'
  dsimp only [MyFun.comp] at hxgfdom
  dsimp only [MyFun.from_fun] at hxgfdom
  dsimp only [MyFun.comp] at hx'gfdom
  dsimp only [MyFun.from_fun] at hx'gfdom
  have hfxgdom :
      MyFun.eval f x hxgfdom ∈ MyFun.domain g := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hxgfdom
  rw [MyFun.comp.eval f g hfg x hxgfdom hfxgdom hxgfdom]
  have hfx'gdom : MyFun.eval f x' hx'gfdom ∈ MyFun.domain g := by
    rw [← hfg]
    exact MyFun.eval_codomain f x' hx'gfdom
  rw [MyFun.comp.eval f g hfg x' hx'gfdom hfx'gdom hx'gfdom]
  exact hginj (MyFun.eval f x hxgfdom) (MyFun.eval f x' hx'gfdom) hfxgdom hfx'gdom
    (hfinj x x' hxgfdom hx'gfdom hxx')

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hfsurj : MyFun.isSurjective f)
    (hgsurj : MyFun.isSurjective g) :
    (MyFun.isSurjective (MyFun.comp f g hfg)) := by
  dsimp only [MyFun.isSurjective] at hfsurj
  dsimp only [MyFun.isSurjective] at hgsurj
  dsimp only [MyFun.isSurjective]
  intro z hz
  dsimp only [MyFun.comp] at hz
  dsimp only [MyFun.from_fun] at hz
  rcases hgsurj z hz with ⟨y, hy, hgyz⟩
  have hyfcodom :
      y ∈ MyFun.codomain f := by
    rw [hfg]
    exact hy
  rcases hfsurj y hyfcodom with ⟨x, hx, hfx⟩
  use x, hx
  have hfxgdom :
      MyFun.eval f x hx ∈ MyFun.domain g := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hx
  rw [MyFun.comp.eval f g hfg x hx hfxgdom hx]
  rw [← hgyz]
  exact MyFun.substitute g (MyFun.eval f x hx) y hfxgdom hy hfx

-- Exercise 3.3.3
-- TODO: When is the empty function into a given set X injective? surjective? bijective?

-- Exercise 3.3.4
example
    (f f' : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf'g : MyFun.codomain f' = MyFun.domain g)
    (hgfgf' : MyFun.comp f g hfg ≃ MyFun.comp f' g hf'g)
    (hginj : MyFun.isInjective g) :
    f ≃ f' := by
  dsimp only [MyFun.eq] at hgfgf'
  rcases hgfgf' with ⟨hgfgf'dom, hgfgf'codom, hgfgf'⟩
  dsimp only [MyFun.comp] at hgfgf'dom
  dsimp only [MyFun.from_fun] at hgfgf'dom
  dsimp only [MyFun.eq]
  constructor
  · exact hgfgf'dom
  · constructor
    · rw [hfg]
      rw [hf'g]
    · intro x hxf hxf'
      have hxgfdom :
          x ∈ (MyFun.domain (MyFun.comp f g hfg)) := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxf
      have hxgf'dom : x ∈ (MyFun.domain (MyFun.comp f' g hf'g)) := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxf'
      have hgfxgf'x :
          (MyFun.eval (MyFun.comp f g hfg)) x hxgfdom =
            (MyFun.eval (MyFun.comp f' g hf'g)) x hxgf'dom :=
        hgfgf' x hxgfdom hxgf'dom
      have hfxgdom :
          MyFun.eval f x hxf ∈ MyFun.domain g := by
        rw [← hfg]
        exact MyFun.eval_codomain f x hxf
      rw [MyFun.comp.eval f g hfg x hxf hfxgdom hxgfdom] at hgfxgf'x
      have hfx'gdom : MyFun.eval f' x hxf' ∈ MyFun.domain g := by
        rw [← hf'g]
        exact MyFun.eval_codomain f' x hxf'
      rw [MyFun.comp.eval f' g hf'g x hxf' hfx'gdom hxgf'dom] at hgfxgf'x
      rw [MyFun.isInjective_iff g] at hginj
      dsimp only [MyFun.isInjective'] at hginj
      exact hginj (MyFun.eval f x hxf) (MyFun.eval f' x hxf') hfxgdom hfx'gdom hgfxgf'x

-- TODO: Is the same statement true if g is not injective?

example
    (f : MyFun α β)
    (g g' : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hfg' : MyFun.codomain f = MyFun.domain g')
    (hgfg'f : MyFun.comp f g hfg ≃ MyFun.comp f g' hfg')
    (hfsurj : MyFun.isSurjective f) :
    g ≃ g' := by
  dsimp only [MyFun.eq] at hgfg'f
  rcases hgfg'f with ⟨hgfg'fdom, hgfg'fcodom, hgfg'f⟩
  dsimp only [MyFun.comp] at hgfg'fcodom
  dsimp only [MyFun.from_fun] at hgfg'fcodom
  dsimp only [MyFun.eq]
  constructor
  · rw [← hfg]
    exact hfg'
  · constructor
    · exact hgfg'fcodom
    · intro y hygdom hyg'dom
      dsimp only [MyFun.isSurjective] at hfsurj
      have hyfcodom :
          y ∈ MyFun.codomain f := by
        rw [hfg]
        exact hygdom
      rcases hfsurj y hyfcodom with ⟨x, hxf, hfy⟩
      have hfxgdom :
          MyFun.eval f x hxf ∈ MyFun.domain g := by
        rw [← hfg]
        exact MyFun.eval_codomain f x hxf
      have hfxg'dom : MyFun.eval f x hxf ∈ MyFun.domain g' := by
        rw [← hfg']
        exact MyFun.eval_codomain f x hxf
      have hgfxg'fx :
          (MyFun.eval (MyFun.comp f g hfg)) x hxf =
            (MyFun.eval (MyFun.comp f g' hfg')) x hxf :=
        hgfg'f x hxf hxf
      rw [MyFun.comp.eval f g hfg x hxf hfxgdom hxf] at hgfxg'fx
      rw [MyFun.comp.eval f g' hfg' x hxf hfxg'dom hxf] at hgfxg'fx
      have hgfxgy :
          MyFun.eval g (MyFun.eval f x hxf) hfxgdom = MyFun.eval g y hygdom :=
        MyFun.substitute g (MyFun.eval f x hxf) y hfxgdom hygdom hfy
      have hg'fxg'y :
          MyFun.eval g' (MyFun.eval f x hxf) hfxg'dom = MyFun.eval g' y hyg'dom :=
        MyFun.substitute g' (MyFun.eval f x hxf) y hfxg'dom hyg'dom hfy
      rw [← hgfxgy]
      rw [← hg'fxg'y]
      exact hgfxg'fx

-- TODO: Is the same statement true if f is not surjective?

-- Exercise 3.3.5
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hgfinj : (MyFun.isInjective (MyFun.comp f g hfg))) :
    MyFun.isInjective f := by
  dsimp only [MyFun.isInjective] at hgfinj
  dsimp only [MyFun.isInjective]
  intro x x' hxfdom hx'fdom hxx'
  have hxgfdom :
      x ∈ (MyFun.domain (MyFun.comp f g hfg)) := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hxfdom
  have hx'gfdom : x' ∈ (MyFun.domain (MyFun.comp f g hfg)) := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hx'fdom
  have hgfxngfx' :
      (MyFun.eval (MyFun.comp f g hfg)) x hxgfdom ≠ (MyFun.eval (MyFun.comp f g hfg)) x' hx'gfdom :=
    hgfinj x x' hxgfdom hx'gfdom hxx'
  have hfxgdom :
      MyFun.eval f x hxfdom ∈ MyFun.domain g := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hxfdom
  have hfx'gdom : MyFun.eval f x' hx'fdom ∈ MyFun.domain g := by
    rw [← hfg]
    exact MyFun.eval_codomain f x' hx'fdom
  rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom] at hgfxngfx'
  rw [MyFun.comp.eval f g hfg x' hx'fdom hfx'gdom hx'gfdom] at hgfxngfx'
  intro hfxfx'
  have hgfxgfx' :
      MyFun.eval g (MyFun.eval f x hxfdom) hfxgdom
        = MyFun.eval g (MyFun.eval f x' hx'fdom) hfx'gdom :=
    MyFun.substitute g (MyFun.eval f x hxfdom) (MyFun.eval f x' hx'fdom)
      hfxgdom hfx'gdom hfxfx'
  exact hgfxngfx' hgfxgfx'

-- TODO: Is it true that g must also be injective?

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hgfsurj : (MyFun.isSurjective (MyFun.comp f g hfg))) :
    MyFun.isSurjective g := by
  dsimp only [MyFun.isSurjective] at hgfsurj
  dsimp only [MyFun.isSurjective]
  intro z hz
  have hzgfcodom :
      z ∈ (MyFun.codomain (MyFun.comp f g hfg)) := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hz
  rcases hgfsurj z hzgfcodom with ⟨x, hxgfdom, hgfxz⟩
  have hxfdom :
      x ∈ MyFun.domain f := by
    dsimp only [MyFun.comp] at hxgfdom
    dsimp only [MyFun.from_fun] at hxgfdom
    exact hxgfdom
  have hfxgdom :
      MyFun.eval f x hxfdom ∈ MyFun.domain g := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hxfdom
  use (MyFun.eval f x hxfdom), hfxgdom
  rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom] at hgfxz
  exact hgfxz

-- TODO: Is it true that f must also be surjective?

-- Exercise 3.3.6
namespace Exercise_3_3_6

theorem aux₁
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    MyFun.codomain f = (MyFun.domain (MyFun.inv f hf)) := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

theorem finv_f
    (f : MyFun α β)
    (hf : MyFun.isBijective f)
    (x : α)
    (hxf : x ∈ MyFun.domain f) :
    (MyFun.eval (MyFun.comp f (MyFun.inv f hf) (aux₁ f hf))) x hxf = x := by
  have hffi :
      MyFun.codomain f = (MyFun.domain (MyFun.inv f hf)) :=
    aux₁ f hf
  have hfxfidom :
      MyFun.eval f x hxf ∈ (MyFun.domain (MyFun.inv f hf)) := by
    rw [← hffi]
    exact MyFun.eval_codomain f x hxf
  rw [MyFun.comp.eval f (MyFun.inv f hf) hffi x hxf hfxfidom hxf]
  dsimp only [MyFun.inv]
  let finv :
      (y : β) → y ∈ MyFun.codomain f → α :=
    fun y hy => MyClassical.choose
      (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hy)
  have hfinvaux
      (y : β)
      (hy : y ∈ MyFun.codomain f) :
      finv y hy ∈ MyFun.domain f := by
    dsimp only [finv]
    rcases MyClassical.choose_spec
      (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hy) with ⟨hx, h⟩
    exact hx
  rw [MyFun.from_fun.eval (MyFun.codomain f) (MyFun.domain f) finv hfinvaux (MyFun.eval f x hxf) hfxfidom]
  rcases MyClassical.choose_spec
      (fun x' => ∃ (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = MyFun.eval f x hxf ∧
        ∀ (x'' : α) (hx'' : x'' ∈ MyFun.domain f),
          MyFun.eval f x'' hx'' = MyFun.eval f x hxf → x' = x'')
      (MyFun.exists_unique_of_bijective f hf (MyFun.eval f x hxf) hfxfidom)
    with ⟨hx, h, h'⟩
  exact h' x hxf rfl

theorem aux₂
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    (MyFun.codomain (MyFun.inv f hf)) = MyFun.domain f := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

theorem f_finv
    (f : MyFun α β)
    (hf : MyFun.isBijective f)
    (y : β)
    (hyfidom : y ∈ (MyFun.domain (MyFun.inv f hf))) :
    (MyFun.eval ((MyFun.comp (MyFun.inv f hf)) f (aux₂ f hf))) y hyfidom = y := by
  have hffi :
      (MyFun.codomain (MyFun.inv f hf)) = MyFun.domain f :=
    aux₂ f hf
  have hfiyfdom :
      (MyFun.eval (MyFun.inv f hf)) y hyfidom ∈ MyFun.domain f := by
    rw [← hffi]
    exact MyFun.eval_codomain (MyFun.inv f hf) y hyfidom
  rw [MyFun.comp.eval (MyFun.inv f hf) f hffi y hyfidom hfiyfdom hyfidom]
  dsimp only [MyFun.inv] at hyfidom
  dsimp only [MyFun.from_fun] at hyfidom
  rcases MyClassical.choose_spec
      (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hyfidom)
    with ⟨hx, h, h'⟩
  have hPfiyy :
      MyFun.prop f ((MyFun.eval (MyFun.inv f hf)) y hyfidom) y := by
    dsimp only [MyFun.inv]
    let finv :
        (y : β) → y ∈ MyFun.codomain f → α :=
      fun y hy => MyClassical.choose
        (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
          ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
        (MyFun.exists_unique_of_bijective f hf y hy)
    have hfinvaux
        (y : β)
        (hy : y ∈ MyFun.codomain f) :
        finv y hy ∈ MyFun.domain f := by
      dsimp only [finv]
      rcases MyClassical.choose_spec
        (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
          ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
        (MyFun.exists_unique_of_bijective f hf y hy) with ⟨hx', h'⟩
      exact hx'
    rw [MyFun.from_fun.eval (MyFun.codomain f) (MyFun.domain f) finv hfinvaux y hyfidom]
    let hchosen :
        α :=
      MyClassical.choose
        (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
          ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
        (MyFun.exists_unique_of_bijective f hf y hyfidom)
    have hfwd :
        y = MyFun.eval f hchosen hx →
          MyFun.prop f hchosen y :=
      Iff.mp (MyFun.def f hchosen y hx hyfidom)
    exact hfwd (Eq.symm h)
  have hfeq :
      y = MyFun.eval f ((MyFun.eval (MyFun.inv f hf)) y hyfidom) hfiyfdom :=
    Iff.mpr (MyFun.def f ((MyFun.eval (MyFun.inv f hf)) y hyfidom) y hfiyfdom hyfidom) hPfiyy
  exact Eq.symm hfeq

theorem finv_bij
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    (MyFun.isBijective (MyFun.inv f hf)) := by
  have hfcopy :
      MyFun.isBijective f :=
    hf
  dsimp only [MyFun.isBijective] at hfcopy
  rcases hfcopy with ⟨hinj, hsurj⟩
  dsimp only [MyFun.isBijective]
  constructor
  · dsimp only [MyFun.isInjective]
    intro y y' hy hy' hyy'
    intro hfiyfiy'
    dsimp only [MyFun.isSurjective] at hsurj
    have hyfcodom :
        y ∈ MyFun.codomain f := by
      dsimp only [MyFun.inv] at hy
      dsimp only [MyFun.from_fun] at hy
      exact hy
    rcases hsurj y hyfcodom with ⟨x, hxfdom, hfxy⟩
    have hy'fcodom : y' ∈ MyFun.codomain f := by
      dsimp only [MyFun.inv] at hy'
      dsimp only [MyFun.from_fun] at hy'
      exact hy'
    rcases hsurj y' hy'fcodom with ⟨x', hx'fdom, hfx'y'⟩
    have hfxfidom :
        (MyFun.eval f x hxfdom) ∈ (MyFun.domain (MyFun.inv f hf)) := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact MyFun.eval_codomain f x hxfdom
    have hfiyfifx :
        (MyFun.eval (MyFun.inv f hf)) y hy =
          (MyFun.eval (MyFun.inv f hf)) (MyFun.eval f x hxfdom) hfxfidom :=
      MyFun.substitute (MyFun.inv f hf) y (MyFun.eval f x hxfdom) hy hfxfidom (Eq.symm hfxy)
    rw [hfiyfifx] at hfiyfiy'
    have hfx'fidom : (MyFun.eval f x' hx'fdom) ∈ (MyFun.domain (MyFun.inv f hf)) := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact MyFun.eval_codomain f x' hx'fdom
    have hfiy'fifx' :
        (MyFun.eval (MyFun.inv f hf)) y' hy' =
          (MyFun.eval (MyFun.inv f hf)) (MyFun.eval f x' hx'fdom) hfx'fidom :=
      MyFun.substitute (MyFun.inv f hf) y' (MyFun.eval f x' hx'fdom) hy' hfx'fidom (Eq.symm hfx'y')
    rw [hfiy'fifx'] at hfiyfiy'
    have hxfifdom :
        x ∈ (MyFun.domain (MyFun.comp f (MyFun.inv f hf) (aux₁ f hf))) := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    rw [← MyFun.comp.eval f (MyFun.inv f hf) (aux₁ f hf) x hxfdom hfxfidom hxfifdom] at hfiyfiy'
    have hx'fifdom : x' ∈ (MyFun.domain (MyFun.comp f (MyFun.inv f hf) (aux₁ f hf))) := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hx'fdom
    rw [← MyFun.comp.eval f (MyFun.inv f hf) (aux₁ f hf) x' hx'fdom hfx'fidom hx'fifdom]
      at hfiyfiy'
    rw [finv_f f hf x hxfdom] at hfiyfiy'
    rw [finv_f f hf x' hx'fdom] at hfiyfiy'
    have hfxfx' : MyFun.eval f x hxfdom = MyFun.eval f x' hx'fdom :=
      MyFun.substitute f x x' hxfdom hx'fdom hfiyfiy'
    rw [hfxy] at hfxfx'
    rw [hfx'y'] at hfxfx'
    exact hyy' hfxfx'
  · dsimp only [MyFun.isSurjective]
    intro x hxficodom
    have hxfdom :
        x ∈ MyFun.domain f := by
      dsimp only [MyFun.inv]
      exact hxficodom
    use (MyFun.eval f x hxficodom)
    have hfxfidom :
        MyFun.eval f x hxfdom ∈ (MyFun.domain (MyFun.inv f hf)) := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact MyFun.eval_codomain f x hxfdom
    use hfxfidom
    have hxfifdom :
        x ∈ (MyFun.domain (MyFun.comp f (MyFun.inv f hf) (aux₁ f hf))) := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    rw [← MyFun.comp.eval f (MyFun.inv f hf) (aux₁ f hf) x hxfdom hfxfidom hxfifdom]
    rw [finv_f f hf x hxfdom]

example
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    (MyFun.inv (MyFun.inv f hf)) (finv_bij f hf) ≃ f := by
  have hfi :
      (MyFun.isBijective (MyFun.inv f hf)) :=
    finv_bij f hf
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [MyFun.inv]
    dsimp only [MyFun.from_fun]
  · constructor
    · dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
    · intro x hxfiidom hxfdom
      have hfiicodomfidom :
          (MyFun.codomain ((MyFun.inv (MyFun.inv f hf)) hfi)) = (MyFun.domain (MyFun.inv f hf)) := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
      have hxfifiidom :
          x ∈ (MyFun.domain ((MyFun.comp ((MyFun.inv (MyFun.inv f hf)) hfi)) (MyFun.inv f hf) hfiicodomfidom)) := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxfiidom
      have hxfifdom :
          x ∈ (MyFun.domain (MyFun.comp f (MyFun.inv f hf) (aux₁ f hf))) := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxfdom
      have hfifiixfifx :
          (MyFun.eval ((MyFun.comp ((MyFun.inv (MyFun.inv f hf)) hfi)) (MyFun.inv f hf) hfiicodomfidom)) x hxfifiidom =
            (MyFun.eval (MyFun.comp f (MyFun.inv f hf) (aux₁ f hf))) x hxfifdom := by
        have hxfiidom2 :
            x ∈ (MyFun.domain ((MyFun.inv (MyFun.inv f hf)) hfi)) := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
          exact hxfiidom
        rw [f_finv (MyFun.inv f hf) hfi x hxfiidom]
        rw [finv_f f hf x hxfdom]
      have hfiixfidom :
          (MyFun.eval ((MyFun.inv (MyFun.inv f hf)) hfi)) x hxfifiidom ∈ (MyFun.domain (MyFun.inv f hf)) := by
        have hfiixfiicodom :
            (MyFun.eval ((MyFun.inv (MyFun.inv f hf)) hfi)) x hxfifiidom ∈ (MyFun.codomain ((MyFun.inv (MyFun.inv f hf)) hfi)) :=
          MyFun.eval_codomain ((MyFun.inv (MyFun.inv f hf)) hfi) x hxfifiidom
        have hfiicodomfidom' :
            (MyFun.codomain ((MyFun.inv (MyFun.inv f hf)) hfi)) = (MyFun.domain (MyFun.inv f hf)) := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
        rw [← hfiicodomfidom']
        exact hfiixfiicodom
      have hfxfidom :
          MyFun.eval f x hxfifdom ∈ (MyFun.domain (MyFun.inv f hf)) := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        exact MyFun.eval_codomain f x hxfdom
      rw [MyFun.comp.eval ((MyFun.inv (MyFun.inv f hf)) hfi) (MyFun.inv f hf) hfiicodomfidom
        x hxfifiidom hfiixfidom hxfifiidom] at hfifiixfifx
      rw [MyFun.comp.eval f (MyFun.inv f hf) (aux₁ f hf) x hxfifdom hfxfidom hxfifdom]
        at hfifiixfifx
      have hficopy :
          (MyFun.isBijective (MyFun.inv f hf)) :=
        hfi
      dsimp only [MyFun.isBijective] at hficopy
      rcases hficopy with ⟨hfi_inj, hfi_surj⟩
      rw [MyFun.isInjective_iff (MyFun.inv f hf)] at hfi_inj
      dsimp only [MyFun.isInjective'] at hfi_inj
      exact hfi_inj ((MyFun.eval ((MyFun.inv (MyFun.inv f hf)) hfi)) x hxfifiidom) (MyFun.eval f x hxfifdom)
        hfiixfidom hfxfidom hfifiixfifx

end Exercise_3_3_6

-- Exercise 3.3.7
namespace Exercise_3_3_7

theorem aux₁
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isBijective f)
    (hg : MyFun.isBijective g) :
    (MyFun.isBijective (MyFun.comp f g hfg)) := by
  dsimp only [MyFun.isBijective]
  constructor
  · dsimp only [MyFun.isInjective]
    intro x x' hxgfdom hx'gfdom hxnx'
    intro hgfxgfx'
    have hxfdom :
        x ∈ MyFun.domain f := by
      dsimp only [MyFun.comp] at hxgfdom
      dsimp only [MyFun.from_fun] at hxgfdom
      exact hxgfdom
    have hfxgdom :
        MyFun.eval f x hxfdom ∈ MyFun.domain g := by
      rw [← hfg]
      exact MyFun.eval_codomain f x hxfdom
    rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom] at hgfxgfx'
    have hx'fdom : x' ∈ MyFun.domain f := by
      dsimp only [MyFun.comp] at hx'gfdom
      dsimp only [MyFun.from_fun] at hx'gfdom
      exact hx'gfdom
    have hfx'gdom : MyFun.eval f x' hx'fdom ∈ MyFun.domain g := by
      rw [← hfg]
      exact MyFun.eval_codomain f x' hx'fdom
    rw [MyFun.comp.eval f g hfg x' hx'fdom hfx'gdom hx'gfdom] at hgfxgfx'
    dsimp only [MyFun.isBijective] at hg
    rcases hg with ⟨hg_inj, hg_surj⟩
    rw [MyFun.isInjective_iff g] at hg_inj
    dsimp only [MyFun.isInjective'] at hg_inj
    have hfxfx' : MyFun.eval f x hxfdom = MyFun.eval f x' hx'fdom :=
      hg_inj (MyFun.eval f x hxfdom) (MyFun.eval f x' hx'fdom) hfxgdom hfx'gdom hgfxgfx'
    dsimp only [MyFun.isBijective] at hf
    rcases hf with ⟨hf_inj, hf_surj⟩
    rw [MyFun.isInjective_iff f] at hf_inj
    dsimp only [MyFun.isInjective'] at hf_inj
    have hxx' : x = x' :=
      hf_inj x x' hxfdom hx'fdom hfxfx'
    exact hxnx' hxx'
  · dsimp only [MyFun.isSurjective]
    intro z hzgfcodom
    dsimp only [MyFun.isBijective] at hg
    rcases hg with ⟨hg_inj, hg_surj⟩
    dsimp only [MyFun.isSurjective] at hg_surj
    rcases hg_surj z hzgfcodom with ⟨y, hygdom, hgyz⟩
    dsimp only [MyFun.isBijective] at hf
    rcases hf with ⟨hf_inj, hf_surj⟩
    dsimp only [MyFun.isSurjective] at hf_surj
    have hyfcodom :
        y ∈ MyFun.codomain f := by
      rw [hfg]
      exact hygdom
    rcases hf_surj y hyfcodom with ⟨x, hxfdom, hfyx⟩
    use x
    have hxgfdom :
        x ∈ (MyFun.domain (MyFun.comp f g hfg)) := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    use hxgfdom
    have hfxgdom :
        MyFun.eval f x hxfdom ∈ MyFun.domain g := by
      rw [← hfg]
      exact MyFun.eval_codomain f x hxfdom
    rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom]
    rw [← hgyz]
    exact MyFun.substitute g (MyFun.eval f x hxfdom) y hfxgdom hygdom hfyx

theorem aux₂
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isBijective f)
    (hg : MyFun.isBijective g) :
    (MyFun.codomain (MyFun.inv g hg)) = (MyFun.domain (MyFun.inv f hf)) := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]
  exact Eq.symm hfg

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isBijective f)
    (hg : MyFun.isBijective g) :
    (MyFun.inv (MyFun.comp f g hfg)) (aux₁ f g hfg hf hg) ≃
      (MyFun.comp (MyFun.inv g hg)) (MyFun.inv f hf) (aux₂ f g hfg hf hg) := by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [MyFun.inv]
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
  · constructor
    · dsimp only [MyFun.inv]
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
    · intro z hzgfidom hzfigidom
      have hzgidom :
          z ∈ (MyFun.domain (MyFun.inv g hg)) := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        dsimp only [MyFun.inv] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        dsimp only [MyFun.comp] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        exact hzgfidom
      have hgizfidom :
          (MyFun.eval (MyFun.inv g hg)) z hzgidom ∈ (MyFun.domain (MyFun.inv f hf)) := by
        have hdomeq :
            (MyFun.domain (MyFun.inv f hf)) = (MyFun.codomain (MyFun.inv g hg)) := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
          exact hfg
        rw [hdomeq]
        exact MyFun.eval_codomain (MyFun.inv g hg) z hzgidom
      rw [MyFun.comp.eval (MyFun.inv g hg) (MyFun.inv f hf) (aux₂ f g hfg hf hg)
        z hzgidom hgizfidom hzgfidom]
      have hgcopy :
          MyFun.isBijective g :=
        hg
      dsimp only [MyFun.isBijective] at hgcopy
      rcases hgcopy with ⟨hg_inj, hg_surj⟩
      dsimp only [MyFun.isSurjective] at hg_surj
      have hzgcodom :
          z ∈ MyFun.codomain g := by
        dsimp only [MyFun.inv] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        dsimp only [MyFun.comp] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        exact hzgfidom
      rcases MyFun.exists_unique_of_bijective g hg z hzgfidom
        with ⟨y, hygdom, hgyz, hgyz!⟩
      have hgizy :
          (MyFun.eval (MyFun.inv g hg)) z hzgidom = y := by
        have hgygidom :
            MyFun.eval g y hygdom ∈ (MyFun.domain (MyFun.inv g hg)) := by
          have hdomeq :
              (MyFun.domain (MyFun.inv g hg)) = MyFun.codomain g := by
            dsimp only [MyFun.inv]
            dsimp only [MyFun.from_fun]
          rw [hdomeq]
          exact MyFun.eval_codomain g y hygdom
        have hsubst :
            (MyFun.eval (MyFun.inv g hg)) z hzgidom =
              (MyFun.eval (MyFun.inv g hg)) (MyFun.eval g y hygdom) hgygidom :=
          MyFun.substitute (MyFun.inv g hg) z (MyFun.eval g y hygdom)
            hzgidom hgygidom (Eq.symm hgyz)
        rw [hsubst]
        rw [← MyFun.comp.eval g (MyFun.inv g hg) (Exercise_3_3_6.aux₁ g hg)
          y hygdom hgygidom hygdom]
        exact Exercise_3_3_6.finv_f g hg y hygdom
      have hyfidom :
          y ∈ (MyFun.domain (MyFun.inv f hf)) := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        rw [hfg]
        exact hygdom
      rw [MyFun.substitute (MyFun.inv f hf) ((MyFun.eval (MyFun.inv g hg)) z hzgidom) y
        hgizfidom hyfidom hgizy]
      rcases MyFun.exists_unique_of_bijective f hf y hyfidom
        with ⟨x, hxfdom, hfxz, hfxz!⟩
      have hfiyx :
          (MyFun.eval (MyFun.inv f hf)) y hyfidom = x := by
        have hfxgidom :
            MyFun.eval f x hxfdom ∈ (MyFun.domain (MyFun.inv f hf)) := by
          have hdomeq :
              (MyFun.domain (MyFun.inv f hf)) = MyFun.codomain f := by
            dsimp only [MyFun.inv]
            dsimp only [MyFun.from_fun]
          rw [hdomeq]
          exact MyFun.eval_codomain f x hxfdom
        have hsubst :
            (MyFun.eval (MyFun.inv f hf)) y hyfidom =
              (MyFun.eval (MyFun.inv f hf)) (MyFun.eval f x hxfdom) hfxgidom :=
          MyFun.substitute (MyFun.inv f hf) y (MyFun.eval f x hxfdom)
            hyfidom hfxgidom (Eq.symm hfxz)
        rw [hsubst]
        rw [← MyFun.comp.eval f (MyFun.inv f hf) (Exercise_3_3_6.aux₁ f hf)
          x hxfdom hfxgidom hxfdom]
        exact Exercise_3_3_6.finv_f f hf x hxfdom
      rw [hfiyx]
      have hgf :
          (MyFun.isBijective (MyFun.comp f g hfg)) :=
        aux₁ f g hfg hf hg
      rcases MyFun.exists_unique_of_bijective (MyFun.comp f g hfg) hgf z hzgfidom
        with ⟨x', hx'gfdom, hgfx'z, hgfx'z!⟩
      have hgfx'gfidom :
          (MyFun.eval (MyFun.comp f g hfg)) x' hx'gfdom ∈ (MyFun.domain ((MyFun.inv (MyFun.comp f g hfg)) hgf)) := by
        have hdomeq :
            (MyFun.domain ((MyFun.inv (MyFun.comp f g hfg)) hgf)) = (MyFun.codomain (MyFun.comp f g hfg)) := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
        rw [hdomeq]
        exact MyFun.eval_codomain (MyFun.comp f g hfg) x' hx'gfdom
      have hsubst :
          (MyFun.eval ((MyFun.inv (MyFun.comp f g hfg)) hgf)) z hzgfidom =
            (MyFun.eval ((MyFun.inv (MyFun.comp f g hfg)) hgf))
              ((MyFun.eval (MyFun.comp f g hfg)) x' hx'gfdom) hgfx'gfidom :=
        MyFun.substitute ((MyFun.inv (MyFun.comp f g hfg)) hgf) z
          ((MyFun.eval (MyFun.comp f g hfg)) x' hx'gfdom)
          hzgfidom hgfx'gfidom (Eq.symm hgfx'z)
      rw [hsubst]
      have hx'gfdom' : x' ∈ (MyFun.domain (MyFun.comp f g hfg)) :=
        hx'gfdom
      have hfg_inv :
          (MyFun.codomain (MyFun.comp f g hfg)) = (MyFun.domain ((MyFun.inv (MyFun.comp f g hfg)) hgf)) := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
      have hx'comp :
          x' ∈ (MyFun.domain ((MyFun.comp (MyFun.comp f g hfg)) ((MyFun.inv (MyFun.comp f g hfg)) hgf) hfg_inv)) := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hx'gfdom
      rw [← MyFun.comp.eval (MyFun.comp f g hfg) ((MyFun.inv (MyFun.comp f g hfg)) hgf) hfg_inv
        x' hx'gfdom hgfx'gfidom hx'comp]
      rw [Exercise_3_3_6.finv_f (MyFun.comp f g hfg) hgf x' hx'gfdom]
      have hxgfdom :
          x ∈ (MyFun.domain (MyFun.comp f g hfg)) := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxfdom
      have hgfxz :
          (MyFun.eval (MyFun.comp f g hfg)) x hxgfdom = z := by
        have hfxgdom :
            MyFun.eval f x hxfdom ∈ MyFun.domain g := by
          rw [← hfg]
          exact MyFun.eval_codomain f x hxfdom
        rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom]
        have hgeq :
            MyFun.eval g (MyFun.eval f x hxfdom) hfxgdom = MyFun.eval g y hygdom :=
          MyFun.substitute g (MyFun.eval f x hxfdom) y hfxgdom hygdom hfxz
        rw [hgeq]
        exact hgyz
      exact hgfx'z! x hxgfdom hgfxz

end Exercise_3_3_7

-- Exercise 3.3.8
namespace Exercise_3_3_8

def ι
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
      f x ∈ Y := by
    exact hXY x hx
  exact MyFun.from_fun X Y (fun x _ => f x) h

theorem aux
    {α : Type}
    (X : MySet α) :
    X ⊆ X := by
  exact fun x hx => hx

def ι_id
    {α : Type}
    (X : MySet α) :=
  ι X X (aux X)

-- (a)
namespace Exercise_3_3_8_a

theorem aux₁
    {α : Type}
    (X Y Z : MySet α)
    (hXY : X ⊆ Y)
    (hYZ : Y ⊆ Z) :
    (MyFun.codomain (ι X Y hXY)) = (MyFun.domain (ι Y Z hYZ)) := by
  dsimp only [ι]
  dsimp only [MyFun.from_fun]

theorem aux₂
    {α : Type}
    (X Y Z : MySet α)
    (hXY : X ⊆ Y)
    (hYZ : Y ⊆ Z) :
    X ⊆ Z := by
  exact MySet.subset_trans X Y Z hXY hYZ

example
    {α : Type}
    (X Y Z : MySet α)
    (hXY : X ⊆ Y)
    (hYZ : Y ⊆ Z) :
    (MyFun.comp (ι X Y hXY)) (ι Y Z hYZ) (aux₁ X Y Z hXY hYZ) ≃
      ι X Z (aux₂ X Y Z hXY hYZ) := by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [ι]
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
  · constructor
    · dsimp only [ι]
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
    · intro x hxYZXYdom hxXZdom
      have hxXYdom :
          x ∈ (MyFun.domain (ι X Y hXY)) := by
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        dsimp only [ι] at hxXZdom
        dsimp only [MyFun.from_fun] at hxXZdom
        exact hxXZdom
      have hXYxYZdom :
          (MyFun.eval (ι X Y hXY)) x hxXYdom ∈ (MyFun.domain (ι Y Z hYZ)) := by
        rw [← aux₁ X Y Z hXY hYZ]
        exact MyFun.eval_codomain (ι X Y hXY) x hxXYdom
      rw [MyFun.comp.eval (ι X Y hXY) (ι Y Z hYZ) (aux₁ X Y Z hXY hYZ)
        x hxXYdom hXYxYZdom hxYZXYdom]
      dsimp only [ι]
      rw [MyFun.from_fun.eval Y Z (fun x _ => x) (fun x hx => hYZ x hx)
        ((MyFun.eval (MyFun.from_fun X Y (fun x _ => x)
          (fun x hx => hXY x hx))) x hxXYdom) hXYxYZdom]
      rw [MyFun.from_fun.eval X Y (fun x _ => x) (fun x hx => hXY x hx)
        x hxXYdom]
      rw [MyFun.from_fun.eval X Z (fun x _ => x)
        (fun x hx => aux₂ X Y Z hXY hYZ x hx) x hxXZdom]

end Exercise_3_3_8_a

-- (b)
namespace Exercise_3_3_8_b

theorem aux₁
    {α β : Type}
    (A : MySet α)
    (f : MyFun α β)
    (hfdom : MyFun.domain f = A) :
    (MyFun.codomain (ι_id A)) = MyFun.domain f := by
  dsimp only [ι_id]
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact Eq.symm hfdom

example
    (A : MySet α)
    (f : MyFun α β)
    (hfdom : MyFun.domain f = A) :
    f ≃ (MyFun.comp (ι_id A)) f (aux₁ A f hfdom) := by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [ι_id]
    dsimp only [ι]
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hfdom
  · constructor
    · dsimp only [ι_id]
      dsimp only [ι]
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
    · intro x hxfdom hxfAdom
      have hxAdom :
          x ∈ (MyFun.domain (ι_id A)) := by
        dsimp only [ι_id]
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        rw [hfdom] at hxfdom
        exact hxfdom
      have hAxfdom :
          (MyFun.eval (ι_id A)) x hxAdom ∈ MyFun.domain f := by
        rw [← aux₁ A f hfdom]
        exact MyFun.eval_codomain (ι_id A) x hxAdom
      rw [MyFun.comp.eval (ι_id A) f (aux₁ A f hfdom) x hxAdom hAxfdom hxfAdom]
      have hxeval :
          x = (MyFun.eval (ι_id A)) x hxAdom := by
        dsimp only [ι_id]
        dsimp only [ι]
        rw [MyFun.from_fun.eval A A (fun x _ => x) (fun x hx => hx) x hxAdom]
      exact MyFun.substitute f x ((MyFun.eval (ι_id A)) x hxAdom) hxfdom hAxfdom hxeval

theorem aux₂
    {α β : Type}
    (B : MySet β)
    (f : MyFun α β)
    (hfcodom : MyFun.codomain f = B) :
    MyFun.codomain f = (MyFun.domain (ι_id B)) := by
  dsimp only [ι_id]
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact hfcodom

example
    (B : MySet β)
    (f : MyFun α β)
    (hfcodom : MyFun.codomain f = B) :
    f ≃ MyFun.comp f (ι_id B) (aux₂ B f hfcodom) := by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [ι_id]
    dsimp only [ι]
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
  · constructor
    · dsimp only [ι_id]
      dsimp only [ι]
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hfcodom
    · intro x hxfdom hxBfdom
      have hfxBdom :
          MyFun.eval f x hxfdom ∈ (MyFun.domain (ι_id B)) := by
        have hdomeq :
            (MyFun.domain (ι_id B)) = MyFun.codomain f := by
          dsimp only [ι_id]
          dsimp only [ι]
          dsimp only [MyFun.from_fun]
          exact Eq.symm hfcodom
        rw [hdomeq]
        exact MyFun.eval_codomain f x hxfdom
      rw [MyFun.comp.eval f (ι_id B) (aux₂ B f hfcodom)
        x hxfdom hfxBdom hxBfdom]
      dsimp only [ι_id]
      dsimp only [ι]
      rw [MyFun.from_fun.eval B B (fun x _ => x) (fun x hx => hx)
        (MyFun.eval f x hxfdom) hfxBdom]

end Exercise_3_3_8_b

-- (c)
namespace Exercise_3_3_8_c

theorem aux₁
    {α β : Type}
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    (MyFun.codomain (MyFun.inv f hf)) = MyFun.domain f := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

example
    (B : MySet β)
    (f : MyFun α β)
    (hfcodom : MyFun.codomain f = B)
    (hf : MyFun.isBijective f) :
    (MyFun.comp (MyFun.inv f hf)) f (aux₁ f hf) ≃ ι_id B := by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [MyFun.inv]
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    dsimp only [ι_id]
    dsimp only [ι]
    dsimp only [MyFun.from_fun]
    exact hfcodom
  · constructor
    · dsimp only [MyFun.inv]
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      dsimp only [ι_id]
      dsimp only [ι]
      dsimp only [MyFun.from_fun]
      exact hfcodom
    · intro x hxffidom hxBdom
      dsimp only [ι_id]
      dsimp only [ι]
      rw [MyFun.from_fun.eval B B (fun x _ => x) (fun x hx => hx) x hxBdom]
      have hxfidom :
          x ∈ (MyFun.domain (MyFun.inv f hf)) := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        rw [hfcodom]
        dsimp only [ι_id] at hxBdom
        dsimp only [ι] at hxBdom
        dsimp only [MyFun.from_fun] at hxBdom
        exact hxBdom
      rw [Exercise_3_3_6.f_finv f hf x hxfidom]

theorem aux₂
    {α β : Type}
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    MyFun.codomain f = (MyFun.domain (MyFun.inv f hf)) := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

example
    (A : MySet α)
    (f : MyFun α β)
    (hfdom : MyFun.domain f = A)
    (hf : MyFun.isBijective f) :
    MyFun.comp f (MyFun.inv f hf) (aux₂ f hf) ≃ ι_id A := by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [MyFun.comp]
    dsimp only [MyFun.inv]
    dsimp only [MyFun.from_fun]
    dsimp only [ι_id]
    dsimp only [ι]
    dsimp only [MyFun.from_fun]
    exact hfdom
  · constructor
    · dsimp only [MyFun.comp]
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      dsimp only [ι_id]
      dsimp only [ι]
      dsimp only [MyFun.from_fun]
      exact hfdom
    · intro x hxfifdom hxAdom
      dsimp only [ι_id]
      dsimp only [ι]
      rw [MyFun.from_fun.eval A A (fun x _ => x) (fun x hx => hx) x hxAdom]
      have hxfdom :
          x ∈ MyFun.domain f := by
        dsimp only [MyFun.comp] at hxfifdom
        dsimp only [MyFun.from_fun] at hxfifdom
        exact hxfifdom
      rw [Exercise_3_3_6.finv_f f hf x hxfdom]

end Exercise_3_3_8_c

-- (d)
namespace Exercise_3_3_8_d

theorem aux₁
    {α : Type}
    (X Y : MySet α) :
    X ⊆ X ∪ Y := by
  dsimp only [MySet.subset]
  intro x hxX
  rw [MySet.mem_union X Y x]
  exact Or.inl hxX

theorem aux₂
    {α : Type}
    (X Y : MySet α) :
    Y ⊆ X ∪ Y := by
  dsimp only [MySet.subset]
  intro x hxY
  rw [MySet.mem_union X Y x]
  exact Or.inr hxY

theorem aux₃
    {α β : Type}
    (X Y : MySet α)
    (h : MyFun α β)
    (hhdom : MyFun.domain h = X ∪ Y) :
    (MyFun.codomain (ι X (X ∪ Y) (aux₁ X Y))) = MyFun.domain h := by
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact Eq.symm hhdom

theorem aux₄
    {α β : Type}
    (X Y : MySet α)
    (h : MyFun α β)
    (hhdom : MyFun.domain h = X ∪ Y) :
    (MyFun.codomain (ι Y (X ∪ Y) (aux₂ X Y))) = MyFun.domain h := by
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact Eq.symm hhdom

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
    ∃ (h : MyFun α β) (hhdom : MyFun.domain h = X ∪ Y),
    MyFun.codomain h = Z ∧
    ((MyFun.comp (ι X (X ∪ Y) (aux₁ X Y))) h (aux₃ X Y h hhdom) ≃ f) ∧
    ((MyFun.comp (ι Y (X ∪ Y) (aux₂ X Y))) h (aux₄ X Y h hhdom) ≃ g) ∧
    (∀ (h' : MyFun α β) (hh'dom : MyFun.domain h' = X ∪ Y),
      MyFun.codomain h' = Z →
      ((MyFun.comp (ι X (X ∪ Y) (aux₁ X Y))) h' (aux₃ X Y h' hh'dom) ≃ f) →
      ((MyFun.comp (ι Y (X ∪ Y) (aux₂ X Y))) h' (aux₄ X Y h' hh'dom) ≃ g) →
        h' ≃ h) := by
  let h :
      MyFun α β :=
    {
    domain := X ∪ Y,
    codomain := Z,
    prop := fun x y => by
      by_cases h : x ∈ X
      · have hxfdom : x ∈ MyFun.domain f := by
          rw [hfdom]
          exact h
        exact y = MyFun.eval f x hxfdom
      · by_cases h' : x ∈ Y
        · have hxgdom : x ∈ MyFun.domain g := by
            rw [hgdom]
            exact h'
          exact y = MyFun.eval g x hxgdom
        · exact False
    isValidProp := by
      intro x hxXY
      rw [MySet.mem_union X Y x] at hxXY
      rcases hxXY with (hxX | hxY)
      · have hxfdom : x ∈ MyFun.domain f := by
          rw [hfdom]
          exact hxX
        use (MyFun.eval f x hxfdom)
        constructor
        · rw [← hfcodom]
          exact MyFun.eval_codomain f x hxfdom
        · constructor
          · dsimp only [MyFun.prop]
            rw [dif_pos hxX]
          · intro y' hy'Z h
            rw [dif_pos hxX] at h
            rw [h]
      · have hxgdom : x ∈ MyFun.domain g := by
          rw [hgdom]
          exact hxY
        use (MyFun.eval g x hxgdom)
        constructor
        · rw [← hgcodom]
          exact MyFun.eval_codomain g x hxgdom
        · have hxnX : ¬ x ∈ X := by
            intro hxX
            have hxXY :
                x ∈ X ∩ Y := by
              dsimp only [MySet.inter]
              rw [MySet.mem_spec X (fun x => x ∈ Y) x]
              constructor
              · exact hxX
              · exact hxY
            dsimp only [MySet.disjoint] at hXY
            rw [hXY] at hxXY
            exact MySet.not_mem_empty x hxXY
          constructor
          · dsimp only [MyFun.prop]
            rw [dif_neg hxnX]
            rw [dif_pos hxY]
          · intro y' hy'Z h
            rw [dif_neg hxnX] at h
            rw [dif_pos hxY] at h
            rw [h]
  }
  have hhdom :
      MyFun.domain h = X ∪ Y := by
    dsimp only [h]
  use h, hhdom
  have hXXY :
      X ⊆ X ∪ Y :=
    aux₁ X Y
  have hYXY :
      Y ⊆ X ∪ Y :=
    aux₂ X Y
  constructor
  · dsimp only [h]
  · constructor
    · dsimp only [MyFun.eq]
      constructor
      · dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        exact Eq.symm hfdom
      · constructor
        · dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
          dsimp only [h]
          exact Eq.symm hfcodom
        · intro x hxhXXYdom hxfdom
          have hXXYcodomhdom :
              (MyFun.codomain (ι X (X ∪ Y) hXXY)) = MyFun.domain h := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
          have hxXXYdom :
              x ∈ (MyFun.domain (ι X (X ∪ Y) hXXY)) := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
            rw [← hfdom]
            exact hxfdom
          have hXXYxhdom :
              (MyFun.eval (ι X (X ∪ Y) hXXY)) x hxXXYdom ∈ MyFun.domain h := by
            have hdomeq :
                MyFun.domain h = (MyFun.codomain (ι X (X ∪ Y) hXXY)) := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            rw [hdomeq]
            exact MyFun.eval_codomain (ι X (X ∪ Y) hXXY) x hxXXYdom
          rw [MyFun.comp.eval (ι X (X ∪ Y) hXXY) h hXXYcodomhdom
            x hxXXYdom hXXYxhdom hxhXXYdom]
          have hxhdom :
              x ∈ MyFun.domain h := by
            dsimp only [h]
            rw [MySet.mem_union X Y x]
            rw [hfdom] at hxfdom
            exact Or.inl hxfdom
          have hheval :
              MyFun.eval h ((MyFun.eval (ι X (X ∪ Y) hXXY)) x hxXXYdom) hXXYxhdom =
                MyFun.eval h x hxhdom := by
            have hιeval :
                (MyFun.eval (ι X (X ∪ Y) hXXY)) x hxXXYdom = x := by
              dsimp only [ι]
              rw [MyFun.from_fun.eval X (X ∪ Y) (fun x _ => x) (fun x hx => hXXY x hx)
                x hxXXYdom]
            exact MyFun.substitute h
              ((MyFun.eval (ι X (X ∪ Y) hXXY)) x hxXXYdom) x hXXYxhdom hxhdom hιeval
          rw [hheval]
          have hfxhcodom :
              MyFun.eval f x hxfdom ∈ MyFun.codomain h := by
            have hcodeq :
                MyFun.codomain h = MyFun.codomain f := by
              dsimp only [h]
              exact Eq.symm hfcodom
            rw [hcodeq]
            exact MyFun.eval_codomain f x hxfdom
          have hprop :
              MyFun.prop h x (MyFun.eval f x hxfdom) := by
            dsimp only [h]
            have hxX :
                x ∈ X := by
              rw [hfdom] at hxfdom
              exact hxfdom
            rw [dif_pos hxX]
          have hfeq :
              MyFun.eval f x hxfdom = MyFun.eval h x hxhdom :=
            Iff.mpr (MyFun.def h x (MyFun.eval f x hxfdom) hxhdom hfxhcodom) hprop
          exact Eq.symm hfeq
    · dsimp only [MyFun.eq]
      constructor
      · constructor
        · dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
          dsimp only [ι]
          dsimp only [MyFun.from_fun]
          exact Eq.symm hgdom
        · constructor
          · dsimp only [MyFun.comp]
            dsimp only [MyFun.from_fun]
            dsimp only [h]
            exact Eq.symm hgcodom
          · intro x hxhYXYdom hxgdom
            have hYXYcodomhdom :
                (MyFun.codomain (ι Y (X ∪ Y) hYXY)) = MyFun.domain h := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            have hxYXYdom :
                x ∈ (MyFun.domain (ι Y (X ∪ Y) hYXY)) := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
              rw [← hgdom]
              exact hxgdom
            have hYXYxhdom :
                (MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxYXYdom ∈ MyFun.domain h := by
              have hdomeq :
                  MyFun.domain h = (MyFun.codomain (ι Y (X ∪ Y) hYXY)) := by
                dsimp only [ι]
                dsimp only [MyFun.from_fun]
              rw [hdomeq]
              exact MyFun.eval_codomain (ι Y (X ∪ Y) hYXY) x hxYXYdom
            rw [MyFun.comp.eval (ι Y (X ∪ Y) hYXY) h hYXYcodomhdom
              x hxYXYdom hYXYxhdom hxhYXYdom]
            have hxhdom :
                x ∈ MyFun.domain h := by
              dsimp only [h]
              rw [MySet.mem_union X Y x]
              rw [hgdom] at hxgdom
              exact Or.inr hxgdom
            have hheval :
                MyFun.eval h ((MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxYXYdom) hYXYxhdom =
                  MyFun.eval h x hxhdom := by
              have hιeval :
                  (MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxYXYdom = x := by
                dsimp only [ι]
                rw [MyFun.from_fun.eval Y (X ∪ Y) (fun x _ => x) (fun x hx => hYXY x hx)
                x hxYXYdom]
              exact MyFun.substitute h
                ((MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxYXYdom) x hYXYxhdom hxhdom hιeval
            rw [hheval]
            have hxgxhcodom :
                MyFun.eval g x hxgdom ∈ MyFun.codomain h := by
              have hcodeq :
                  MyFun.codomain h = MyFun.codomain g := by
                dsimp only [h]
                exact Eq.symm hgcodom
              rw [hcodeq]
              exact MyFun.eval_codomain g x hxgdom
            have hprop :
                MyFun.prop h x (MyFun.eval g x hxgdom) := by
              dsimp only [h]
              have hxY :
                  x ∈ Y := by
                rw [hgdom] at hxgdom
                exact hxgdom
              have hxnX :
                  ¬ x ∈ X := by
                intro hxX
                have hxXY :
                    x ∈ X ∩ Y := by
                  dsimp only [MySet.inter]
                  rw [MySet.mem_spec X (fun x => x ∈ Y) x]
                  constructor
                  · exact hxX
                  · exact hxY
                dsimp only [MySet.disjoint] at hXY
                rw [hXY] at hxXY
                exact MySet.not_mem_empty x hxXY
              rw [dif_neg hxnX]
              rw [dif_pos hxY]
            have hgeq :
                MyFun.eval g x hxgdom = MyFun.eval h x hxhdom :=
              Iff.mpr (MyFun.def h x (MyFun.eval g x hxgdom) hxhdom hxgxhcodom) hprop
            exact Eq.symm hgeq
      · intro h' hh'dom hh'codom hh'f hh'g
        constructor
        · dsimp only [h]
          exact hh'dom
        · constructor
          · dsimp only [h]
            exact hh'codom
          · intro x hxh'dom hxhdom
            have hprop :
                MyFun.prop h x (MyFun.eval h' x hxh'dom) := by
              dsimp only [h]
              by_cases hxX : x ∈ X
              · rw [dif_pos hxX]
                rcases hh'f with ⟨hh'XXYdomfdom, hh'XXYcodomfcodom, hh'XXYxfx⟩
                have hXXYcodomh'dom :
                    (MyFun.codomain (ι X (X ∪ Y) hXXY)) = MyFun.domain h' := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact Eq.symm hh'dom
                have hxh'XXY :
                    x ∈ (MyFun.domain ((MyFun.comp (ι X (X ∪ Y) hXXY)) h' hXXYcodomh'dom)) := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxX
                have hxfdom :
                    x ∈ MyFun.domain f := by
                  rw [hfdom]
                  exact hxX
                have hcompeq :
                    (MyFun.eval ((MyFun.comp (ι X (X ∪ Y) hXXY)) h' hXXYcodomh'dom)) x hxh'XXY =
                      MyFun.eval f x hxfdom :=
                  hh'XXYxfx x hxh'XXY hxfdom
                rw [← hcompeq]
                have hXXYxh'dom :
                    (MyFun.eval (ι X (X ∪ Y) hXXY)) x hxh'XXY ∈ MyFun.domain h' := by
                  have hdomeq :
                      MyFun.domain h' = (MyFun.codomain (ι X (X ∪ Y) hXXY)) := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [hdomeq]
                  exact MyFun.eval_codomain (ι X (X ∪ Y) hXXY) x hxh'XXY
                rw [MyFun.comp.eval (ι X (X ∪ Y) hXXY) h' hXXYcodomh'dom
                  x hxh'XXY hXXYxh'dom hxh'XXY]
                have hxeval :
                    x = (MyFun.eval (ι X (X ∪ Y) hXXY)) x hxh'XXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval X (X ∪ Y) (fun x _ => x)
                    (fun x hx => hXXY x hx) x hxh'XXY]
                exact MyFun.substitute h' x ((MyFun.eval (ι X (X ∪ Y) hXXY)) x hxh'XXY)
                  hxh'dom hXXYxh'dom hxeval
              · rw [dif_neg hxX]
                have hxY :
                    x ∈ Y := by
                  rw [hh'dom] at hxh'dom
                  rw [MySet.mem_union X Y x] at hxh'dom
                  rcases hxh'dom with (hxX' | hxY')
                  · exact absurd hxX' hxX
                  · exact hxY'
                rw [dif_pos hxY]
                rcases hh'g with ⟨hh'YXYdomgdom, hh'YXYcodomgcodom, hh'YXYxgx⟩
                have hYXYcodomh'dom :
                    (MyFun.codomain (ι Y (X ∪ Y) hYXY)) = MyFun.domain h' := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact Eq.symm hh'dom
                have hxh'YXY :
                    x ∈ (MyFun.domain ((MyFun.comp (ι Y (X ∪ Y) hYXY)) h' hYXYcodomh'dom)) := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxY
                have hxgdom :
                    x ∈ MyFun.domain g := by
                  rw [hgdom]
                  exact hxY
                have hcompeq :
                    (MyFun.eval ((MyFun.comp (ι Y (X ∪ Y) hYXY)) h' hYXYcodomh'dom)) x hxh'YXY =
                      MyFun.eval g x hxgdom :=
                  hh'YXYxgx x hxh'YXY hxgdom
                rw [← hcompeq]
                have hYXYxh'dom :
                    (MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxh'YXY ∈ MyFun.domain h' := by
                  have hdomeq :
                      MyFun.domain h' = (MyFun.codomain (ι Y (X ∪ Y) hYXY)) := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [hdomeq]
                  exact MyFun.eval_codomain (ι Y (X ∪ Y) hYXY) x hxh'YXY
                rw [MyFun.comp.eval (ι Y (X ∪ Y) hYXY) h' hYXYcodomh'dom
                  x hxh'YXY hYXYxh'dom hxh'YXY]
                have hxeval :
                    x = (MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxh'YXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval Y (X ∪ Y) (fun x _ => x)
                    (fun x hx => hYXY x hx) x hxh'YXY]
                exact MyFun.substitute h' x ((MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxh'YXY)
                  hxh'dom hYXYxh'dom hxeval
            have hh'xhcodom : MyFun.eval h' x hxh'dom ∈ MyFun.codomain h := by
              have hcodeq :
                  MyFun.codomain h = MyFun.codomain h' := by
                dsimp only [h]
                exact Eq.symm hh'codom
              rw [hcodeq]
              exact MyFun.eval_codomain h' x hxh'dom
            refine Iff.mpr (MyFun.def h x (MyFun.eval h' x hxh'dom) hxhdom hh'xhcodom) hprop

end Exercise_3_3_8_d

-- (e)
namespace Exercise_3_3_8_e

open Exercise_3_3_8_d

theorem aux₅
    {α β : Type}
    (x : α)
    (X Y : MySet α)
    (f : MyFun α β)
    (hfdom : MyFun.domain f = X)
    (hxXY : x ∈ X ∩ Y) :
    x ∈ MyFun.domain f := by
  rw [MySet.mem_inter X Y x] at hxXY
  rw [hfdom]
  exact And.left hxXY

theorem aux₆
    {α β : Type}
    (x : α)
    (X Y : MySet α)
    (g : MyFun α β)
    (hgdom : MyFun.domain g = Y)
    (hxXY : x ∈ X ∩ Y) :
    x ∈ MyFun.domain g := by
  rw [MySet.mem_inter X Y x] at hxXY
  rw [hgdom]
  exact And.right hxXY

example
    (X Y : MySet α)
    (Z : MySet β)
    (f : MyFun α β)
    (hfdom : MyFun.domain f = X)
    (hfcodom : MyFun.codomain f = Z)
    (g : MyFun α β)
    (hgdom : MyFun.domain g = Y)
    (hgcodom : MyFun.codomain g = Z)
    (hfg : ∀ (x : α) (hx : x ∈ X ∩ Y),
      MyFun.eval f x (aux₅ x X Y f hfdom hx) =
        MyFun.eval g x (aux₆ x X Y g hgdom hx)) :
    ∃ (h : MyFun α β) (hhdom : MyFun.domain h = X ∪ Y),
    MyFun.codomain h = Z ∧
    ((MyFun.comp (ι X (X ∪ Y) (aux₁ X Y))) h (aux₃ X Y h hhdom) ≃ f) ∧
    ((MyFun.comp (ι Y (X ∪ Y) (aux₂ X Y))) h (aux₄ X Y h hhdom) ≃ g) ∧
    (∀ (h' : MyFun α β) (hh'dom : MyFun.domain h' = X ∪ Y),
      MyFun.codomain h' = Z →
      ((MyFun.comp (ι X (X ∪ Y) (aux₁ X Y))) h' (aux₃ X Y h' hh'dom) ≃ f) →
      ((MyFun.comp (ι Y (X ∪ Y) (aux₂ X Y))) h' (aux₄ X Y h' hh'dom) ≃ g) →
        h' ≃ h) := by
  let h :
      MyFun α β :=
    {
    domain := X ∪ Y,
    codomain := Z,
    prop := fun x y => by
      by_cases h : x ∈ X
      · have hxfdom : x ∈ MyFun.domain f := by
          rw [hfdom]
          exact h
        exact y = MyFun.eval f x hxfdom
      · by_cases h' : x ∈ Y
        · have hxgdom : x ∈ MyFun.domain g := by
            rw [hgdom]
            exact h'
          exact y = MyFun.eval g x hxgdom
        · exact False
    isValidProp := by
      intro x hxXY
      rw [MySet.mem_union X Y x] at hxXY
      rcases hxXY with (hxX | hxY)
      · have hxfdom : x ∈ MyFun.domain f := by
          rw [hfdom]
          exact hxX
        use (MyFun.eval f x hxfdom)
        constructor
        · rw [← hfcodom]
          exact MyFun.eval_codomain f x hxfdom
        · constructor
          · dsimp only [MyFun.prop]
            rw [dif_pos hxX]
          · intro y' hy'Z h
            rw [dif_pos hxX] at h
            rw [h]
      · have hxgdom : x ∈ MyFun.domain g := by
          rw [hgdom]
          exact hxY
        use (MyFun.eval g x hxgdom)
        constructor
        · rw [← hgcodom]
          exact MyFun.eval_codomain g x hxgdom
        · constructor
          · dsimp only [MyFun.prop]
            rw [dif_pos hxY]
            by_cases hxX : x ∈ X
            · rw [dif_pos hxX]
              have hxXY :
                  x ∈ X ∩ Y := by
                dsimp only [MySet.inter]
                rw [MySet.mem_spec X (fun x => x ∈ Y) x]
                constructor
                · exact hxX
                · exact hxY
              exact Eq.symm (hfg x hxXY)
            · rw [dif_neg hxX]
          · intro y' hy'Z h
            rw [dif_pos hxY] at h
            by_cases hxX : x ∈ X
            · rw [dif_pos hxX] at h
              have hxXY :
                  x ∈ X ∩ Y := by
                dsimp only [MySet.inter]
                rw [MySet.mem_spec X (fun x => x ∈ Y) x]
                constructor
                · exact hxX
                · exact hxY
              rw [h]
              exact Eq.symm (hfg x hxXY)
            · rw [dif_neg hxX] at h
              exact Eq.symm h
  }
  have hhdom :
      MyFun.domain h = X ∪ Y := by
    dsimp only [h]
  use h, hhdom
  have hXXY :
      X ⊆ X ∪ Y :=
    aux₁ X Y
  have hYXY :
      Y ⊆ X ∪ Y :=
    aux₂ X Y
  constructor
  · dsimp only [h]
  · constructor
    · dsimp only [MyFun.eq]
      constructor
      · dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        exact Eq.symm hfdom
      · constructor
        · dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
          dsimp only [h]
          exact Eq.symm hfcodom
        · intro x hxhXXYdom hxfdom
          have hXXYcodomhdom :
              (MyFun.codomain (ι X (X ∪ Y) hXXY)) = MyFun.domain h := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
          have hxXXYdom :
              x ∈ (MyFun.domain (ι X (X ∪ Y) hXXY)) := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
            rw [← hfdom]
            exact hxfdom
          have hXXYxhdom :
              (MyFun.eval (ι X (X ∪ Y) hXXY)) x hxXXYdom ∈ MyFun.domain h := by
            have hdomeq :
                MyFun.domain h = (MyFun.codomain (ι X (X ∪ Y) hXXY)) := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            rw [hdomeq]
            exact MyFun.eval_codomain (ι X (X ∪ Y) hXXY) x hxXXYdom
          rw [MyFun.comp.eval (ι X (X ∪ Y) hXXY) h hXXYcodomhdom
            x hxXXYdom hXXYxhdom hxhXXYdom]
          have hxhdom :
              x ∈ MyFun.domain h := by
            dsimp only [h]
            rw [MySet.mem_union X Y x]
            rw [hfdom] at hxfdom
            exact Or.inl hxfdom
          have hheval :
              MyFun.eval h ((MyFun.eval (ι X (X ∪ Y) hXXY)) x hxXXYdom) hXXYxhdom =
                MyFun.eval h x hxhdom := by
            have hιeval :
                (MyFun.eval (ι X (X ∪ Y) hXXY)) x hxXXYdom = x := by
              dsimp only [ι]
              rw [MyFun.from_fun.eval X (X ∪ Y) (fun x _ => x) (fun x hx => hXXY x hx)
                x hxXXYdom]
            exact MyFun.substitute h
              ((MyFun.eval (ι X (X ∪ Y) hXXY)) x hxXXYdom) x hXXYxhdom hxhdom hιeval
          rw [hheval]
          have hfxhcodom :
              MyFun.eval f x hxfdom ∈ MyFun.codomain h := by
            have hcodeq :
                MyFun.codomain h = MyFun.codomain f := by
              dsimp only [h]
              exact Eq.symm hfcodom
            rw [hcodeq]
            exact MyFun.eval_codomain f x hxfdom
          have hprop :
              MyFun.prop h x (MyFun.eval f x hxfdom) := by
            dsimp only [h]
            have hxX :
                x ∈ X := by
              rw [hfdom] at hxfdom
              exact hxfdom
            rw [dif_pos hxX]
          have hfeq :
              MyFun.eval f x hxfdom = MyFun.eval h x hxhdom :=
            Iff.mpr (MyFun.def h x (MyFun.eval f x hxfdom) hxhdom hfxhcodom) hprop
          exact Eq.symm hfeq
    · dsimp only [MyFun.eq]
      constructor
      · constructor
        · dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
          dsimp only [ι]
          dsimp only [MyFun.from_fun]
          exact Eq.symm hgdom
        · constructor
          · dsimp only [MyFun.comp]
            dsimp only [MyFun.from_fun]
            dsimp only [h]
            exact Eq.symm hgcodom
          · intro x hxhYXYdom hxgdom
            have hYXYcodomhdom :
                (MyFun.codomain (ι Y (X ∪ Y) hYXY)) = MyFun.domain h := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            have hxYXYdom :
                x ∈ (MyFun.domain (ι Y (X ∪ Y) hYXY)) := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
              rw [← hgdom]
              exact hxgdom
            have hYXYxhdom :
                (MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxYXYdom ∈ MyFun.domain h := by
              have hdomeq :
                  MyFun.domain h = (MyFun.codomain (ι Y (X ∪ Y) hYXY)) := by
                dsimp only [ι]
                dsimp only [MyFun.from_fun]
              rw [hdomeq]
              exact MyFun.eval_codomain (ι Y (X ∪ Y) hYXY) x hxYXYdom
            rw [MyFun.comp.eval (ι Y (X ∪ Y) hYXY) h hYXYcodomhdom
              x hxYXYdom hYXYxhdom hxhYXYdom]
            have hxhdom :
                x ∈ MyFun.domain h := by
              dsimp only [h]
              rw [MySet.mem_union X Y x]
              rw [hgdom] at hxgdom
              exact Or.inr hxgdom
            have hheval :
                MyFun.eval h ((MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxYXYdom) hYXYxhdom =
                  MyFun.eval h x hxhdom := by
              have hιeval :
                  (MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxYXYdom = x := by
                dsimp only [ι]
                rw [MyFun.from_fun.eval Y (X ∪ Y) (fun x _ => x) (fun x hx => hYXY x hx)
                x hxYXYdom]
              exact MyFun.substitute h
                ((MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxYXYdom) x hYXYxhdom hxhdom hιeval
            rw [hheval]
            have hxgxhcodom :
                MyFun.eval g x hxgdom ∈ MyFun.codomain h := by
              have hcodeq :
                  MyFun.codomain h = MyFun.codomain g := by
                dsimp only [h]
                exact Eq.symm hgcodom
              rw [hcodeq]
              exact MyFun.eval_codomain g x hxgdom
            have hprop :
                MyFun.prop h x (MyFun.eval g x hxgdom) := by
              dsimp only [h]
              have hxY :
                  x ∈ Y := by
                rw [hgdom] at hxgdom
                exact hxgdom
              by_cases hxX : x ∈ X
              · rw [dif_pos hxX]
                have hxXY :
                    x ∈ X ∩ Y := by
                  dsimp only [MySet.inter]
                  rw [MySet.mem_spec X (fun x => x ∈ Y) x]
                  constructor
                  · exact hxX
                  · exact hxY
                exact Eq.symm (hfg x hxXY)
              · rw [dif_neg hxX]
                rw [dif_pos hxY]
            have hgeq :
                MyFun.eval g x hxgdom = MyFun.eval h x hxhdom :=
              Iff.mpr (MyFun.def h x (MyFun.eval g x hxgdom) hxhdom hxgxhcodom) hprop
            exact Eq.symm hgeq
      · intro h' hh'dom hh'codom hh'f hh'g
        constructor
        · dsimp only [h]
          exact hh'dom
        · constructor
          · dsimp only [h]
            exact hh'codom
          · intro x hxh'dom hxhdom
            have hprop :
                MyFun.prop h x (MyFun.eval h' x hxh'dom) := by
              dsimp only [h]
              by_cases hxX : x ∈ X
              · rw [dif_pos hxX]
                rcases hh'f with ⟨hh'XXYdomfdom, hh'XXYcodomfcodom, hh'XXYxfx⟩
                have hXXYcodomh'dom :
                    (MyFun.codomain (ι X (X ∪ Y) hXXY)) = MyFun.domain h' := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact Eq.symm hh'dom
                have hxh'XXY :
                    x ∈ (MyFun.domain ((MyFun.comp (ι X (X ∪ Y) hXXY)) h' hXXYcodomh'dom)) := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxX
                have hxfdom :
                    x ∈ MyFun.domain f := by
                  rw [hfdom]
                  exact hxX
                have hcompeq :
                    (MyFun.eval ((MyFun.comp (ι X (X ∪ Y) hXXY)) h' hXXYcodomh'dom)) x hxh'XXY =
                      MyFun.eval f x hxfdom :=
                  hh'XXYxfx x hxh'XXY hxfdom
                rw [← hcompeq]
                have hXXYxh'dom :
                    (MyFun.eval (ι X (X ∪ Y) hXXY)) x hxh'XXY ∈ MyFun.domain h' := by
                  have hdomeq :
                      MyFun.domain h' = (MyFun.codomain (ι X (X ∪ Y) hXXY)) := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [hdomeq]
                  exact MyFun.eval_codomain (ι X (X ∪ Y) hXXY) x hxh'XXY
                rw [MyFun.comp.eval (ι X (X ∪ Y) hXXY) h' hXXYcodomh'dom
                  x hxh'XXY hXXYxh'dom hxh'XXY]
                have hxeval :
                    x = (MyFun.eval (ι X (X ∪ Y) hXXY)) x hxh'XXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval X (X ∪ Y) (fun x _ => x)
                    (fun x hx => hXXY x hx) x hxh'XXY]
                exact MyFun.substitute h' x ((MyFun.eval (ι X (X ∪ Y) hXXY)) x hxh'XXY)
                  hxh'dom hXXYxh'dom hxeval
              · rw [dif_neg hxX]
                have hxY :
                    x ∈ Y := by
                  rw [hh'dom] at hxh'dom
                  rw [MySet.mem_union X Y x] at hxh'dom
                  rcases hxh'dom with (hxX' | hxY')
                  · exact absurd hxX' hxX
                  · exact hxY'
                rw [dif_pos hxY]
                rcases hh'g with ⟨hh'YXYdomgdom, hh'YXYcodomgcodom, hh'YXYxgx⟩
                have hYXYcodomh'dom :
                    (MyFun.codomain (ι Y (X ∪ Y) hYXY)) = MyFun.domain h' := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact Eq.symm hh'dom
                have hxh'YXY :
                    x ∈ (MyFun.domain ((MyFun.comp (ι Y (X ∪ Y) hYXY)) h' hYXYcodomh'dom)) := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxY
                have hxgdom :
                    x ∈ MyFun.domain g := by
                  rw [hgdom]
                  exact hxY
                have hcompeq :
                    (MyFun.eval ((MyFun.comp (ι Y (X ∪ Y) hYXY)) h' hYXYcodomh'dom)) x hxh'YXY =
                      MyFun.eval g x hxgdom :=
                  hh'YXYxgx x hxh'YXY hxgdom
                rw [← hcompeq]
                have hYXYxh'dom :
                    (MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxh'YXY ∈ MyFun.domain h' := by
                  have hdomeq :
                      MyFun.domain h' = (MyFun.codomain (ι Y (X ∪ Y) hYXY)) := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [hdomeq]
                  exact MyFun.eval_codomain (ι Y (X ∪ Y) hYXY) x hxh'YXY
                rw [MyFun.comp.eval (ι Y (X ∪ Y) hYXY) h' hYXYcodomh'dom
                  x hxh'YXY hYXYxh'dom hxh'YXY]
                have hxeval :
                    x = (MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxh'YXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval Y (X ∪ Y) (fun x _ => x)
                    (fun x hx => hYXY x hx) x hxh'YXY]
                exact MyFun.substitute h' x ((MyFun.eval (ι Y (X ∪ Y) hYXY)) x hxh'YXY)
                  hxh'dom hYXYxh'dom hxeval
            have hh'xhcodom : MyFun.eval h' x hxh'dom ∈ MyFun.codomain h := by
              have hcodeq :
                  MyFun.codomain h = MyFun.codomain h' := by
                dsimp only [h]
                exact Eq.symm hh'codom
              rw [hcodeq]
              exact MyFun.eval_codomain h' x hxh'dom
            refine Iff.mpr (MyFun.def h x (MyFun.eval h' x hxh'dom) hxhdom hh'xhcodom) hprop

end Exercise_3_3_8_e

end Exercise_3_3_8

end Exercises -- section Exercises
