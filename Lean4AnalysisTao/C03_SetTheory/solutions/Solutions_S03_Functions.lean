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
          x ∈ g.domain := by
        rw [← hdomfg]
        exact hxf
      rw [hfg x hxf hxg]
      exact hgh x hxg hxh

example
    (f f' : MyFun α β)
    (g g' : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hf'g' : f'.codomain = g'.domain)
    (hff' : f ≃ f')
    (hgg' : g ≃ g') :
    f.comp g hfg ≃ f'.comp g' hf'g' := by
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
          (hx : x ∈ f.domain) :
          f.eval x hx ∈ g.domain := by
        rw [← hfg]
        exact MyFun.eval_codomain f x hx
      have hauxf'
          (x : α)
          (hx : x ∈ f'.domain) :
          f'.eval x hx ∈ g'.domain := by
        rw [← hf'g']
        exact MyFun.eval_codomain f' x hx
      have hgfcodom
          (x : α)
          (hx : x ∈ f.domain) :
          g.eval (f.eval x hx) (hauxf x hx) ∈ g.codomain := by
        exact MyFun.eval_codomain g (f.eval x hx) (hauxf x hx)
      have hg'f'codom
          (x : α)
          (hx : x ∈ f'.domain) :
          g'.eval (f'.eval x hx) (hauxf' x hx) ∈ g'.codomain := by
        exact MyFun.eval_codomain g' (f'.eval x hx) (hauxf' x hx)
      rw [MyFun.from_fun.eval f.domain g.codomain
        (fun x h => g.eval (f.eval x h) (hauxf x h)) hgfcodom x hxf]
      rw [MyFun.from_fun.eval f'.domain g'.codomain
        (fun x h => g'.eval (f'.eval x h) (hauxf' x h)) hg'f'codom x hxf']
      dsimp only [MyFun.comp] at hxf
      dsimp only [MyFun.from_fun] at hxf
      dsimp only [MyFun.comp] at hxf'
      dsimp only [MyFun.from_fun] at hxf'
      have hfxg :
          f.eval x hxf ∈ g.domain := by
        rw [← hfg]
        exact MyFun.eval_codomain f x hxf
      have hfxg' : f.eval x hxf ∈ g'.domain := by
        rw [← hf'g']
        rw [← hcodomff']
        exact MyFun.eval_codomain f x hxf
      have hfxfx' : f.eval x hxf = f'.eval x hxf' :=
        hff' x hxf hxf'
      have hgfxg'fx :
          g.eval (f.eval x hxf) hfxg = g'.eval (f.eval x hxf) hfxg' :=
        hgg' (f.eval x hxf) hfxg hfxg'
      rw [hgfxg'fx]
      have hf'xg' : f'.eval x hxf' ∈ g'.domain := by
        rw [← hf'g']
        exact MyFun.eval_codomain f' x hxf'
      exact MyFun.substitute g' (f.eval x hxf) (f'.eval x hxf')
        hfxg' hf'xg' hfxfx'

-- Exercise 3.3.2
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hfinj : f.isInjective)
    (hginj : g.isInjective) :
    (f.comp g hfg).isInjective := by
  dsimp only [MyFun.isInjective] at hfinj
  dsimp only [MyFun.isInjective] at hginj
  dsimp only [MyFun.isInjective]
  intro x x' hxgfdom hx'gfdom hxx'
  dsimp only [MyFun.comp] at hxgfdom
  dsimp only [MyFun.from_fun] at hxgfdom
  dsimp only [MyFun.comp] at hx'gfdom
  dsimp only [MyFun.from_fun] at hx'gfdom
  have hfxgdom :
      f.eval x hxgfdom ∈ g.domain := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hxgfdom
  rw [MyFun.comp.eval f g hfg x hxgfdom hfxgdom hxgfdom]
  have hfx'gdom : f.eval x' hx'gfdom ∈ g.domain := by
    rw [← hfg]
    exact MyFun.eval_codomain f x' hx'gfdom
  rw [MyFun.comp.eval f g hfg x' hx'gfdom hfx'gdom hx'gfdom]
  exact hginj (f.eval x hxgfdom) (f.eval x' hx'gfdom) hfxgdom hfx'gdom
    (hfinj x x' hxgfdom hx'gfdom hxx')

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hfsurj : f.isSurjective)
    (hgsurj : g.isSurjective) :
    (f.comp g hfg).isSurjective := by
  dsimp only [MyFun.isSurjective] at hfsurj
  dsimp only [MyFun.isSurjective] at hgsurj
  dsimp only [MyFun.isSurjective]
  intro z hz
  dsimp only [MyFun.comp] at hz
  dsimp only [MyFun.from_fun] at hz
  rcases hgsurj z hz with ⟨y, hy, hgyz⟩
  have hyfcodom :
      y ∈ f.codomain := by
    rw [hfg]
    exact hy
  rcases hfsurj y hyfcodom with ⟨x, hx, hfx⟩
  use x, hx
  have hfxgdom :
      f.eval x hx ∈ g.domain := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hx
  rw [MyFun.comp.eval f g hfg x hx hfxgdom hx]
  rw [← hgyz]
  exact MyFun.substitute g (f.eval x hx) y hfxgdom hy hfx

-- Exercise 3.3.3
-- TODO: When is the empty function into a given set X injective? surjective? bijective?

-- Exercise 3.3.4
example
    (f f' : MyFun α β)
    (g : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hf'g : f'.codomain = g.domain)
    (hgfgf' : f.comp g hfg ≃ f'.comp g hf'g)
    (hginj : g.isInjective) :
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
          x ∈ (f.comp g hfg).domain := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxf
      have hxgf'dom : x ∈ (f'.comp g hf'g).domain := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxf'
      have hgfxgf'x :
          (f.comp g hfg).eval x hxgfdom =
            (f'.comp g hf'g).eval x hxgf'dom :=
        hgfgf' x hxgfdom hxgf'dom
      have hfxgdom :
          f.eval x hxf ∈ g.domain := by
        rw [← hfg]
        exact MyFun.eval_codomain f x hxf
      rw [MyFun.comp.eval f g hfg x hxf hfxgdom hxgfdom] at hgfxgf'x
      have hfx'gdom : f'.eval x hxf' ∈ g.domain := by
        rw [← hf'g]
        exact MyFun.eval_codomain f' x hxf'
      rw [MyFun.comp.eval f' g hf'g x hxf' hfx'gdom hxgf'dom] at hgfxgf'x
      rw [MyFun.isInjective_iff g] at hginj
      dsimp only [MyFun.isInjective'] at hginj
      exact hginj (f.eval x hxf) (f'.eval x hxf') hfxgdom hfx'gdom hgfxgf'x

-- TODO: Is the same statement true if g is not injective?

example
    (f : MyFun α β)
    (g g' : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hfg' : f.codomain = g'.domain)
    (hgfg'f : f.comp g hfg ≃ f.comp g' hfg')
    (hfsurj : f.isSurjective) :
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
          y ∈ f.codomain := by
        rw [hfg]
        exact hygdom
      rcases hfsurj y hyfcodom with ⟨x, hxf, hfy⟩
      have hfxgdom :
          f.eval x hxf ∈ g.domain := by
        rw [← hfg]
        exact MyFun.eval_codomain f x hxf
      have hfxg'dom : f.eval x hxf ∈ g'.domain := by
        rw [← hfg']
        exact MyFun.eval_codomain f x hxf
      have hgfxg'fx :
          (f.comp g hfg).eval x hxf =
            (f.comp g' hfg').eval x hxf :=
        hgfg'f x hxf hxf
      rw [MyFun.comp.eval f g hfg x hxf hfxgdom hxf] at hgfxg'fx
      rw [MyFun.comp.eval f g' hfg' x hxf hfxg'dom hxf] at hgfxg'fx
      have hgfxgy :
          g.eval (f.eval x hxf) hfxgdom = g.eval y hygdom :=
        MyFun.substitute g (f.eval x hxf) y hfxgdom hygdom hfy
      have hg'fxg'y :
          g'.eval (f.eval x hxf) hfxg'dom = g'.eval y hyg'dom :=
        MyFun.substitute g' (f.eval x hxf) y hfxg'dom hyg'dom hfy
      rw [← hgfxgy]
      rw [← hg'fxg'y]
      exact hgfxg'fx

-- TODO: Is the same statement true if f is not surjective?

-- Exercise 3.3.5
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hgfinj : (f.comp g hfg).isInjective) :
    f.isInjective := by
  dsimp only [MyFun.isInjective] at hgfinj
  dsimp only [MyFun.isInjective]
  intro x x' hxfdom hx'fdom hxx'
  have hxgfdom :
      x ∈ (f.comp g hfg).domain := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hxfdom
  have hx'gfdom : x' ∈ (f.comp g hfg).domain := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hx'fdom
  have hgfxngfx' :
      (f.comp g hfg).eval x hxgfdom ≠ (f.comp g hfg).eval x' hx'gfdom :=
    hgfinj x x' hxgfdom hx'gfdom hxx'
  have hfxgdom :
      f.eval x hxfdom ∈ g.domain := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hxfdom
  have hfx'gdom : f.eval x' hx'fdom ∈ g.domain := by
    rw [← hfg]
    exact MyFun.eval_codomain f x' hx'fdom
  rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom] at hgfxngfx'
  rw [MyFun.comp.eval f g hfg x' hx'fdom hfx'gdom hx'gfdom] at hgfxngfx'
  intro hfxfx'
  have hgfxgfx' :
      g.eval (f.eval x hxfdom) hfxgdom
        = g.eval (f.eval x' hx'fdom) hfx'gdom :=
    MyFun.substitute g (f.eval x hxfdom) (f.eval x' hx'fdom)
      hfxgdom hfx'gdom hfxfx'
  exact hgfxngfx' hgfxgfx'

-- TODO: Is it true that g must also be injective?

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hgfsurj : (f.comp g hfg).isSurjective) :
    g.isSurjective := by
  dsimp only [MyFun.isSurjective] at hgfsurj
  dsimp only [MyFun.isSurjective]
  intro z hz
  have hzgfcodom :
      z ∈ (f.comp g hfg).codomain := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hz
  rcases hgfsurj z hzgfcodom with ⟨x, hxgfdom, hgfxz⟩
  have hxfdom :
      x ∈ f.domain := by
    dsimp only [MyFun.comp] at hxgfdom
    dsimp only [MyFun.from_fun] at hxgfdom
    exact hxgfdom
  have hfxgdom :
      f.eval x hxfdom ∈ g.domain := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hxfdom
  use (f.eval x hxfdom), hfxgdom
  rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom] at hgfxz
  exact hgfxz

-- TODO: Is it true that f must also be surjective?

-- Exercise 3.3.6
namespace Exercise_3_3_6

theorem aux₁
    (f : MyFun α β)
    (hf : f.isBijective) :
    f.codomain = (f.inv hf).domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

theorem finv_f
    (f : MyFun α β)
    (hf : f.isBijective)
    (x : α)
    (hxf : x ∈ f.domain) :
    (f.comp (f.inv hf) (aux₁ f hf)).eval x hxf = x := by
  have hffi :
      f.codomain = (f.inv hf).domain :=
    aux₁ f hf
  have hfxfidom :
      f.eval x hxf ∈ (f.inv hf).domain := by
    rw [← hffi]
    exact MyFun.eval_codomain f x hxf
  rw [MyFun.comp.eval f (f.inv hf) hffi x hxf hfxfidom hxf]
  dsimp only [MyFun.inv]
  let finv :
      (y : β) → y ∈ f.codomain → α :=
    fun y hy => MyClassical.choose
      (fun x => ∃ (hx : x ∈ f.domain), f.eval x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ f.domain), f.eval x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hy)
  have hfinvaux
      (y : β)
      (hy : y ∈ f.codomain) :
      finv y hy ∈ f.domain := by
    dsimp only [finv]
    rcases MyClassical.choose_spec
      (fun x => ∃ (hx : x ∈ f.domain), f.eval x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ f.domain), f.eval x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hy) with ⟨hx, h⟩
    exact hx
  rw [MyFun.from_fun.eval f.codomain f.domain finv hfinvaux (f.eval x hxf) hfxfidom]
  rcases MyClassical.choose_spec
      (fun x' => ∃ (hx' : x' ∈ f.domain), f.eval x' hx' = f.eval x hxf ∧
        ∀ (x'' : α) (hx'' : x'' ∈ f.domain),
          f.eval x'' hx'' = f.eval x hxf → x' = x'')
      (MyFun.exists_unique_of_bijective f hf (f.eval x hxf) hfxfidom)
    with ⟨hx, h, h'⟩
  exact h' x hxf rfl

theorem aux₂
    (f : MyFun α β)
    (hf : f.isBijective) :
    (f.inv hf).codomain = f.domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

theorem f_finv
    (f : MyFun α β)
    (hf : f.isBijective)
    (y : β)
    (hyfidom : y ∈ (f.inv hf).domain) :
    ((f.inv hf).comp f (aux₂ f hf)).eval y hyfidom = y := by
  have hffi :
      (f.inv hf).codomain = f.domain :=
    aux₂ f hf
  have hfiyfdom :
      (f.inv hf).eval y hyfidom ∈ f.domain := by
    rw [← hffi]
    exact MyFun.eval_codomain (f.inv hf) y hyfidom
  rw [MyFun.comp.eval (f.inv hf) f hffi y hyfidom hfiyfdom hyfidom]
  dsimp only [MyFun.inv] at hyfidom
  dsimp only [MyFun.from_fun] at hyfidom
  rcases MyClassical.choose_spec
      (fun x => ∃ (hx : x ∈ f.domain), f.eval x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ f.domain), f.eval x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hyfidom)
    with ⟨hx, h, h'⟩
  have hPfiyy :
      f.prop ((f.inv hf).eval y hyfidom) y := by
    dsimp only [MyFun.inv]
    let finv :
        (y : β) → y ∈ f.codomain → α :=
      fun y hy => MyClassical.choose
        (fun x => ∃ (hx : x ∈ f.domain), f.eval x hx = y ∧
          ∀ (x' : α) (hx' : x' ∈ f.domain), f.eval x' hx' = y → x = x')
        (MyFun.exists_unique_of_bijective f hf y hy)
    have hfinvaux
        (y : β)
        (hy : y ∈ f.codomain) :
        finv y hy ∈ f.domain := by
      dsimp only [finv]
      rcases MyClassical.choose_spec
        (fun x => ∃ (hx : x ∈ f.domain), f.eval x hx = y ∧
          ∀ (x' : α) (hx' : x' ∈ f.domain), f.eval x' hx' = y → x = x')
        (MyFun.exists_unique_of_bijective f hf y hy) with ⟨hx', h'⟩
      exact hx'
    rw [MyFun.from_fun.eval f.codomain f.domain finv hfinvaux y hyfidom]
    let hchosen :
        α :=
      MyClassical.choose
        (fun x => ∃ (hx : x ∈ f.domain), f.eval x hx = y ∧
          ∀ (x' : α) (hx' : x' ∈ f.domain), f.eval x' hx' = y → x = x')
        (MyFun.exists_unique_of_bijective f hf y hyfidom)
    have hfwd :
        y = f.eval hchosen hx →
          f.prop hchosen y :=
      Iff.mp (MyFun.def f hchosen y hx hyfidom)
    exact hfwd (Eq.symm h)
  have hfeq :
      y = f.eval ((f.inv hf).eval y hyfidom) hfiyfdom :=
    Iff.mpr (MyFun.def f ((f.inv hf).eval y hyfidom) y hfiyfdom hyfidom) hPfiyy
  exact Eq.symm hfeq

theorem finv_bij
    (f : MyFun α β)
    (hf : f.isBijective) :
    (f.inv hf).isBijective := by
  have hfcopy :
      f.isBijective :=
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
        y ∈ f.codomain := by
      dsimp only [MyFun.inv] at hy
      dsimp only [MyFun.from_fun] at hy
      exact hy
    rcases hsurj y hyfcodom with ⟨x, hxfdom, hfxy⟩
    have hy'fcodom : y' ∈ f.codomain := by
      dsimp only [MyFun.inv] at hy'
      dsimp only [MyFun.from_fun] at hy'
      exact hy'
    rcases hsurj y' hy'fcodom with ⟨x', hx'fdom, hfx'y'⟩
    have hfxfidom :
        (f.eval x hxfdom) ∈ (f.inv hf).domain := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact MyFun.eval_codomain f x hxfdom
    have hfiyfifx :
        (f.inv hf).eval y hy =
          (f.inv hf).eval (f.eval x hxfdom) hfxfidom :=
      MyFun.substitute (f.inv hf) y (f.eval x hxfdom) hy hfxfidom (Eq.symm hfxy)
    rw [hfiyfifx] at hfiyfiy'
    have hfx'fidom : (f.eval x' hx'fdom) ∈ (f.inv hf).domain := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact MyFun.eval_codomain f x' hx'fdom
    have hfiy'fifx' :
        (f.inv hf).eval y' hy' =
          (f.inv hf).eval (f.eval x' hx'fdom) hfx'fidom :=
      MyFun.substitute (f.inv hf) y' (f.eval x' hx'fdom) hy' hfx'fidom (Eq.symm hfx'y')
    rw [hfiy'fifx'] at hfiyfiy'
    have hxfifdom :
        x ∈ (f.comp (f.inv hf) (aux₁ f hf)).domain := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    rw [← MyFun.comp.eval f (f.inv hf) (aux₁ f hf) x hxfdom hfxfidom hxfifdom] at hfiyfiy'
    have hx'fifdom : x' ∈ (f.comp (f.inv hf) (aux₁ f hf)).domain := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hx'fdom
    rw [← MyFun.comp.eval f (f.inv hf) (aux₁ f hf) x' hx'fdom hfx'fidom hx'fifdom]
      at hfiyfiy'
    rw [finv_f f hf x hxfdom] at hfiyfiy'
    rw [finv_f f hf x' hx'fdom] at hfiyfiy'
    have hfxfx' : f.eval x hxfdom = f.eval x' hx'fdom :=
      MyFun.substitute f x x' hxfdom hx'fdom hfiyfiy'
    rw [hfxy] at hfxfx'
    rw [hfx'y'] at hfxfx'
    exact hyy' hfxfx'
  · dsimp only [MyFun.isSurjective]
    intro x hxficodom
    have hxfdom :
        x ∈ f.domain := by
      dsimp only [MyFun.inv]
      exact hxficodom
    use (f.eval x hxficodom)
    have hfxfidom :
        f.eval x hxfdom ∈ (f.inv hf).domain := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact MyFun.eval_codomain f x hxfdom
    use hfxfidom
    have hxfifdom :
        x ∈ (f.comp (f.inv hf) (aux₁ f hf)).domain := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    rw [← MyFun.comp.eval f (f.inv hf) (aux₁ f hf) x hxfdom hfxfidom hxfifdom]
    rw [finv_f f hf x hxfdom]

example
    (f : MyFun α β)
    (hf : f.isBijective) :
    (f.inv hf).inv (finv_bij f hf) ≃ f := by
  have hfi :
      (f.inv hf).isBijective :=
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
          ((f.inv hf).inv hfi).codomain = (f.inv hf).domain := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
      have hxfifiidom :
          x ∈ (((f.inv hf).inv hfi).comp (f.inv hf) hfiicodomfidom).domain := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxfiidom
      have hxfifdom :
          x ∈ (f.comp (f.inv hf) (aux₁ f hf)).domain := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxfdom
      have hfifiixfifx :
          (((f.inv hf).inv hfi).comp (f.inv hf) hfiicodomfidom).eval x hxfifiidom =
            (f.comp (f.inv hf) (aux₁ f hf)).eval x hxfifdom := by
        have hxfiidom2 :
            x ∈ ((f.inv hf).inv hfi).domain := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
          exact hxfiidom
        rw [f_finv (f.inv hf) hfi x hxfiidom]
        rw [finv_f f hf x hxfdom]
      have hfiixfidom :
          ((f.inv hf).inv hfi).eval x hxfifiidom ∈ (f.inv hf).domain := by
        have hfiixfiicodom :
            ((f.inv hf).inv hfi).eval x hxfifiidom ∈ ((f.inv hf).inv hfi).codomain :=
          MyFun.eval_codomain ((f.inv hf).inv hfi) x hxfifiidom
        have hfiicodomfidom' :
            ((f.inv hf).inv hfi).codomain = (f.inv hf).domain := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
        rw [← hfiicodomfidom']
        exact hfiixfiicodom
      have hfxfidom :
          f.eval x hxfifdom ∈ (f.inv hf).domain := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        exact MyFun.eval_codomain f x hxfdom
      rw [MyFun.comp.eval ((f.inv hf).inv hfi) (f.inv hf) hfiicodomfidom
        x hxfifiidom hfiixfidom hxfifiidom] at hfifiixfifx
      rw [MyFun.comp.eval f (f.inv hf) (aux₁ f hf) x hxfifdom hfxfidom hxfifdom]
        at hfifiixfifx
      have hficopy :
          (f.inv hf).isBijective :=
        hfi
      dsimp only [MyFun.isBijective] at hficopy
      rcases hficopy with ⟨hfi_inj, hfi_surj⟩
      rw [MyFun.isInjective_iff (f.inv hf)] at hfi_inj
      dsimp only [MyFun.isInjective'] at hfi_inj
      exact hfi_inj (((f.inv hf).inv hfi).eval x hxfifiidom) (f.eval x hxfifdom)
        hfiixfidom hfxfidom hfifiixfifx

end Exercise_3_3_6

-- Exercise 3.3.7
namespace Exercise_3_3_7

theorem aux₁
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hf : f.isBijective)
    (hg : g.isBijective) :
    (f.comp g hfg).isBijective := by
  dsimp only [MyFun.isBijective]
  constructor
  · dsimp only [MyFun.isInjective]
    intro x x' hxgfdom hx'gfdom hxnx'
    intro hgfxgfx'
    have hxfdom :
        x ∈ f.domain := by
      dsimp only [MyFun.comp] at hxgfdom
      dsimp only [MyFun.from_fun] at hxgfdom
      exact hxgfdom
    have hfxgdom :
        f.eval x hxfdom ∈ g.domain := by
      rw [← hfg]
      exact MyFun.eval_codomain f x hxfdom
    rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom] at hgfxgfx'
    have hx'fdom : x' ∈ f.domain := by
      dsimp only [MyFun.comp] at hx'gfdom
      dsimp only [MyFun.from_fun] at hx'gfdom
      exact hx'gfdom
    have hfx'gdom : f.eval x' hx'fdom ∈ g.domain := by
      rw [← hfg]
      exact MyFun.eval_codomain f x' hx'fdom
    rw [MyFun.comp.eval f g hfg x' hx'fdom hfx'gdom hx'gfdom] at hgfxgfx'
    dsimp only [MyFun.isBijective] at hg
    rcases hg with ⟨hg_inj, hg_surj⟩
    rw [MyFun.isInjective_iff g] at hg_inj
    dsimp only [MyFun.isInjective'] at hg_inj
    have hfxfx' : f.eval x hxfdom = f.eval x' hx'fdom :=
      hg_inj (f.eval x hxfdom) (f.eval x' hx'fdom) hfxgdom hfx'gdom hgfxgfx'
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
        y ∈ f.codomain := by
      rw [hfg]
      exact hygdom
    rcases hf_surj y hyfcodom with ⟨x, hxfdom, hfyx⟩
    use x
    have hxgfdom :
        x ∈ (f.comp g hfg).domain := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    use hxgfdom
    have hfxgdom :
        f.eval x hxfdom ∈ g.domain := by
      rw [← hfg]
      exact MyFun.eval_codomain f x hxfdom
    rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom]
    rw [← hgyz]
    exact MyFun.substitute g (f.eval x hxfdom) y hfxgdom hygdom hfyx

theorem aux₂
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hf : f.isBijective)
    (hg : g.isBijective) :
    (g.inv hg).codomain = (f.inv hf).domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]
  exact Eq.symm hfg

example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : f.codomain = g.domain)
    (hf : f.isBijective)
    (hg : g.isBijective) :
    (f.comp g hfg).inv (aux₁ f g hfg hf hg) ≃
      (g.inv hg).comp (f.inv hf) (aux₂ f g hfg hf hg) := by
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
          z ∈ (g.inv hg).domain := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        dsimp only [MyFun.inv] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        dsimp only [MyFun.comp] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        exact hzgfidom
      have hgizfidom :
          (g.inv hg).eval z hzgidom ∈ (f.inv hf).domain := by
        have hdomeq :
            (f.inv hf).domain = (g.inv hg).codomain := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
          exact hfg
        rw [hdomeq]
        exact MyFun.eval_codomain (g.inv hg) z hzgidom
      rw [MyFun.comp.eval (g.inv hg) (f.inv hf) (aux₂ f g hfg hf hg)
        z hzgidom hgizfidom hzgfidom]
      have hgcopy :
          g.isBijective :=
        hg
      dsimp only [MyFun.isBijective] at hgcopy
      rcases hgcopy with ⟨hg_inj, hg_surj⟩
      dsimp only [MyFun.isSurjective] at hg_surj
      have hzgcodom :
          z ∈ g.codomain := by
        dsimp only [MyFun.inv] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        dsimp only [MyFun.comp] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        exact hzgfidom
      rcases MyFun.exists_unique_of_bijective g hg z hzgfidom
        with ⟨y, hygdom, hgyz, hgyz!⟩
      have hgizy :
          (g.inv hg).eval z hzgidom = y := by
        have hgygidom :
            g.eval y hygdom ∈ (g.inv hg).domain := by
          have hdomeq :
              (g.inv hg).domain = g.codomain := by
            dsimp only [MyFun.inv]
            dsimp only [MyFun.from_fun]
          rw [hdomeq]
          exact MyFun.eval_codomain g y hygdom
        have hsubst :
            (g.inv hg).eval z hzgidom =
              (g.inv hg).eval (g.eval y hygdom) hgygidom :=
          MyFun.substitute (g.inv hg) z (g.eval y hygdom)
            hzgidom hgygidom (Eq.symm hgyz)
        rw [hsubst]
        rw [← MyFun.comp.eval g (g.inv hg) (Exercise_3_3_6.aux₁ g hg)
          y hygdom hgygidom hygdom]
        exact Exercise_3_3_6.finv_f g hg y hygdom
      have hyfidom :
          y ∈ (f.inv hf).domain := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        rw [hfg]
        exact hygdom
      rw [MyFun.substitute (f.inv hf) ((g.inv hg).eval z hzgidom) y
        hgizfidom hyfidom hgizy]
      rcases MyFun.exists_unique_of_bijective f hf y hyfidom
        with ⟨x, hxfdom, hfxz, hfxz!⟩
      have hfiyx :
          (f.inv hf).eval y hyfidom = x := by
        have hfxgidom :
            f.eval x hxfdom ∈ (f.inv hf).domain := by
          have hdomeq :
              (f.inv hf).domain = f.codomain := by
            dsimp only [MyFun.inv]
            dsimp only [MyFun.from_fun]
          rw [hdomeq]
          exact MyFun.eval_codomain f x hxfdom
        have hsubst :
            (f.inv hf).eval y hyfidom =
              (f.inv hf).eval (f.eval x hxfdom) hfxgidom :=
          MyFun.substitute (f.inv hf) y (f.eval x hxfdom)
            hyfidom hfxgidom (Eq.symm hfxz)
        rw [hsubst]
        rw [← MyFun.comp.eval f (f.inv hf) (Exercise_3_3_6.aux₁ f hf)
          x hxfdom hfxgidom hxfdom]
        exact Exercise_3_3_6.finv_f f hf x hxfdom
      rw [hfiyx]
      have hgf :
          (f.comp g hfg).isBijective :=
        aux₁ f g hfg hf hg
      rcases MyFun.exists_unique_of_bijective (f.comp g hfg) hgf z hzgfidom
        with ⟨x', hx'gfdom, hgfx'z, hgfx'z!⟩
      have hgfx'gfidom :
          (f.comp g hfg).eval x' hx'gfdom ∈ ((f.comp g hfg).inv hgf).domain := by
        have hdomeq :
            ((f.comp g hfg).inv hgf).domain = (f.comp g hfg).codomain := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
        rw [hdomeq]
        exact MyFun.eval_codomain (f.comp g hfg) x' hx'gfdom
      have hsubst :
          ((f.comp g hfg).inv hgf).eval z hzgfidom =
            ((f.comp g hfg).inv hgf).eval
              ((f.comp g hfg).eval x' hx'gfdom) hgfx'gfidom :=
        MyFun.substitute ((f.comp g hfg).inv hgf) z
          ((f.comp g hfg).eval x' hx'gfdom)
          hzgfidom hgfx'gfidom (Eq.symm hgfx'z)
      rw [hsubst]
      have hx'gfdom' : x' ∈ (f.comp g hfg).domain :=
        hx'gfdom
      have hfg_inv :
          (f.comp g hfg).codomain = ((f.comp g hfg).inv hgf).domain := by
        dsimp only [MyFun.inv, MyFun.from_fun]
      have hx'comp :
          x' ∈ ((f.comp g hfg).comp ((f.comp g hfg).inv hgf) hfg_inv).domain := by
        dsimp only [MyFun.comp, MyFun.from_fun]
        exact hx'gfdom
      rw [← MyFun.comp.eval (f.comp g hfg) ((f.comp g hfg).inv hgf) hfg_inv
        x' hx'gfdom hgfx'gfidom hx'comp]
      rw [Exercise_3_3_6.finv_f (f.comp g hfg) hgf x' hx'gfdom]
      have hxgfdom :
          x ∈ (f.comp g hfg).domain := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxfdom
      have hgfxz :
          (f.comp g hfg).eval x hxgfdom = z := by
        have hfxgdom :
            f.eval x hxfdom ∈ g.domain := by
          rw [← hfg]
          exact MyFun.eval_codomain f x hxfdom
        rw [MyFun.comp.eval f g hfg x hxfdom hfxgdom hxgfdom]
        have hgeq :
            g.eval (f.eval x hxfdom) hfxgdom = g.eval y hygdom :=
          MyFun.substitute g (f.eval x hxfdom) y hfxgdom hygdom hfxz
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
    (ι X Y hXY).codomain = (ι Y Z hYZ).domain := by
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
    (ι X Y hXY).comp (ι Y Z hYZ) (aux₁ X Y Z hXY hYZ) ≃
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
          x ∈ (ι X Y hXY).domain := by
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        dsimp only [ι] at hxXZdom
        dsimp only [MyFun.from_fun] at hxXZdom
        exact hxXZdom
      have hXYxYZdom :
          (ι X Y hXY).eval x hxXYdom ∈ (ι Y Z hYZ).domain := by
        rw [← aux₁ X Y Z hXY hYZ]
        exact MyFun.eval_codomain (ι X Y hXY) x hxXYdom
      rw [MyFun.comp.eval (ι X Y hXY) (ι Y Z hYZ) (aux₁ X Y Z hXY hYZ)
        x hxXYdom hXYxYZdom hxYZXYdom]
      dsimp only [ι]
      rw [MyFun.from_fun.eval Y Z (fun x _ => x) (fun x hx => hYZ x hx)
        ((MyFun.from_fun X Y (fun x _ => x)
          (fun x hx => hXY x hx)).eval x hxXYdom) hXYxYZdom]
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
    (hfdom : f.domain = A) :
    (ι_id A).codomain = f.domain := by
  dsimp only [ι_id]
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact Eq.symm hfdom

example
    (A : MySet α)
    (f : MyFun α β)
    (hfdom : f.domain = A) :
    f ≃ (ι_id A).comp f (aux₁ A f hfdom) := by
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
          x ∈ (ι_id A).domain := by
        dsimp only [ι_id]
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        rw [hfdom] at hxfdom
        exact hxfdom
      have hAxfdom :
          (ι_id A).eval x hxAdom ∈ f.domain := by
        rw [← aux₁ A f hfdom]
        exact MyFun.eval_codomain (ι_id A) x hxAdom
      rw [MyFun.comp.eval (ι_id A) f (aux₁ A f hfdom) x hxAdom hAxfdom hxfAdom]
      have hxeval :
          x = (ι_id A).eval x hxAdom := by
        dsimp only [ι_id]
        dsimp only [ι]
        rw [MyFun.from_fun.eval A A (fun x _ => x) (fun x hx => hx) x hxAdom]
      exact MyFun.substitute f x ((ι_id A).eval x hxAdom) hxfdom hAxfdom hxeval

theorem aux₂
    {α β : Type}
    (B : MySet β)
    (f : MyFun α β)
    (hfcodom : f.codomain = B) :
    f.codomain = (ι_id B).domain := by
  dsimp only [ι_id]
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact hfcodom

example
    (B : MySet β)
    (f : MyFun α β)
    (hfcodom : f.codomain = B) :
    f ≃ f.comp (ι_id B) (aux₂ B f hfcodom) := by
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
          f.eval x hxfdom ∈ (ι_id B).domain := by
        have hdomeq :
            (ι_id B).domain = f.codomain := by
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
        (f.eval x hxfdom) hfxBdom]

end Exercise_3_3_8_b

-- (c)
namespace Exercise_3_3_8_c

theorem aux₁
    {α β : Type}
    (f : MyFun α β)
    (hf : f.isBijective) :
    (f.inv hf).codomain = f.domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

example
    (B : MySet β)
    (f : MyFun α β)
    (hfcodom : f.codomain = B)
    (hf : f.isBijective) :
    (f.inv hf).comp f (aux₁ f hf) ≃ ι_id B := by
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
          x ∈ (f.inv hf).domain := by
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
    (hf : f.isBijective) :
    f.codomain = (f.inv hf).domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

example
    (A : MySet α)
    (f : MyFun α β)
    (hfdom : f.domain = A)
    (hf : f.isBijective) :
    f.comp (f.inv hf) (aux₂ f hf) ≃ ι_id A := by
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
          x ∈ f.domain := by
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
    (hhdom : h.domain = X ∪ Y) :
    (ι X (X ∪ Y) (aux₁ X Y)).codomain = h.domain := by
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact Eq.symm hhdom

theorem aux₄
    {α β : Type}
    (X Y : MySet α)
    (h : MyFun α β)
    (hhdom : h.domain = X ∪ Y) :
    (ι Y (X ∪ Y) (aux₂ X Y)).codomain = h.domain := by
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact Eq.symm hhdom

example
    (X Y : MySet α)
    (Z : MySet β)
    (hXY : MySet.disjoint X Y)
    (f : MyFun α β)
    (hfdom : f.domain = X)
    (hfcodom : f.codomain = Z)
    (g : MyFun α β)
    (hgdom : g.domain = Y)
    (hgcodom : g.codomain = Z) :
    ∃ (h : MyFun α β) (hhdom : h.domain = X ∪ Y),
    h.codomain = Z ∧
    ((ι X (X ∪ Y) (aux₁ X Y)).comp h (aux₃ X Y h hhdom) ≃ f) ∧
    ((ι Y (X ∪ Y) (aux₂ X Y)).comp h (aux₄ X Y h hhdom) ≃ g) ∧
    (∀ (h' : MyFun α β) (hh'dom : h'.domain = X ∪ Y),
      h'.codomain = Z →
      ((ι X (X ∪ Y) (aux₁ X Y)).comp h' (aux₃ X Y h' hh'dom) ≃ f) →
      ((ι Y (X ∪ Y) (aux₂ X Y)).comp h' (aux₄ X Y h' hh'dom) ≃ g) →
        h' ≃ h) := by
  let h :
      MyFun α β :=
    {
    domain := X ∪ Y,
    codomain := Z,
    prop := fun x y => by
      by_cases h : x ∈ X
      · have hxfdom : x ∈ f.domain := by
          rw [hfdom]
          exact h
        exact y = f.eval x hxfdom
      · by_cases h' : x ∈ Y
        · have hxgdom : x ∈ g.domain := by
            rw [hgdom]
            exact h'
          exact y = g.eval x hxgdom
        · exact False
    isValidProp := by
      intro x hxXY
      rw [MySet.mem_union X Y x] at hxXY
      rcases hxXY with (hxX | hxY)
      · have hxfdom : x ∈ f.domain := by
          rw [hfdom]
          exact hxX
        use (f.eval x hxfdom)
        constructor
        · rw [← hfcodom]
          exact MyFun.eval_codomain f x hxfdom
        · constructor
          · dsimp only [MyFun.prop]
            rw [dif_pos hxX]
          · intro y' hy'Z h
            rw [dif_pos hxX] at h
            rw [h]
      · have hxgdom : x ∈ g.domain := by
          rw [hgdom]
          exact hxY
        use (g.eval x hxgdom)
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
      h.domain = X ∪ Y := by
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
              (ι X (X ∪ Y) hXXY).codomain = h.domain := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
          have hxXXYdom :
              x ∈ (ι X (X ∪ Y) hXXY).domain := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
            rw [← hfdom]
            exact hxfdom
          have hXXYxhdom :
              (ι X (X ∪ Y) hXXY).eval x hxXXYdom ∈ h.domain := by
            have hdomeq :
                h.domain = (ι X (X ∪ Y) hXXY).codomain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            rw [hdomeq]
            exact MyFun.eval_codomain (ι X (X ∪ Y) hXXY) x hxXXYdom
          rw [MyFun.comp.eval (ι X (X ∪ Y) hXXY) h hXXYcodomhdom
            x hxXXYdom hXXYxhdom hxhXXYdom]
          have hxhdom :
              x ∈ h.domain := by
            dsimp only [h]
            rw [MySet.mem_union X Y x]
            rw [hfdom] at hxfdom
            exact Or.inl hxfdom
          have hheval :
              h.eval ((ι X (X ∪ Y) hXXY).eval x hxXXYdom) hXXYxhdom =
                h.eval x hxhdom := by
            have hιeval :
                (ι X (X ∪ Y) hXXY).eval x hxXXYdom = x := by
              dsimp only [ι]
              rw [MyFun.from_fun.eval X (X ∪ Y) (fun x _ => x) (fun x hx => hXXY x hx)
                x hxXXYdom]
            exact MyFun.substitute h
              ((ι X (X ∪ Y) hXXY).eval x hxXXYdom) x hXXYxhdom hxhdom hιeval
          rw [hheval]
          have hfxhcodom :
              f.eval x hxfdom ∈ h.codomain := by
            have hcodeq :
                h.codomain = f.codomain := by
              dsimp only [h]
              exact Eq.symm hfcodom
            rw [hcodeq]
            exact MyFun.eval_codomain f x hxfdom
          have hprop :
              h.prop x (f.eval x hxfdom) := by
            dsimp only [h]
            have hxX :
                x ∈ X := by
              rw [hfdom] at hxfdom
              exact hxfdom
            rw [dif_pos hxX]
          have hfeq :
              f.eval x hxfdom = h.eval x hxhdom :=
            Iff.mpr (MyFun.def h x (f.eval x hxfdom) hxhdom hfxhcodom) hprop
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
                (ι Y (X ∪ Y) hYXY).codomain = h.domain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            have hxYXYdom :
                x ∈ (ι Y (X ∪ Y) hYXY).domain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
              rw [← hgdom]
              exact hxgdom
            have hYXYxhdom :
                (ι Y (X ∪ Y) hYXY).eval x hxYXYdom ∈ h.domain := by
              have hdomeq :
                  h.domain = (ι Y (X ∪ Y) hYXY).codomain := by
                dsimp only [ι]
                dsimp only [MyFun.from_fun]
              rw [hdomeq]
              exact MyFun.eval_codomain (ι Y (X ∪ Y) hYXY) x hxYXYdom
            rw [MyFun.comp.eval (ι Y (X ∪ Y) hYXY) h hYXYcodomhdom
              x hxYXYdom hYXYxhdom hxhYXYdom]
            have hxhdom :
                x ∈ h.domain := by
              dsimp only [h]
              rw [MySet.mem_union X Y x]
              rw [hgdom] at hxgdom
              exact Or.inr hxgdom
            have hheval :
                h.eval ((ι Y (X ∪ Y) hYXY).eval x hxYXYdom) hYXYxhdom =
                  h.eval x hxhdom := by
              have hιeval :
                  (ι Y (X ∪ Y) hYXY).eval x hxYXYdom = x := by
                dsimp only [ι]
                rw [MyFun.from_fun.eval Y (X ∪ Y) (fun x _ => x) (fun x hx => hYXY x hx)
                x hxYXYdom]
              exact MyFun.substitute h
                ((ι Y (X ∪ Y) hYXY).eval x hxYXYdom) x hYXYxhdom hxhdom hιeval
            rw [hheval]
            have hxgxhcodom :
                g.eval x hxgdom ∈ h.codomain := by
              have hcodeq :
                  h.codomain = g.codomain := by
                dsimp only [h]
                exact Eq.symm hgcodom
              rw [hcodeq]
              exact MyFun.eval_codomain g x hxgdom
            have hprop :
                h.prop x (g.eval x hxgdom) := by
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
                g.eval x hxgdom = h.eval x hxhdom :=
              Iff.mpr (MyFun.def h x (g.eval x hxgdom) hxhdom hxgxhcodom) hprop
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
                h.prop x (h'.eval x hxh'dom) := by
              dsimp only [h]
              by_cases hxX : x ∈ X
              · rw [dif_pos hxX]
                rcases hh'f with ⟨hh'XXYdomfdom, hh'XXYcodomfcodom, hh'XXYxfx⟩
                have hXXYcodomh'dom :
                    (ι X (X ∪ Y) hXXY).codomain = h'.domain := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact Eq.symm hh'dom
                have hxh'XXY :
                    x ∈ ((ι X (X ∪ Y) hXXY).comp h' hXXYcodomh'dom).domain := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxX
                have hxfdom :
                    x ∈ f.domain := by
                  rw [hfdom]
                  exact hxX
                have hcompeq :
                    ((ι X (X ∪ Y) hXXY).comp h' hXXYcodomh'dom).eval x hxh'XXY =
                      f.eval x hxfdom :=
                  hh'XXYxfx x hxh'XXY hxfdom
                rw [← hcompeq]
                have hXXYxh'dom :
                    (ι X (X ∪ Y) hXXY).eval x hxh'XXY ∈ h'.domain := by
                  have hdomeq :
                      h'.domain = (ι X (X ∪ Y) hXXY).codomain := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [hdomeq]
                  exact MyFun.eval_codomain (ι X (X ∪ Y) hXXY) x hxh'XXY
                rw [MyFun.comp.eval (ι X (X ∪ Y) hXXY) h' hXXYcodomh'dom
                  x hxh'XXY hXXYxh'dom hxh'XXY]
                have hxeval :
                    x = (ι X (X ∪ Y) hXXY).eval x hxh'XXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval X (X ∪ Y) (fun x _ => x)
                    (fun x hx => hXXY x hx) x hxh'XXY]
                exact MyFun.substitute h' x ((ι X (X ∪ Y) hXXY).eval x hxh'XXY)
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
                    (ι Y (X ∪ Y) hYXY).codomain = h'.domain := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact Eq.symm hh'dom
                have hxh'YXY :
                    x ∈ ((ι Y (X ∪ Y) hYXY).comp h' hYXYcodomh'dom).domain := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxY
                have hxgdom :
                    x ∈ g.domain := by
                  rw [hgdom]
                  exact hxY
                have hcompeq :
                    ((ι Y (X ∪ Y) hYXY).comp h' hYXYcodomh'dom).eval x hxh'YXY =
                      g.eval x hxgdom :=
                  hh'YXYxgx x hxh'YXY hxgdom
                rw [← hcompeq]
                have hYXYxh'dom :
                    (ι Y (X ∪ Y) hYXY).eval x hxh'YXY ∈ h'.domain := by
                  have hdomeq :
                      h'.domain = (ι Y (X ∪ Y) hYXY).codomain := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [hdomeq]
                  exact MyFun.eval_codomain (ι Y (X ∪ Y) hYXY) x hxh'YXY
                rw [MyFun.comp.eval (ι Y (X ∪ Y) hYXY) h' hYXYcodomh'dom
                  x hxh'YXY hYXYxh'dom hxh'YXY]
                have hxeval :
                    x = (ι Y (X ∪ Y) hYXY).eval x hxh'YXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval Y (X ∪ Y) (fun x _ => x)
                    (fun x hx => hYXY x hx) x hxh'YXY]
                exact MyFun.substitute h' x ((ι Y (X ∪ Y) hYXY).eval x hxh'YXY)
                  hxh'dom hYXYxh'dom hxeval
            have hh'xhcodom : h'.eval x hxh'dom ∈ h.codomain := by
              have hcodeq :
                  h.codomain = h'.codomain := by
                dsimp only [h]
                exact Eq.symm hh'codom
              rw [hcodeq]
              exact MyFun.eval_codomain h' x hxh'dom
            refine Iff.mpr (MyFun.def h x (h'.eval x hxh'dom) hxhdom hh'xhcodom) hprop

end Exercise_3_3_8_d

-- (e)
namespace Exercise_3_3_8_e

open Exercise_3_3_8_d

theorem aux₅
    {α β : Type}
    (x : α)
    (X Y : MySet α)
    (f : MyFun α β)
    (hfdom : f.domain = X)
    (hxXY : x ∈ X ∩ Y) :
    x ∈ f.domain := by
  rw [MySet.mem_inter X Y x] at hxXY
  rw [hfdom]
  exact And.left hxXY

theorem aux₆
    {α β : Type}
    (x : α)
    (X Y : MySet α)
    (g : MyFun α β)
    (hgdom : g.domain = Y)
    (hxXY : x ∈ X ∩ Y) :
    x ∈ g.domain := by
  rw [MySet.mem_inter X Y x] at hxXY
  rw [hgdom]
  exact And.right hxXY

example
    (X Y : MySet α)
    (Z : MySet β)
    (f : MyFun α β)
    (hfdom : f.domain = X)
    (hfcodom : f.codomain = Z)
    (g : MyFun α β)
    (hgdom : g.domain = Y)
    (hgcodom : g.codomain = Z)
    (hfg : ∀ (x : α) (hx : x ∈ X ∩ Y),
      f.eval x (aux₅ x X Y f hfdom hx) =
        g.eval x (aux₆ x X Y g hgdom hx)) :
    ∃ (h : MyFun α β) (hhdom : h.domain = X ∪ Y),
    h.codomain = Z ∧
    ((ι X (X ∪ Y) (aux₁ X Y)).comp h (aux₃ X Y h hhdom) ≃ f) ∧
    ((ι Y (X ∪ Y) (aux₂ X Y)).comp h (aux₄ X Y h hhdom) ≃ g) ∧
    (∀ (h' : MyFun α β) (hh'dom : h'.domain = X ∪ Y),
      h'.codomain = Z →
      ((ι X (X ∪ Y) (aux₁ X Y)).comp h' (aux₃ X Y h' hh'dom) ≃ f) →
      ((ι Y (X ∪ Y) (aux₂ X Y)).comp h' (aux₄ X Y h' hh'dom) ≃ g) →
        h' ≃ h) := by
  let h :
      MyFun α β :=
    {
    domain := X ∪ Y,
    codomain := Z,
    prop := fun x y => by
      by_cases h : x ∈ X
      · have hxfdom : x ∈ f.domain := by
          rw [hfdom]
          exact h
        exact y = f.eval x hxfdom
      · by_cases h' : x ∈ Y
        · have hxgdom : x ∈ g.domain := by
            rw [hgdom]
            exact h'
          exact y = g.eval x hxgdom
        · exact False
    isValidProp := by
      intro x hxXY
      rw [MySet.mem_union X Y x] at hxXY
      rcases hxXY with (hxX | hxY)
      · have hxfdom : x ∈ f.domain := by
          rw [hfdom]
          exact hxX
        use (f.eval x hxfdom)
        constructor
        · rw [← hfcodom]
          exact MyFun.eval_codomain f x hxfdom
        · constructor
          · dsimp only [MyFun.prop]
            rw [dif_pos hxX]
          · intro y' hy'Z h
            rw [dif_pos hxX] at h
            rw [h]
      · have hxgdom : x ∈ g.domain := by
          rw [hgdom]
          exact hxY
        use (g.eval x hxgdom)
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
      h.domain = X ∪ Y := by
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
              (ι X (X ∪ Y) hXXY).codomain = h.domain := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
          have hxXXYdom :
              x ∈ (ι X (X ∪ Y) hXXY).domain := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
            rw [← hfdom]
            exact hxfdom
          have hXXYxhdom :
              (ι X (X ∪ Y) hXXY).eval x hxXXYdom ∈ h.domain := by
            have hdomeq :
                h.domain = (ι X (X ∪ Y) hXXY).codomain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            rw [hdomeq]
            exact MyFun.eval_codomain (ι X (X ∪ Y) hXXY) x hxXXYdom
          rw [MyFun.comp.eval (ι X (X ∪ Y) hXXY) h hXXYcodomhdom
            x hxXXYdom hXXYxhdom hxhXXYdom]
          have hxhdom :
              x ∈ h.domain := by
            dsimp only [h]
            rw [MySet.mem_union X Y x]
            rw [hfdom] at hxfdom
            exact Or.inl hxfdom
          have hheval :
              h.eval ((ι X (X ∪ Y) hXXY).eval x hxXXYdom) hXXYxhdom =
                h.eval x hxhdom := by
            have hιeval :
                (ι X (X ∪ Y) hXXY).eval x hxXXYdom = x := by
              dsimp only [ι]
              rw [MyFun.from_fun.eval X (X ∪ Y) (fun x _ => x) (fun x hx => hXXY x hx)
                x hxXXYdom]
            exact MyFun.substitute h
              ((ι X (X ∪ Y) hXXY).eval x hxXXYdom) x hXXYxhdom hxhdom hιeval
          rw [hheval]
          have hfxhcodom :
              f.eval x hxfdom ∈ h.codomain := by
            have hcodeq :
                h.codomain = f.codomain := by
              dsimp only [h]
              exact Eq.symm hfcodom
            rw [hcodeq]
            exact MyFun.eval_codomain f x hxfdom
          have hprop :
              h.prop x (f.eval x hxfdom) := by
            dsimp only [h]
            have hxX :
                x ∈ X := by
              rw [hfdom] at hxfdom
              exact hxfdom
            rw [dif_pos hxX]
          have hfeq :
              f.eval x hxfdom = h.eval x hxhdom :=
            Iff.mpr (MyFun.def h x (f.eval x hxfdom) hxhdom hfxhcodom) hprop
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
                (ι Y (X ∪ Y) hYXY).codomain = h.domain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            have hxYXYdom :
                x ∈ (ι Y (X ∪ Y) hYXY).domain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
              rw [← hgdom]
              exact hxgdom
            have hYXYxhdom :
                (ι Y (X ∪ Y) hYXY).eval x hxYXYdom ∈ h.domain := by
              have hdomeq :
                  h.domain = (ι Y (X ∪ Y) hYXY).codomain := by
                dsimp only [ι]
                dsimp only [MyFun.from_fun]
              rw [hdomeq]
              exact MyFun.eval_codomain (ι Y (X ∪ Y) hYXY) x hxYXYdom
            rw [MyFun.comp.eval (ι Y (X ∪ Y) hYXY) h hYXYcodomhdom
              x hxYXYdom hYXYxhdom hxhYXYdom]
            have hxhdom :
                x ∈ h.domain := by
              dsimp only [h]
              rw [MySet.mem_union X Y x]
              rw [hgdom] at hxgdom
              exact Or.inr hxgdom
            have hheval :
                h.eval ((ι Y (X ∪ Y) hYXY).eval x hxYXYdom) hYXYxhdom =
                  h.eval x hxhdom := by
              have hιeval :
                  (ι Y (X ∪ Y) hYXY).eval x hxYXYdom = x := by
                dsimp only [ι]
                rw [MyFun.from_fun.eval Y (X ∪ Y) (fun x _ => x) (fun x hx => hYXY x hx)
                x hxYXYdom]
              exact MyFun.substitute h
                ((ι Y (X ∪ Y) hYXY).eval x hxYXYdom) x hYXYxhdom hxhdom hιeval
            rw [hheval]
            have hxgxhcodom :
                g.eval x hxgdom ∈ h.codomain := by
              have hcodeq :
                  h.codomain = g.codomain := by
                dsimp only [h]
                exact Eq.symm hgcodom
              rw [hcodeq]
              exact MyFun.eval_codomain g x hxgdom
            have hprop :
                h.prop x (g.eval x hxgdom) := by
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
                g.eval x hxgdom = h.eval x hxhdom :=
              Iff.mpr (MyFun.def h x (g.eval x hxgdom) hxhdom hxgxhcodom) hprop
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
                h.prop x (h'.eval x hxh'dom) := by
              dsimp only [h]
              by_cases hxX : x ∈ X
              · rw [dif_pos hxX]
                rcases hh'f with ⟨hh'XXYdomfdom, hh'XXYcodomfcodom, hh'XXYxfx⟩
                have hXXYcodomh'dom :
                    (ι X (X ∪ Y) hXXY).codomain = h'.domain := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact Eq.symm hh'dom
                have hxh'XXY :
                    x ∈ ((ι X (X ∪ Y) hXXY).comp h' hXXYcodomh'dom).domain := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxX
                have hxfdom :
                    x ∈ f.domain := by
                  rw [hfdom]
                  exact hxX
                have hcompeq :
                    ((ι X (X ∪ Y) hXXY).comp h' hXXYcodomh'dom).eval x hxh'XXY =
                      f.eval x hxfdom :=
                  hh'XXYxfx x hxh'XXY hxfdom
                rw [← hcompeq]
                have hXXYxh'dom :
                    (ι X (X ∪ Y) hXXY).eval x hxh'XXY ∈ h'.domain := by
                  have hdomeq :
                      h'.domain = (ι X (X ∪ Y) hXXY).codomain := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [hdomeq]
                  exact MyFun.eval_codomain (ι X (X ∪ Y) hXXY) x hxh'XXY
                rw [MyFun.comp.eval (ι X (X ∪ Y) hXXY) h' hXXYcodomh'dom
                  x hxh'XXY hXXYxh'dom hxh'XXY]
                have hxeval :
                    x = (ι X (X ∪ Y) hXXY).eval x hxh'XXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval X (X ∪ Y) (fun x _ => x)
                    (fun x hx => hXXY x hx) x hxh'XXY]
                exact MyFun.substitute h' x ((ι X (X ∪ Y) hXXY).eval x hxh'XXY)
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
                    (ι Y (X ∪ Y) hYXY).codomain = h'.domain := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact Eq.symm hh'dom
                have hxh'YXY :
                    x ∈ ((ι Y (X ∪ Y) hYXY).comp h' hYXYcodomh'dom).domain := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxY
                have hxgdom :
                    x ∈ g.domain := by
                  rw [hgdom]
                  exact hxY
                have hcompeq :
                    ((ι Y (X ∪ Y) hYXY).comp h' hYXYcodomh'dom).eval x hxh'YXY =
                      g.eval x hxgdom :=
                  hh'YXYxgx x hxh'YXY hxgdom
                rw [← hcompeq]
                have hYXYxh'dom :
                    (ι Y (X ∪ Y) hYXY).eval x hxh'YXY ∈ h'.domain := by
                  have hdomeq :
                      h'.domain = (ι Y (X ∪ Y) hYXY).codomain := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [hdomeq]
                  exact MyFun.eval_codomain (ι Y (X ∪ Y) hYXY) x hxh'YXY
                rw [MyFun.comp.eval (ι Y (X ∪ Y) hYXY) h' hYXYcodomh'dom
                  x hxh'YXY hYXYxh'dom hxh'YXY]
                have hxeval :
                    x = (ι Y (X ∪ Y) hYXY).eval x hxh'YXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval Y (X ∪ Y) (fun x _ => x)
                    (fun x hx => hYXY x hx) x hxh'YXY]
                exact MyFun.substitute h' x ((ι Y (X ∪ Y) hYXY).eval x hxh'YXY)
                  hxh'dom hYXYxh'dom hxeval
            have hh'xhcodom : h'.eval x hxh'dom ∈ h.codomain := by
              have hcodeq :
                  h.codomain = h'.codomain := by
                dsimp only [h]
                exact Eq.symm hh'codom
              rw [hcodeq]
              exact MyFun.eval_codomain h' x hxh'dom
            refine Iff.mpr (MyFun.def h x (h'.eval x hxh'dom) hxhdom hh'xhcodom) hprop

end Exercise_3_3_8_e

end Exercise_3_3_8

end Exercises -- section Exercises
