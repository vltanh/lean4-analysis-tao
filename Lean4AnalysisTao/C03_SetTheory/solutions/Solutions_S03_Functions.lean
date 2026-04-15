import Lean4AnalysisTao.C03_SetTheory.S03_Functions

section Exercises

-- Exercise 3.3.1
example :
  ∀ (f : MyFun α β), f ≃ f := by
  intro f
  dsimp only [MyFun.eq]
  constructor
  · rfl
  · constructor
    · rfl
    · intro x hxf hxg
      dsimp only [MyFun.eval]

example :
  ∀ (f g : MyFun α β), (f ≃ g) → (g ≃ f) := by
  intro f g h
  dsimp only [MyFun.eq] at h
  rcases h with ⟨hdom, hcodom, hfg⟩
  dsimp only [MyFun.eq]
  constructor
  · exact hdom.symm
  · constructor
    · exact hcodom.symm
    · intro x hxg hxf
      exact (hfg hxf hxg).symm

example :
  ∀ (f g h : MyFun α β), (f ≃ g) → (g ≃ h) → (f ≃ h) := by
  intro f g h hfg hgh
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
      have hxg : x ∈ g.domain := by
        rw [← hdomfg]
        exact hxf
      rw [hfg hxf hxg]
      exact hgh hxg hxh

example (f f' : MyFun α β) (g g' : MyFun β γ)
  (hfg : f.codomain = g.domain) (hf'g' : f'.codomain = g'.domain) :
  (f ≃ f') → (g ≃ g') → (f.comp g hfg ≃ f'.comp g' hf'g') := by
  intro hff' hgg'
  dsimp only [MyFun.eq] at hff'
  rcases hff' with ⟨hdomff', hcodomff', hff'⟩
  dsimp only [MyFun.eq] at hgg'
  rcases hgg' with ⟨hdomgg', hcodomgg', hgg'⟩
  dsimp only [MyFun.eq]
  constructor
  · rw [MyFun.comp.eval.domain]
    rw [MyFun.comp.eval.domain]
    exact hdomff'
  · constructor
    · rw [MyFun.comp.eval.codomain]
      rw [MyFun.comp.eval.codomain]
      exact hcodomgg'
    · intro x hxf hxf'
      dsimp only [MyFun.comp]
      rw [MyFun.from_fun.eval]
      rw [MyFun.from_fun.eval]
      dsimp only [MyFun.comp] at hxf
      dsimp only [MyFun.from_fun] at hxf
      dsimp only [MyFun.comp] at hxf'
      dsimp only [MyFun.from_fun] at hxf'
      have hfxg : f.eval x hxf ∈ g.domain := by
        rw [← hfg]
        exact f.eval_codomain hxf
      have hfxg' : f.eval x hxf ∈ g'.domain := by
        rw [← hf'g']
        rw [← hcodomff']
        exact f.eval_codomain hxf
      have hfxfx' : f.eval x hxf = f'.eval x hxf' := hff' hxf hxf'
      have hgfxg'fx :
        g.eval (f.eval x hxf) hfxg = g'.eval (f.eval x hxf) hfxg' :=
        hgg' hfxg hfxg'
      rw [hgfxg'fx]
      have hf'xg' : f'.eval x hxf' ∈ g'.domain := by
        rw [← hf'g']
        exact f'.eval_codomain hxf'
      exact g'.substitute hfxg' hf'xg' hfxfx'

-- Exercise 3.3.2
example (f : MyFun α β) (g : MyFun β γ)
  (hfg : f.codomain = g.domain) :
  f.isInjective → g.isInjective → (f.comp g hfg).isInjective := by
  intro hf hg
  dsimp only [MyFun.isInjective] at hf
  dsimp only [MyFun.isInjective] at hg
  dsimp only [MyFun.isInjective]
  intro x x' hxgfdom hx'gfdom hxx'
  dsimp only [MyFun.comp] at hxgfdom
  dsimp only [MyFun.from_fun] at hxgfdom
  dsimp only [MyFun.comp] at hx'gfdom
  dsimp only [MyFun.from_fun] at hx'gfdom
  have hfxgdom : f.eval x hxgfdom ∈ g.domain := by
    rw [← hfg]
    exact f.eval_codomain hxgfdom
  rw [MyFun.comp.eval hfg hxgfdom hfxgdom]
  have hfx'gdom : f.eval x' hx'gfdom ∈ g.domain := by
    rw [← hfg]
    exact f.eval_codomain hx'gfdom
  rw [MyFun.comp.eval hfg hx'gfdom hfx'gdom]
  exact hg hfxgdom hfx'gdom (hf hxgfdom hx'gfdom hxx')

example (f : MyFun α β) (g : MyFun β γ)
  (hfg : f.codomain = g.domain) :
  f.isSurjective → g.isSurjective → (f.comp g hfg).isSurjective := by
  intro hf hg
  dsimp only [MyFun.isSurjective] at hf
  dsimp only [MyFun.isSurjective] at hg
  dsimp only [MyFun.isSurjective]
  intro z hz
  dsimp only [MyFun.comp] at hz
  dsimp only [MyFun.from_fun] at hz
  rcases hg z hz with ⟨y, hy, hgyz⟩
  have hyfcodom : y ∈ f.codomain := by
    rw [hfg]
    exact hy
  rcases hf y hyfcodom with ⟨x, hx, hfx⟩
  use x, hx
  have hfxgdom : f.eval x hx ∈ g.domain := by
    rw [← hfg]
    exact f.eval_codomain hx
  rw [MyFun.comp.eval hfg hx hfxgdom]
  rw [← hgyz]
  exact g.substitute hfxgdom hy hfx

-- Exercise 3.3.3
-- TODO: When is the empty function into a given set X injective? surjective? bijective?

-- Exercise 3.3.4
example (f f' : MyFun α β) (g : MyFun β γ)
  (hfg : f.codomain = g.domain) (hf'g : f'.codomain = g.domain) :
  (f.comp g hfg ≃ f'.comp g hf'g) → g.isInjective → f ≃ f' := by
  intro hgfgf' hg
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
      have hxgfdom : x ∈ (f.comp g hfg).domain := by
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
        hgfgf' hxgfdom hxgf'dom
      have hfxgdom : f.eval x hxf ∈ g.domain := by
        rw [← hfg]
        exact f.eval_codomain hxf
      rw [MyFun.comp.eval hfg hxf hfxgdom] at hgfxgf'x
      have hfx'gdom : f'.eval x hxf' ∈ g.domain := by
        rw [← hf'g]
        exact f'.eval_codomain hxf'
      rw [MyFun.comp.eval hf'g hxf' hfx'gdom] at hgfxgf'x
      rw [MyFun.isInjective_iff] at hg
      dsimp only [MyFun.isInjective'] at hg
      exact hg hfxgdom hfx'gdom hgfxgf'x

-- TODO: Is the same statement true if g is not injective?

example (f : MyFun α β) (g g' : MyFun β γ)
  (hfg : f.codomain = g.domain) (hfg' : f.codomain = g'.domain) :
  (f.comp g hfg ≃ f.comp g' hfg') → f.isSurjective → g ≃ g' := by
  intro hgfg'f hf
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
      dsimp only [MyFun.isSurjective] at hf
      have hyfcodom : y ∈ f.codomain := by
        rw [hfg]
        exact hygdom
      rcases hf y hyfcodom with ⟨x, hxf, hfy⟩
      have hfxgdom : f.eval x hxf ∈ g.domain := by
        rw [← hfg]
        exact f.eval_codomain hxf
      have hfxg'dom : f.eval x hxf ∈ g'.domain := by
        rw [← hfg']
        exact f.eval_codomain hxf
      have hgfxg'fx :
        (f.comp g hfg).eval x hxf =
          (f.comp g' hfg').eval x hxf :=
        hgfg'f hxf hxf
      rw [MyFun.comp.eval hfg hxf hfxgdom] at hgfxg'fx
      rw [MyFun.comp.eval hfg' hxf hfxg'dom] at hgfxg'fx
      have hgfxgy :
        g.eval (f.eval x hxf) hfxgdom = g.eval y hygdom :=
        g.substitute hfxgdom hygdom hfy
      have hg'fxg'y :
        g'.eval (f.eval x hxf) hfxg'dom = g'.eval y hyg'dom :=
        g'.substitute hfxg'dom hyg'dom hfy
      rw [← hgfxgy]
      rw [← hg'fxg'y]
      exact hgfxg'fx

-- TODO: Is the same statement true if f is not surjective?

-- Exercise 3.3.5
example (f : MyFun α β) (g : MyFun β γ) (hfg : f.codomain = g.domain) :
  (f.comp g hfg).isInjective → f.isInjective := by
  intro hgf
  dsimp only [MyFun.isInjective] at hgf
  dsimp only [MyFun.isInjective]
  intro x x' hxfdom hx'fdom hxx'
  have hxgfdom : x ∈ (f.comp g hfg).domain := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hxfdom
  have hx'gfdom : x' ∈ (f.comp g hfg).domain := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hx'fdom
  have hgfxngfx' := hgf hxgfdom hx'gfdom hxx'
  have hfxgdom : f.eval x hxfdom ∈ g.domain := by
    rw [← hfg]
    exact f.eval_codomain hxfdom
  have hfx'gdom : f.eval x' hx'fdom ∈ g.domain := by
    rw [← hfg]
    exact f.eval_codomain hx'fdom
  rw [MyFun.comp.eval hfg hxfdom hfxgdom] at hgfxngfx'
  rw [MyFun.comp.eval hfg hx'fdom hfx'gdom] at hgfxngfx'
  intro hfxfx'
  have hgfxgfx' :
    g.eval (f.eval x hxfdom) hfxgdom
      = g.eval (f.eval x' hx'fdom) hfx'gdom :=
    g.substitute hfxgdom hfx'gdom hfxfx'
  exact hgfxngfx' hgfxgfx'

-- TODO: Is it true that g must also be injective?

example (f : MyFun α β) (g : MyFun β γ) (hfg : f.codomain = g.domain) :
  (f.comp g hfg).isSurjective → g.isSurjective := by
  intro hgf
  dsimp only [MyFun.isSurjective] at hgf
  dsimp only [MyFun.isSurjective]
  intro z hz
  have hzgfcodom : z ∈ (f.comp g hfg).codomain := by
    dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
    exact hz
  rcases hgf z hzgfcodom with ⟨x, hxgfdom, hgfxz⟩
  have hxfdom : x ∈ f.domain := by
    dsimp only [MyFun.comp] at hxgfdom
    dsimp only [MyFun.from_fun] at hxgfdom
    exact hxgfdom
  have hfxgdom : f.eval x hxfdom ∈ g.domain := by
    rw [← hfg]
    exact f.eval_codomain hxfdom
  use (f.eval x hxfdom), hfxgdom
  rw [MyFun.comp.eval hfg hxfdom hfxgdom] at hgfxz
  exact hgfxz

-- TODO: Is it true that f must also be surjective?

-- Exercise 3.3.6
namespace Exercise_3_3_6

theorem aux₁ {f : MyFun α β} (hf : f.isBijective) :
  f.codomain = (f.inv hf).domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

theorem finv_f {f : MyFun α β} (hf : f.isBijective) :
  ∀ {x : α} (hx : x ∈ f.domain),
    (f.comp (f.inv hf) (aux₁ hf)).eval x hx = x := by
  intro x hxf
  have hffi : f.codomain = (f.inv hf).domain := aux₁ hf
  have hfxfidom : f.eval x hxf ∈ (f.inv hf).domain := by
    rw [← hffi]
    exact f.eval_codomain hxf
  rw [MyFun.comp.eval hffi hxf hfxfidom]
  dsimp only [MyFun.inv]
  rw [MyFun.from_fun.eval]
  rcases MyClassical.choose_spec (MyFun.exists_unique_of_bijective hf hfxfidom)
    with ⟨hx, h, h'⟩
  exact h' hxf rfl

theorem aux₂ {f : MyFun α β} (hf : f.isBijective) :
  (f.inv hf).codomain = f.domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

theorem f_finv {f : MyFun α β} (hf : f.isBijective) :
  ∀ {y : β} (hy : y ∈ (f.inv hf).domain),
    ((f.inv hf).comp f (aux₂ hf)).eval y hy = y := by
  intro y hyfidom
  have hffi : (f.inv hf).codomain = f.domain := aux₂ hf
  have hfiyfdom : (f.inv hf).eval y hyfidom ∈ f.domain := by
    rw [← hffi]
    exact (f.inv hf).eval_codomain hyfidom
  rw [MyFun.comp.eval hffi hyfidom hfiyfdom]
  dsimp only [MyFun.inv] at hyfidom
  dsimp only [MyFun.from_fun] at hyfidom
  rcases MyClassical.choose_spec (MyFun.exists_unique_of_bijective hf hyfidom)
    with ⟨hx, h, h'⟩
  have hPfiyy : f.prop ((f.inv hf).eval y hyfidom) y := by
    dsimp only [MyFun.inv]
    rw [MyFun.from_fun.eval]
    have := (MyFun.def f hx hyfidom).mp
    exact this h.symm
  have := (MyFun.def f hfiyfdom hyfidom).mpr hPfiyy
  exact this.symm

theorem finv_bij {f : MyFun α β} (hf : f.isBijective) :
  (f.inv hf).isBijective := by
  have hf : f.isBijective := hf
  dsimp only [MyFun.isBijective] at hf
  rcases hf with ⟨hinj, hsurj⟩
  dsimp only [MyFun.isBijective]
  constructor
  · dsimp only [MyFun.isInjective]
    intro y y' hy hy' hyy'
    intro hfiyfiy'
    dsimp only [MyFun.isSurjective] at hsurj
    have hyfcodom : y ∈ f.codomain := by
      dsimp only [MyFun.inv] at hy
      dsimp only [MyFun.from_fun] at hy
      exact hy
    rcases hsurj y hyfcodom with ⟨x, hxfdom, hfxy⟩
    have hy'fcodom : y' ∈ f.codomain := by
      dsimp only [MyFun.inv] at hy'
      dsimp only [MyFun.from_fun] at hy'
      exact hy'
    rcases hsurj y' hy'fcodom with ⟨x', hx'fdom, hfx'y'⟩
    have hfxfidom : (f.eval x hxfdom) ∈ (f.inv hf).domain := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact f.eval_codomain hxfdom
    have hfiyfifx :
      (f.inv hf).eval y hy =
        (f.inv hf).eval (f.eval x hxfdom) hfxfidom :=
      MyFun.substitute (f.inv hf) hy hfxfidom hfxy.symm
    rw [hfiyfifx] at hfiyfiy'
    have hfx'fidom : (f.eval x' hx'fdom) ∈ (f.inv hf).domain := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact f.eval_codomain hx'fdom
    have hfiy'fifx' :
      (f.inv hf).eval y' hy' =
        (f.inv hf).eval (f.eval x' hx'fdom) hfx'fidom :=
      MyFun.substitute (f.inv hf) hy' hfx'fidom hfx'y'.symm
    rw [hfiy'fifx'] at hfiyfiy'
    have hxfifdom : x ∈ (f.comp (f.inv hf) (aux₁ hf)).domain := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    rw [← MyFun.comp.eval (aux₁ hf) hxfdom hfxfidom hxfifdom] at hfiyfiy'
    have hx'fifdom : x' ∈ (f.comp (f.inv hf) (aux₁ hf)).domain := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hx'fdom
    rw [← MyFun.comp.eval (aux₁ hf) hx'fdom hfx'fidom hx'fifdom] at hfiyfiy'
    rw [finv_f hf hxfdom] at hfiyfiy'
    rw [finv_f hf hx'fdom] at hfiyfiy'
    have hfxfx' : f.eval x hxfdom = f.eval x' hx'fdom :=
      MyFun.substitute f hxfdom hx'fdom hfiyfiy'
    rw [hfxy] at hfxfx'
    rw [hfx'y'] at hfxfx'
    exact hyy' hfxfx'
  · dsimp only [MyFun.isSurjective]
    intro x hxficodom
    have hxfdom : x ∈ f.domain := by
      dsimp only [MyFun.inv]
      exact hxficodom
    use (f.eval x hxficodom)
    have hfxfidom : f.eval x hxfdom ∈ (f.inv hf).domain := by
      dsimp only [MyFun.inv]
      dsimp only [MyFun.from_fun]
      exact f.eval_codomain hxfdom
    use hfxfidom
    have hxfifdom : x ∈ (f.comp (f.inv hf) (aux₁ hf)).domain := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    rw [← MyFun.comp.eval (aux₁ hf) hxfdom hfxfidom hxfifdom]
    rw [finv_f hf hxfdom]

example (f : MyFun α β) (hf : f.isBijective) :
  (f.inv hf).inv (finv_bij hf) ≃ f := by
  have hfi : (f.inv hf).isBijective := finv_bij hf
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
        x ∈ (f.comp (f.inv hf) (aux₁ hf)).domain := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxfdom
      have hfifiixfifx:
        (((f.inv hf).inv hfi).comp (f.inv hf) hfiicodomfidom).eval x hxfifiidom =
          (f.comp (f.inv hf) (aux₁ hf)).eval x hxfifdom := by
        have hxfiidom : x ∈ ((f.inv hf).inv hfi).domain := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
          exact hxfiidom
        rw [f_finv hfi hxfiidom]
        rw [finv_f hf hxfiidom]
      have hfiixfidom :
        ((f.inv hf).inv hfi).eval x hxfifiidom ∈ (f.inv hf).domain := by
        have hfiixfiicodom:
          ((f.inv hf).inv hfi).eval x hxfifiidom ∈ ((f.inv hf).inv hfi).codomain :=
          ((f.inv hf).inv hfi).eval_codomain hxfifiidom
        have hfiicodomfidom :
          ((f.inv hf).inv hfi).codomain = (f.inv hf).domain := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
        rw [← hfiicodomfidom]
        exact hfiixfiicodom
      have hfxfidom :
        f.eval x hxfifdom ∈ (f.inv hf).domain := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        exact f.eval_codomain hxfdom
      rw [MyFun.comp.eval hfiicodomfidom hxfifiidom hfiixfidom] at hfifiixfifx
      rw [MyFun.comp.eval (aux₁ hf) hxfifdom hfxfidom] at hfifiixfifx
      have hfi := hfi
      dsimp only [MyFun.isBijective] at hfi
      rcases hfi with ⟨hfi_inj, hfi_surj⟩
      rw [(f.inv hf).isInjective_iff] at hfi_inj
      dsimp only [MyFun.isInjective'] at hfi_inj
      exact hfi_inj hfiixfidom hfxfidom hfifiixfifx

end Exercise_3_3_6

-- Exercise 3.3.7
namespace Exercise_3_3_7

theorem aux₁ {f : MyFun α β} {g : MyFun β γ} (hfg : f.codomain = g.domain)
  (hf : f.isBijective) (hg : g.isBijective) :
  (f.comp g hfg).isBijective := by
  dsimp only [MyFun.isBijective]
  constructor
  · dsimp only [MyFun.isInjective]
    intro x x' hxgfdom hx'gfdom hxnx'
    intro hgfxgfx'
    have hxfdom : x ∈ f.domain := by
      dsimp only [MyFun.comp] at hxgfdom
      dsimp only [MyFun.from_fun] at hxgfdom
      exact hxgfdom
    have hfxgdom : f.eval x hxfdom ∈ g.domain := by
      rw [← hfg]
      exact f.eval_codomain hxfdom
    rw [MyFun.comp.eval hfg hxfdom hfxgdom] at hgfxgfx'
    have hx'fdom : x' ∈ f.domain := by
      dsimp only [MyFun.comp] at hx'gfdom
      dsimp only [MyFun.from_fun] at hx'gfdom
      exact hx'gfdom
    have hfx'gdom : f.eval x' hx'fdom ∈ g.domain := by
      rw [← hfg]
      exact f.eval_codomain hx'fdom
    rw [MyFun.comp.eval hfg hx'fdom hfx'gdom] at hgfxgfx'
    dsimp only [MyFun.isBijective] at hg
    rcases hg with ⟨hg_inj, hg_surj⟩
    rw [g.isInjective_iff] at hg_inj
    dsimp only [MyFun.isInjective'] at hg_inj
    have hfxfx' : f.eval x hxfdom = f.eval x' hx'fdom :=
      hg_inj hfxgdom hfx'gdom hgfxgfx'
    dsimp only [MyFun.isBijective] at hf
    rcases hf with ⟨hf_inj, hf_surj⟩
    rw [f.isInjective_iff] at hf_inj
    dsimp only [MyFun.isInjective'] at hf_inj
    have hxx' := hf_inj hxfdom hx'fdom hfxfx'
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
    have hyfcodom : y ∈ f.codomain := by
      rw [hfg]
      exact hygdom
    rcases hf_surj y hyfcodom with ⟨x, hxfdom, hfyx⟩
    use x
    have hxgfdom : x ∈ (f.comp g hfg).domain := by
      dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
      exact hxfdom
    use hxgfdom
    have hfxgdom : f.eval x hxfdom ∈ g.domain := by
      rw [← hfg]
      exact f.eval_codomain hxfdom
    rw [MyFun.comp.eval hfg hxfdom hfxgdom]
    rw [← hgyz]
    exact g.substitute hfxgdom hygdom hfyx

theorem aux₂ {f : MyFun α β} {g : MyFun β γ} (hfg : f.codomain = g.domain)
  (hf : f.isBijective) (hg : g.isBijective) :
  (g.inv hg).codomain = (f.inv hf).domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]
  exact hfg.symm

example (f : MyFun α β) (g : MyFun β γ) (hfg : f.codomain = g.domain)
  (hf : f.isBijective) (hg : g.isBijective) :
  (f.comp g hfg).inv (aux₁ hfg hf hg) ≃
    (g.inv hg).comp (f.inv hf) (aux₂ hfg hf hg) := by
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
      have hzgidom : z ∈ (g.inv hg).domain := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        dsimp only [MyFun.inv] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        dsimp only [MyFun.comp] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        exact hzgfidom
      have hgizfidom : (g.inv hg).eval z hzgidom ∈ (f.inv hf).domain := by
        have : (f.inv hf).domain = (g.inv hg).codomain := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.from_fun]
          exact hfg
        rw [this]
        exact (g.inv hg).eval_codomain hzgidom
      rw [MyFun.comp.eval (aux₂ hfg hf hg) hzgfidom hgizfidom]
      have hg : g.isBijective := hg
      dsimp only [MyFun.isBijective] at hg
      rcases hg with ⟨hg_inj, hg_surj⟩
      dsimp only [MyFun.isSurjective] at hg_surj
      have hzgcodom : z ∈ g.codomain := by
        dsimp only [MyFun.inv] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        dsimp only [MyFun.comp] at hzgfidom
        dsimp only [MyFun.from_fun] at hzgfidom
        exact hzgfidom
      rcases MyFun.exists_unique_of_bijective hg hzgfidom with ⟨y, hygdom, hgyz, hgyz!⟩
      have hgizy : (g.inv hg).eval z hzgfidom = y := by
        have hgygidom : g.eval y hygdom ∈ (g.inv hg).domain := by
          have : (g.inv hg).domain = g.codomain := by
            dsimp only [MyFun.inv]
            dsimp only [MyFun.from_fun]
          rw [this]
          exact g.eval_codomain hygdom
        have :
          (g.inv hg).eval z hzgfidom =
            (g.inv hg).eval (g.eval y hygdom) hgygidom :=
          MyFun.substitute (g.inv hg) hzgfidom hgygidom hgyz.symm
        rw [this]
        rw [← MyFun.comp.eval]
        exact Exercise_3_3_6.finv_f hg hygdom
      have hyfidom : y ∈ (f.inv hf).domain := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        rw [hfg]
        exact hygdom
      rw [MyFun.substitute (f.inv hf) hgizfidom hyfidom hgizy]
      rcases MyFun.exists_unique_of_bijective hf hyfidom with ⟨x, hxfdom, hfxz, hfxz!⟩
      have hfiyx : (f.inv hf).eval y hyfidom = x := by
        have hfxgidom : f.eval x hxfdom ∈ (f.inv hf).domain := by
          have : (f.inv hf).domain = f.codomain := by
            dsimp only [MyFun.inv]
            dsimp only [MyFun.from_fun]
          rw [this]
          exact f.eval_codomain hxfdom
        have :
          (f.inv hf).eval y hyfidom =
            (f.inv hf).eval (f.eval x hxfdom) hfxgidom :=
          MyFun.substitute (f.inv hf) hyfidom hfxgidom hfxz.symm
        rw [this]
        rw [← MyFun.comp.eval]
        exact Exercise_3_3_6.finv_f hf hxfdom
      rw [hfiyx]
      have hgf : (f.comp g hfg).isBijective := aux₁ hfg hf hg
      rcases MyFun.exists_unique_of_bijective hgf hzgfidom with ⟨x', hx'gfdom, hgfx'z, hgfx'z!⟩
      have hgfx'gfidom : (f.comp g hfg).eval x' hx'gfdom ∈ ((f.comp g hfg).inv hgf).domain := by
        have : ((f.comp g hfg).inv hgf).domain = (f.comp g hfg).codomain := by
          dsimp only [MyFun.inv]
          dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
        rw [this]
        exact (f.comp g hfg).eval_codomain hx'gfdom
      have :
        ((f.comp g hfg).inv hgf).eval z hzgfidom =
          ((f.comp g hfg).inv hgf).eval ((f.comp g hfg).eval x' hx'gfdom) hgfx'gfidom :=
        ((f.comp g hfg).inv hgf).substitute hzgfidom hgfx'gfidom hgfx'z.symm
      rw [this]
      have : x' ∈ (f.comp g hfg).domain := hx'gfdom
      have hfg_inv : (f.comp g hfg).codomain = ((f.comp g hfg).inv hgf).domain := by
        dsimp only [MyFun.inv, MyFun.from_fun]
      have hx'comp : x' ∈ ((f.comp g hfg).comp ((f.comp g hfg).inv hgf) hfg_inv).domain := by
        dsimp only [MyFun.comp, MyFun.from_fun]
        exact hx'gfdom
      rw [← MyFun.comp.eval hfg_inv hx'gfdom hgfx'gfidom hx'comp]
      rw [Exercise_3_3_6.finv_f hgf hx'gfdom]
      have hxgfdom : x ∈ (f.comp g hfg).domain := by
        dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        exact hxfdom
      have hgfxz : (f.comp g hfg).eval x hxgfdom = z := by
        have hfxgdom : f.eval x hxfdom ∈ g.domain := by
          rw [← hfg]
          exact f.eval_codomain hxfdom
        rw [MyFun.comp.eval hfg hxfdom hfxgdom]
        have : g.eval (f.eval x hxfdom) hfxgdom = g.eval y hygdom :=
          g.substitute hfxgdom hygdom hfxz
        rw [this]
        exact hgyz
      exact hgfx'z! hxgfdom hgfxz

end Exercise_3_3_7

-- Exercise 3.3.8
namespace Exercise_3_3_8

def ι {X Y : MySet α} (hXY : X ⊆ Y) : MyFun α α := by
  let f : α → α := fun x => x
  have h : ∀ {x : α} (hx : x ∈ X), f x ∈ Y := by
    intro x hx
    exact hXY x hx
  exact MyFun.from_fun h

theorem aux {α : Type} (X : MySet α) : X ⊆ X := by
  exact fun x hx => hx

def ι_id (X : MySet α) := ι (aux X)

-- (a)
namespace Exercise_3_3_8_a

theorem aux₁ {X Y Z : MySet α} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
  (ι hXY).codomain = (ι hYZ).domain := by
  dsimp only [ι]
  dsimp only [MyFun.from_fun]

theorem aux₂ {X Y Z : MySet α} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
  X ⊆ Z := by
  exact MySet.subset_trans hXY hYZ

example {X Y Z : MySet α} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
  (ι hXY).comp (ι hYZ) (aux₁ hXY hYZ) ≃ ι (aux₂ hXY hYZ) := by
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
      have hxXYdom : x ∈ (ι hXY).domain := by
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        dsimp only [ι] at hxXZdom
        dsimp only [MyFun.from_fun] at hxXZdom
        exact hxXZdom
      have hXYxYZdom : (ι hXY).eval x hxXYdom ∈ (ι hYZ).domain := by
        rw [← aux₁ hXY hYZ]
        exact (ι hXY).eval_codomain hxXYdom
      rw [MyFun.comp.eval (aux₁ hXY hYZ) hxXYdom hXYxYZdom]
      dsimp only [ι]
      rw [MyFun.from_fun.eval]
      rw [MyFun.from_fun.eval]
      rw [MyFun.from_fun.eval]

end Exercise_3_3_8_a

-- (b)
namespace Exercise_3_3_8_b

theorem aux₁ {A : MySet α} {f : MyFun α β} (hfdom : f.domain = A) :
  (ι_id A).codomain = f.domain := by
  dsimp only [ι_id]
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact hfdom.symm

example (A : MySet α) (f : MyFun α β) (hfdom : f.domain = A) :
  f ≃ (ι_id A).comp f (aux₁ hfdom) := by
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
      have hxAdom : x ∈ (ι_id A).domain := by
        dsimp only [ι_id]
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        rw [hfdom] at hxfdom
        exact hxfdom
      have hAxfdom : (ι_id A).eval x hxAdom ∈ f.domain := by
        rw [← aux₁ hfdom]
        exact (ι_id A).eval_codomain hxAdom
      rw [MyFun.comp.eval (aux₁ hfdom) hxAdom hAxfdom]
      have : x = (ι_id A).eval x hxAdom := by
        dsimp only [ι_id]
        dsimp only [ι]
        rw [MyFun.from_fun.eval]
      exact f.substitute hxfdom hAxfdom this

theorem aux₂ {B : MySet β} {f : MyFun α β} (hfcodom : f.codomain = B) :
  f.codomain = (ι_id B).domain := by
  dsimp only [ι_id]
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact hfcodom

example (B : MySet β) (f : MyFun α β) (hfcodom : f.codomain = B) :
  f ≃ f.comp (ι_id B) (aux₂ hfcodom) := by
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
      have hfxBdom : f.eval x hxfdom ∈ (ι_id B).domain := by
        have : (ι_id B).domain = f.codomain := by
          dsimp only [ι_id]
          dsimp only [ι]
          dsimp only [MyFun.from_fun]
          exact hfcodom.symm
        rw [this]
        exact f.eval_codomain hxfdom
      rw [MyFun.comp.eval (aux₂ hfcodom) hxfdom hfxBdom]
      dsimp only [ι_id]
      dsimp only [ι]
      rw [MyFun.from_fun.eval]

end Exercise_3_3_8_b

-- (c)
namespace Exercise_3_3_8_c

theorem aux₁ {f : MyFun α β} (hf : f.isBijective) :
  (f.inv hf).codomain = f.domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

example {B : MySet β} {f : MyFun α β}
  (hfcodom : f.codomain = B) (hf : f.isBijective) :
  (f.inv hf).comp f (aux₁ hf) ≃ ι_id B := by
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
      rw [MyFun.from_fun.eval]
      have hxfidom : x ∈ (f.inv hf).domain := by
        dsimp only [MyFun.inv]
        dsimp only [MyFun.from_fun]
        rw [hfcodom]
        dsimp only [ι_id] at hxBdom
        dsimp only [ι] at hxBdom
        dsimp only [MyFun.from_fun] at hxBdom
        exact hxBdom
      rw [Exercise_3_3_6.f_finv hf hxfidom]

theorem aux₂ {f : MyFun α β} (hf : f.isBijective) :
  f.codomain = (f.inv hf).domain := by
  dsimp only [MyFun.inv]
  dsimp only [MyFun.from_fun]

example {A : MySet α} {f : MyFun α β}
  (hfdom : f.domain = A) (hf : f.isBijective) :
  f.comp (f.inv hf) (aux₂ hf) ≃ ι_id A := by
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
      rw [MyFun.from_fun.eval]
      have hxfdom : x ∈ f.domain := by
        dsimp only [MyFun.comp] at hxfifdom
        dsimp only [MyFun.from_fun] at hxfifdom
        exact hxfifdom
      rw [Exercise_3_3_6.finv_f hf hxfdom]

end Exercise_3_3_8_c

-- (d)
namespace Exercise_3_3_8_d

theorem aux₁ {α : Type} (X Y : MySet α) :
  X ⊆ X ∪ Y := by
  dsimp only [MySet.subset]
  intro x hxX
  rw [MySet.mem_union X Y x]
  exact Or.inl hxX

theorem aux₂ {α : Type} (X Y : MySet α) :
  Y ⊆ X ∪ Y := by
  dsimp only [MySet.subset]
  intro x hxY
  rw [MySet.mem_union X Y x]
  exact Or.inr hxY

theorem aux₃ {α : Type} (X Y : MySet α) (h : MyFun α β)
  (hhdom : h.domain = X ∪ Y) :
  (ι (aux₁ X Y)).codomain = h.domain := by
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact hhdom.symm

theorem aux₄ {α : Type} (X Y : MySet α) (h : MyFun α β)
  (hhdom : h.domain = X ∪ Y) :
  (ι (aux₂ X Y)).codomain = h.domain := by
  dsimp only [ι]
  dsimp only [MyFun.from_fun]
  exact hhdom.symm

example {X Y : MySet α} {Z : MySet β}
  (hXY : MySet.disjoint X Y)
  (f : MyFun α β) (hfdom : f.domain = X) (hfcodom : f.codomain = Z)
  (g : MyFun α β) (hgdom : g.domain = Y) (hgcodom : g.codomain = Z) :
  ∃ (h : MyFun α β) (hhdom : h.domain = X ∪ Y),
    h.codomain = Z ∧
    ((ι (aux₁ X Y)).comp h (aux₃ X Y h hhdom) ≃ f) ∧
    ((ι (aux₂ X Y)).comp h (aux₄ X Y h hhdom) ≃ g) ∧
    (∀ (h' : MyFun α β) (hh'dom : h'.domain = X ∪ Y),
      h'.codomain = Z →
      ((ι (aux₁ X Y)).comp h' (aux₃ X Y h' hh'dom) ≃ f) →
      ((ι (aux₂ X Y)).comp h' (aux₄ X Y h' hh'dom) ≃ g) → h' ≃ h) := by
  let h : MyFun α β := {
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
          exact f.eval_codomain hxfdom
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
          exact g.eval_codomain hxgdom
        · have hxnX : ¬ x ∈ X := by
            intro hxX
            have : x ∈ X ∩ Y := by
              dsimp only [MySet.inter]
              rw [MySet.mem_spec]
              constructor
              · exact hxX
              · exact hxY
            dsimp only [MySet.disjoint] at hXY
            rw [hXY] at this
            exact MySet.not_mem_empty this
          constructor
          · dsimp only [MyFun.prop]
            rw [dif_neg hxnX]
            rw [dif_pos hxY]
          · intro y' hy'Z h
            rw [dif_neg hxnX] at h
            rw [dif_pos hxY] at h
            rw [h]
  }
  have hhdom : h.domain = X ∪ Y := by
    dsimp only [h]
  use h, hhdom
  have hXXY : X ⊆ X ∪ Y := (aux₁ X Y)
  have hYXY : Y ⊆ X ∪ Y := (aux₂ X Y)
  constructor
  · dsimp only [h]
  · constructor
    · dsimp only [MyFun.eq]
      constructor
      · dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        exact hfdom.symm
      · constructor
        · dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
          dsimp only [h]
          exact hfcodom.symm
        · intro x hxhXXYdom hxfdom
          have hXXYcodomhdom : (ι hXXY).codomain = h.domain := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
          have hxXXYdom : x ∈ (ι hXXY).domain := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
            rw [← hfdom]
            exact hxfdom
          have hXXYxhdom : (ι hXXY).eval x hxXXYdom ∈ h.domain := by
            have : h.domain = (ι hXXY).codomain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            rw [this]
            exact (ι hXXY).eval_codomain hxXXYdom
          rw [MyFun.comp.eval hXXYcodomhdom hxXXYdom hXXYxhdom]
          have hxhdom : x ∈ h.domain := by
            dsimp only [h]
            rw [MySet.mem_union X Y x]
            rw [hfdom] at hxfdom
            exact Or.inl hxfdom
          have : h.eval ((ι hXXY).eval x hxXXYdom) hXXYxhdom = h.eval x hxhdom := by
            have : (ι hXXY).eval x hxXXYdom = x := by
              dsimp only [ι]
              rw [MyFun.from_fun.eval]
            exact h.substitute hXXYxhdom hxhdom this
          rw [this]
          have hfxhcodom : f.eval x hxfdom ∈ h.codomain := by
            have : h.codomain = f.codomain := by
              dsimp only [h]
              exact hfcodom.symm
            rw [this]
            exact f.eval_codomain hxfdom
          have : h.prop x (f.eval x hxfdom) := by
            dsimp only [h]
            have hxX : x ∈ X := by
              rw [hfdom] at hxfdom
              exact hxfdom
            rw [dif_pos hxX]
          have := (h.def hxhdom hfxhcodom).mpr this
          exact this.symm
    · dsimp only [MyFun.eq]
      constructor
      · constructor
        · dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
          dsimp only [ι]
          dsimp only [MyFun.from_fun]
          exact hgdom.symm
        · constructor
          · dsimp only [MyFun.comp]
            dsimp only [MyFun.from_fun]
            dsimp only [h]
            exact hgcodom.symm
          · intro x hxhYXYdom hxgdom
            have hYXYcodomhdom : (ι hYXY).codomain = h.domain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            have hxYXYdom : x ∈ (ι hYXY).domain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
              rw [← hgdom]
              exact hxgdom
            have hYXYxhdom : (ι hYXY).eval x hxYXYdom ∈ h.domain := by
              have : h.domain = (ι hYXY).codomain := by
                dsimp only [ι]
                dsimp only [MyFun.from_fun]
              rw [this]
              exact (ι hYXY).eval_codomain hxYXYdom
            rw [MyFun.comp.eval hYXYcodomhdom hxYXYdom hYXYxhdom]
            have hxhdom : x ∈ h.domain := by
              dsimp only [h]
              rw [MySet.mem_union X Y x]
              rw [hgdom] at hxgdom
              exact Or.inr hxgdom
            have : h.eval ((ι hYXY).eval x hxYXYdom) hYXYxhdom = h.eval x hxhdom := by
              have : (ι hYXY).eval x hxYXYdom = x := by
                dsimp only [ι]
                rw [MyFun.from_fun.eval]
              exact h.substitute hYXYxhdom hxhdom this
            rw [this]
            have hxgxhcodom : g.eval x hxgdom ∈ h.codomain := by
              have : h.codomain = g.codomain := by
                dsimp only [h]
                exact hgcodom.symm
              rw [this]
              exact g.eval_codomain hxgdom
            have : h.prop x (g.eval x hxgdom) := by
              dsimp only [h]
              have hxY : x ∈ Y := by
                rw [hgdom] at hxgdom
                exact hxgdom
              have hxnX : ¬ x ∈ X := by
                intro hxX
                have : x ∈ X ∩ Y := by
                  dsimp only [MySet.inter]
                  rw [MySet.mem_spec]
                  constructor
                  · exact hxX
                  · exact hxY
                dsimp only [MySet.disjoint] at hXY
                rw [hXY] at this
                exact MySet.not_mem_empty this
              rw [dif_neg hxnX]
              rw [dif_pos hxY]
            have := (h.def hxhdom hxgxhcodom).mpr this
            exact this.symm
      · intro h' hh'dom hh'codom hh'f hh'g
        constructor
        · dsimp only [h]
          exact hh'dom
        · constructor
          · dsimp only [h]
            exact hh'codom
          · intro x hxh'dom hxhdom
            have : h.prop x (h'.eval x hxh'dom) := by
              dsimp only [h]
              by_cases hxX : x ∈ X
              · rw [dif_pos hxX]
                rcases hh'f with ⟨hh'XXYdomfdom, hh'XXYcodomfcodom, hh'XXYxfx⟩
                have hXXYcodomh'dom : (ι hXXY).codomain = h'.domain := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hh'dom.symm
                have hxh'XXY : x ∈ ((ι hXXY).comp h' hXXYcodomh'dom).domain := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxX
                have hxfdom : x ∈ f.domain := by
                  rw [hfdom]
                  exact hxX
                have :
                  ((ι hXXY).comp h' hXXYcodomh'dom).eval x hxh'XXY =
                    f.eval x hxfdom := hh'XXYxfx hxh'XXY hxfdom
                rw [← this]
                have hXXYxh'dom : (ι hXXY).eval x hxh'XXY ∈ h'.domain := by
                  have : h'.domain = (ι hXXY).codomain := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [this]
                  exact (ι hXXY).eval_codomain hxh'XXY
                rw [MyFun.comp.eval hXXYcodomh'dom hxh'XXY hXXYxh'dom]
                have : x = (ι hXXY).eval x hxh'XXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval]
                exact h'.substitute hxh'dom hXXYxh'dom this
              · rw [dif_neg hxX]
                have hxY : x ∈ Y := by
                  rw [hh'dom] at hxh'dom
                  rw [MySet.mem_union] at hxh'dom
                  rcases hxh'dom with (hxX' | hxY')
                  · exact absurd hxX' hxX
                  · exact hxY'
                rw [dif_pos hxY]
                rcases hh'g with ⟨hh'YXYdomgdom, hh'YXYcodomgcodom, hh'YXYxgx⟩
                have hYXYcodomh'dom : (ι hYXY).codomain = h'.domain := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hh'dom.symm
                have hxh'YXY : x ∈ ((ι hYXY).comp h' hYXYcodomh'dom).domain := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxY
                have hxgdom : x ∈ g.domain := by
                  rw [hgdom]
                  exact hxY
                have :
                  ((ι hYXY).comp h' hYXYcodomh'dom).eval x hxh'YXY =
                    g.eval x hxgdom := hh'YXYxgx hxh'YXY hxgdom
                rw [← this]
                have hYXYxh'dom : (ι hYXY).eval x hxh'YXY ∈ h'.domain := by
                  have : h'.domain = (ι hYXY).codomain := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [this]
                  exact (ι hYXY).eval_codomain hxh'YXY
                rw [MyFun.comp.eval hYXYcodomh'dom hxh'YXY hYXYxh'dom]
                have : x = (ι hYXY).eval x hxh'YXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval]
                exact h'.substitute hxh'dom hYXYxh'dom this
            have hh'xhcodom : h'.eval x hxh'dom ∈ h.codomain := by
              have : h.codomain = h'.codomain := by
                dsimp only [h]
                exact hh'codom.symm
              rw [this]
              exact h'.eval_codomain hxh'dom
            refine (h.def hxhdom hh'xhcodom).mpr this

end Exercise_3_3_8_d

-- (e)
namespace Exercise_3_3_8_e

open Exercise_3_3_8_d

theorem aux₅ {x : α} {X Y : MySet α}
  {f : MyFun α β} (hfdom : f.domain = X) :
  x ∈ X ∩ Y → x ∈ f.domain := by
  intro hxXY
  rw [MySet.mem_inter X Y x] at hxXY
  rw [hfdom]
  exact hxXY.left

theorem aux₆ {x : α} {X Y : MySet α}
  {g : MyFun α β} (hgdom : g.domain = Y) :
  x ∈ X ∩ Y → x ∈ g.domain := by
  intro hxXY
  rw [MySet.mem_inter X Y x] at hxXY
  rw [hgdom]
  exact hxXY.right

example {X Y : MySet α} {Z : MySet β}
  (f : MyFun α β) (hfdom : f.domain = X) (hfcodom : f.codomain = Z)
  (g : MyFun α β) (hgdom : g.domain = Y) (hgcodom : g.codomain = Z)
  (hfg : ∀ (x : α) (hx : x ∈ X ∩ Y),
    f.eval x (aux₅ hfdom hx) = g.eval x (aux₆ hgdom hx)) :
  ∃ (h : MyFun α β) (hhdom : h.domain = X ∪ Y),
    h.codomain = Z ∧
    ((ι (aux₁ X Y)).comp h (aux₃ X Y h hhdom) ≃ f) ∧
    ((ι (aux₂ X Y)).comp h (aux₄ X Y h hhdom) ≃ g) ∧
    (∀ (h' : MyFun α β) (hh'dom : h'.domain = X ∪ Y),
      h'.codomain = Z →
      ((ι (aux₁ X Y)).comp h' (aux₃ X Y h' hh'dom) ≃ f) →
      ((ι (aux₂ X Y)).comp h' (aux₄ X Y h' hh'dom) ≃ g) → h' ≃ h) := by
  let h : MyFun α β := {
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
          exact f.eval_codomain hxfdom
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
          exact g.eval_codomain hxgdom
        · constructor
          · dsimp only [MyFun.prop]
            rw [dif_pos hxY]
            by_cases hxX : x ∈ X
            · rw [dif_pos hxX]
              have hxXY : x ∈ X ∩ Y := by
                dsimp only [MySet.inter]
                rw [MySet.mem_spec]
                constructor
                · exact hxX
                · exact hxY
              exact (hfg x hxXY).symm
            · rw [dif_neg hxX]
          · intro y' hy'Z h
            rw [dif_pos hxY] at h
            by_cases hxX : x ∈ X
            · rw [dif_pos hxX] at h
              have hxXY : x ∈ X ∩ Y := by
                dsimp only [MySet.inter]
                rw [MySet.mem_spec]
                constructor
                · exact hxX
                · exact hxY
              rw [h]
              exact (hfg x hxXY).symm
            · rw [dif_neg hxX] at h
              exact h.symm
  }
  have hhdom : h.domain = X ∪ Y := by
    dsimp only [h]
  use h, hhdom
  have hXXY : X ⊆ X ∪ Y := (aux₁ X Y)
  have hYXY : Y ⊆ X ∪ Y := (aux₂ X Y)
  constructor
  · dsimp only [h]
  · constructor
    · dsimp only [MyFun.eq]
      constructor
      · dsimp only [MyFun.comp]
        dsimp only [MyFun.from_fun]
        dsimp only [ι]
        dsimp only [MyFun.from_fun]
        exact hfdom.symm
      · constructor
        · dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
          dsimp only [h]
          exact hfcodom.symm
        · intro x hxhXXYdom hxfdom
          have hXXYcodomhdom : (ι hXXY).codomain = h.domain := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
          have hxXXYdom : x ∈ (ι hXXY).domain := by
            dsimp only [ι]
            dsimp only [MyFun.from_fun]
            rw [← hfdom]
            exact hxfdom
          have hXXYxhdom : (ι hXXY).eval x hxXXYdom ∈ h.domain := by
            have : h.domain = (ι hXXY).codomain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            rw [this]
            exact (ι hXXY).eval_codomain hxXXYdom
          rw [MyFun.comp.eval hXXYcodomhdom hxXXYdom hXXYxhdom]
          have hxhdom : x ∈ h.domain := by
            dsimp only [h]
            rw [MySet.mem_union X Y x]
            rw [hfdom] at hxfdom
            exact Or.inl hxfdom
          have : h.eval ((ι hXXY).eval x hxXXYdom) hXXYxhdom = h.eval x hxhdom := by
            have : (ι hXXY).eval x hxXXYdom = x := by
              dsimp only [ι]
              rw [MyFun.from_fun.eval]
            exact h.substitute hXXYxhdom hxhdom this
          rw [this]
          have hfxhcodom : f.eval x hxfdom ∈ h.codomain := by
            have : h.codomain = f.codomain := by
              dsimp only [h]
              exact hfcodom.symm
            rw [this]
            exact f.eval_codomain hxfdom
          have : h.prop x (f.eval x hxfdom) := by
            dsimp only [h]
            have hxX : x ∈ X := by
              rw [hfdom] at hxfdom
              exact hxfdom
            rw [dif_pos hxX]
          have := (h.def hxhdom hfxhcodom).mpr this
          exact this.symm
    · dsimp only [MyFun.eq]
      constructor
      · constructor
        · dsimp only [MyFun.comp]
          dsimp only [MyFun.from_fun]
          dsimp only [ι]
          dsimp only [MyFun.from_fun]
          exact hgdom.symm
        · constructor
          · dsimp only [MyFun.comp]
            dsimp only [MyFun.from_fun]
            dsimp only [h]
            exact hgcodom.symm
          · intro x hxhYXYdom hxgdom
            have hYXYcodomhdom : (ι hYXY).codomain = h.domain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
            have hxYXYdom : x ∈ (ι hYXY).domain := by
              dsimp only [ι]
              dsimp only [MyFun.from_fun]
              rw [← hgdom]
              exact hxgdom
            have hYXYxhdom : (ι hYXY).eval x hxYXYdom ∈ h.domain := by
              have : h.domain = (ι hYXY).codomain := by
                dsimp only [ι]
                dsimp only [MyFun.from_fun]
              rw [this]
              exact (ι hYXY).eval_codomain hxYXYdom
            rw [MyFun.comp.eval hYXYcodomhdom hxYXYdom hYXYxhdom]
            have hxhdom : x ∈ h.domain := by
              dsimp only [h]
              rw [MySet.mem_union X Y x]
              rw [hgdom] at hxgdom
              exact Or.inr hxgdom
            have : h.eval ((ι hYXY).eval x hxYXYdom) hYXYxhdom = h.eval x hxhdom := by
              have : (ι hYXY).eval x hxYXYdom = x := by
                dsimp only [ι]
                rw [MyFun.from_fun.eval]
              exact h.substitute hYXYxhdom hxhdom this
            rw [this]
            have hxgxhcodom : g.eval x hxgdom ∈ h.codomain := by
              have : h.codomain = g.codomain := by
                dsimp only [h]
                exact hgcodom.symm
              rw [this]
              exact g.eval_codomain hxgdom
            have : h.prop x (g.eval x hxgdom) := by
              dsimp only [h]
              have hxY : x ∈ Y := by
                rw [hgdom] at hxgdom
                exact hxgdom
              by_cases hxX : x ∈ X
              · rw [dif_pos hxX]
                have hxXY : x ∈ X ∩ Y := by
                  dsimp only [MySet.inter]
                  rw [MySet.mem_spec]
                  constructor
                  · exact hxX
                  · exact hxY
                exact (hfg x hxXY).symm
              · rw [dif_neg hxX]
                rw [dif_pos hxY]
            have := (h.def hxhdom hxgxhcodom).mpr this
            exact this.symm
      · intro h' hh'dom hh'codom hh'f hh'g
        constructor
        · dsimp only [h]
          exact hh'dom
        · constructor
          · dsimp only [h]
            exact hh'codom
          · intro x hxh'dom hxhdom
            have : h.prop x (h'.eval x hxh'dom) := by
              dsimp only [h]
              by_cases hxX : x ∈ X
              · rw [dif_pos hxX]
                rcases hh'f with ⟨hh'XXYdomfdom, hh'XXYcodomfcodom, hh'XXYxfx⟩
                have hXXYcodomh'dom : (ι hXXY).codomain = h'.domain := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hh'dom.symm
                have hxh'XXY : x ∈ ((ι hXXY).comp h' hXXYcodomh'dom).domain := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxX
                have hxfdom : x ∈ f.domain := by
                  rw [hfdom]
                  exact hxX
                have :
                  ((ι hXXY).comp h' hXXYcodomh'dom).eval x hxh'XXY =
                    f.eval x hxfdom := hh'XXYxfx hxh'XXY hxfdom
                rw [← this]
                have hXXYxh'dom : (ι hXXY).eval x hxh'XXY ∈ h'.domain := by
                  have : h'.domain = (ι hXXY).codomain := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [this]
                  exact (ι hXXY).eval_codomain hxh'XXY
                rw [MyFun.comp.eval hXXYcodomh'dom hxh'XXY hXXYxh'dom]
                have : x = (ι hXXY).eval x hxh'XXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval]
                exact h'.substitute hxh'dom hXXYxh'dom this
              · rw [dif_neg hxX]
                have hxY : x ∈ Y := by
                  rw [hh'dom] at hxh'dom
                  rw [MySet.mem_union] at hxh'dom
                  rcases hxh'dom with (hxX' | hxY')
                  · exact absurd hxX' hxX
                  · exact hxY'
                rw [dif_pos hxY]
                rcases hh'g with ⟨hh'YXYdomgdom, hh'YXYcodomgcodom, hh'YXYxgx⟩
                have hYXYcodomh'dom : (ι hYXY).codomain = h'.domain := by
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hh'dom.symm
                have hxh'YXY : x ∈ ((ι hYXY).comp h' hYXYcodomh'dom).domain := by
                  dsimp only [MyFun.comp]
                  dsimp only [MyFun.from_fun]
                  dsimp only [ι]
                  dsimp only [MyFun.from_fun]
                  exact hxY
                have hxgdom : x ∈ g.domain := by
                  rw [hgdom]
                  exact hxY
                have :
                  ((ι hYXY).comp h' hYXYcodomh'dom).eval x hxh'YXY =
                    g.eval x hxgdom := hh'YXYxgx hxh'YXY hxgdom
                rw [← this]
                have hYXYxh'dom : (ι hYXY).eval x hxh'YXY ∈ h'.domain := by
                  have : h'.domain = (ι hYXY).codomain := by
                    dsimp only [ι]
                    dsimp only [MyFun.from_fun]
                    exact hh'dom
                  rw [this]
                  exact (ι hYXY).eval_codomain hxh'YXY
                rw [MyFun.comp.eval hYXYcodomh'dom hxh'YXY hYXYxh'dom]
                have : x = (ι hYXY).eval x hxh'YXY := by
                  dsimp only [ι]
                  rw [MyFun.from_fun.eval]
                exact h'.substitute hxh'dom hYXYxh'dom this
            have hh'xhcodom : h'.eval x hxh'dom ∈ h.codomain := by
              have : h.codomain = h'.codomain := by
                dsimp only [h]
                exact hh'codom.symm
              rw [this]
              exact h'.eval_codomain hxh'dom
            refine (h.def hxhdom hh'xhcodom).mpr this

end Exercise_3_3_8_e

end Exercise_3_3_8

end Exercises -- section Exercises
