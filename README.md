# Formalization of "Analysis I" by Terence Tao

The goal of this project is to formalize the book ["Analysis I"](https://terrytao.wordpress.com/books/analysis-i/) by Terence Tao, including the main text and the exercises. This is a work in progress. The formalization is done in [Lean 4](https://lean-lang.org/). The repository pins a [Mathlib](https://leanprover-community.github.io/) version in `lakefile.lean` to anchor the toolchain, but **no module inside [Lean4AnalysisTao/](Lean4AnalysisTao/) imports Mathlib**; the development rebuilds every structure it needs from the Peano axioms upward, so that the Lean proofs can mirror Tao's axiomatic development.

> **Note.** Tao has since started his own [Lean companion](https://github.com/teorth/analysis), which is more advanced. This repo is a personal learning exercise kept as an alternative take, not a competitor, and it diverges in three ways: (1) no Mathlib anywhere, not just the early chapters; (2) the end-of-section exercises are formalized too, not left as `sorry`; (3) a strict uniform proof [style](#style) so the corpus reads as structured data.

## Progress

**(Updated on 2026-04-14)**

### Main text

- [x] 2. [Starting at the Beginning: The Natural Numbers](Lean4AnalysisTao/C02_NaturalNumbers)
    - [x] 2.1. [The Peano axioms](Lean4AnalysisTao/C02_NaturalNumbers/S01_PeanoAxioms.lean)
    - [x] 2.2. [Addition](Lean4AnalysisTao/C02_NaturalNumbers/S02_Addition.lean)
    - [x] 2.3. [Multiplication](Lean4AnalysisTao/C02_NaturalNumbers/S03_Multiplication.lean)
- [ ] 3. [Set Theory](Lean4AnalysisTao/C03_SetTheory)
    - [x] 3.1. [Fundamentals](Lean4AnalysisTao/C03_SetTheory/S01_Fundamentals.lean)
    - [ ] 3.2. [Russell's Paradox](Lean4AnalysisTao/C03_SetTheory/S02_RussellParadox.lean)
    - [x] 3.3. [Functions](Lean4AnalysisTao/C03_SetTheory/S03_Functions.lean)
    - [ ] 3.4. Images and Inverse Images
    - [ ] 3.5. Cartesian Products
    - [ ] 3.6. Cardinality of Sets
- [ ] 4. Integers and Rationals
- [ ] 5. The Real Numbers
- [ ] 6. Limits of Sequences
- [ ] 7. Series
- [ ] 8. Infinite Sets
- [ ] 9. Continuous Functions on R
- [ ] 10. Differentiation of Functions
- [ ] 11. The Riemann Integral
- [ ] Appendix A: The Basics of Mathematical Logic
- [ ] Appendix B: The Decimal System

### Solutions to exercises

- [x] 2. [Starting at the Beginning: The Natural Numbers](Lean4AnalysisTao/C02_NaturalNumbers/solutions/)
    - [x] 2.2. [Addition](Lean4AnalysisTao/C02_NaturalNumbers/solutions/Solutions_S02_Addition.lean)
    - [x] 2.3. [Multiplication](Lean4AnalysisTao/C02_NaturalNumbers/solutions/Solutions_S03_Multiplication.lean)
- [ ] 3. [Set Theory](Lean4AnalysisTao/C03_SetTheory/solutions/)
    - [x] 3.1. [Fundamentals](Lean4AnalysisTao/C03_SetTheory/solutions/Solutions_S01_Fundamentals.lean)
    - [x] 3.2. [Russell's Paradox](Lean4AnalysisTao/C03_SetTheory/solutions/Solutions_S02_RussellParadox.lean)
    - [x] 3.3. [Functions](Lean4AnalysisTao/C03_SetTheory/solutions/Solutions_S03_Functions.lean)
    - [ ] 3.4. Images and Inverse Images
    - [ ] 3.5. Cartesian Products
    - [ ] 3.6. Cardinality of Sets
- [ ] 4. Integers and Rationals
- [ ] 5. The Real Numbers
- [ ] 6. Limits of Sequences
- [ ] 7. Series
- [ ] 8. Infinite Sets
- [ ] 9. Continuous Functions on R
- [ ] 10. Differentiation of Functions
- [ ] 11. The Riemann Integral
- [ ] Appendix A: The Basics of Mathematical Logic
- [ ] Appendix B: The Decimal System

## Style

Proofs decompose into a small uniform set of discrete named inference steps, so the corpus reads as structured training data. Five concerns organise the rules: **fidelity**, **explicitness**, **uniformity**, **articulation**, **layout**.

### Fidelity

- No `import Mathlib.*` under `Lean4AnalysisTao/`; re-derive any missing lemma from current-chapter axioms.
- Main-text `S*.lean` files contain only what Tao states, in his order. Scaffolding (bridging lemmas, strengthened axioms, type-hierarchy facts) goes in `S*_Extras.lean` or the chapter's `Util.lean`.
- Main-text proofs mirror Tao's argument. Exercise solutions (`Solutions_S*`) are free, but should reach first for earlier in-chapter lemmas.
- Prefix every numbered book item with a `-- <Kind> X.Y.Z` anchor (`-- Definition 3.1.1`, `-- Lemma 2.2.3`, `-- Axiom 3.9`, `-- Proposition 2.2.4`, `-- Exercise 3.2.2`) for cross-reference.

### Explicitness

Every binder, value, and identifier is spelled out; nothing is inferred silently.

- Only `{α : Type}` / `{α : Sort u}` stay implicit. All other arguments become explicit `(x : T)` binders; `[Inst]` stays in bracket form.
- Lift leading `∀` and `→` into binders on every named binding (`axiom` / `theorem` / `def` / `lemma` / `example` / `instance` / `have` / `let`): `∀ x, P x → Q x` becomes `(x : T) (hp : P x) : Q x`. Exception: keep `∀` in the conclusion of higher-order principles whose consumers unify against the `∀`-shape (induction schemes, choice, pointwise-equality lemmas fed to `rw` / `congrArg`).
- Always annotate `have` with a type: `have hfoo : T := …`.
- No `_` in applied or type-hole positions: spell `congrArg P h`, `Exists.intro a h`, `Eq.trans h₁ h₂`. Reach for `@` only when unification genuinely can't resolve a type implicit; prefer dropping `@` and passing arguments positionally. `_` is allowed only to discard names in binding patterns; `?_` only as a `refine` hole.
- Numeric literals carry type ascriptions (`(3 : MyNat)`).
- Fully-qualified names only: `Eq.symm h`, `And.left h`, `Iff.mp h`, `Or.elim h f g`, `Or.inl x`, `And.intro hp hq`, `Exists.intro a h`. No dot-projection (`h.symm`), no leading-dot constructors (`.inl x`), no anonymous `⟨…⟩` in term position — not at the top of a term, not nested as an argument (`Or.inr ⟨h1, h2⟩` becomes `Or.inr (And.intro h1 h2)`). Destructor-pattern `⟨…⟩` in `intro` / `rcases` / `let` / `fun` is fine.
- Prefix proof hypotheses with `h`: `hle`, `hlt`, `hpos`, `hne`, `hxA`, `hfdom`. Value binders keep their natural name (`x`, `n`, `A`, `f`).
- No `show T from e`; use `(e : T)` ascription.

### Uniformity

Each inference move has one canonical form.

- Tactic whitelist. Every `by` block may use only: `intro`, `have`, `let`, `exact`, `refine`, `rw`, `rcases`, `by_contra`, `by_cases`, `use`, `constructor`, `dsimp only [defs]` (the `only` form is mandatory), `rfl`. Everything else is banned, including `simp`, `simp only`, `omega`, `decide`, `tauto`, `linarith`, `aesop`, `norm_num`, `ring`, `field_simp`, `push_neg`, `trivial`, `assumption`, `apply`, `show`, `exfalso`, `left`, `right`, `cases`, `obtain`, `rintro`, `match`, `change`, `subst`, `suffices`, `contradiction`, `ext`, `funext`, `unfold`, `<;>`. `refine` subsumes `apply` / `left` / `right` / `exfalso`; `rcases` subsumes `cases` / `rintro` / `obtain`.
- No `▸`: use `rw` or `Eq.mpr (congrArg P h) x`. `▸` hides direction.
- Macro bodies that implement a whitelisted tactic may use term-position `⟨…⟩` and `first` where genuinely required for the expansion, but nothing else from the banned list.
- Term-mode `match`, `let`, `funext`, `fun`, and destructor-pattern `⟨…⟩` are not tactics and are unrestricted.

### Articulation

Every logical joint is named and visible at the top level of its block.

- Name every hypothesis and intermediate fact (`hle`, `hlt`, `hpos`, …); no anonymous `this`.
- `by_contra` and `by_cases` always name their hypothesis: `by_contra hne`, `by_cases hx : x ∈ A`.
- No inline `by` blocks for proofs and no proof-producing `fun` in applied position; lift to a named `have hfoo : T := by …` above. Single exception: a `fun` passed as a non-lifted argument that produces a value, a predicate, or a structure field (e.g. `prop := fun x y => by …` inside a struct literal, or the `p` argument to `choose_spec`). The `by` block inside such a `fun` inherits the exception.
- One tactic per line, one lemma per tactic: `rw [h1]` then `rw [h2]` on separate lines, not `rw [h1, h2]`; same for `dsimp only`. No `;` chaining.
- Every subgoal opens with `·`.

### Layout

- Cap line length at ~100 characters; long lines usually mean a step is doing too much.
- Term RHS breaks: `:=` ends the line, term on next indented line. Tactic RHS stays inline as `:= by`, tactics on subsequent lines.
- Canonical signature layout for every named binding: name on line 1; one binder group per line indented 4, last binder line ends ` :`; conclusion on its own line indented 4, then `:= by` or `:=`. No inline `name : concl := body`.
- Canonical `match` layout (term-mode): `match` and its scrutinees on line 1, `with` at the end of that line (or on its own line if the scrutinee list wraps); each arm on its own line starting with `|`, indented to match the `match` keyword; arm RHS inline after `=>` for short terms, or broken to the next indented line for long ones.

## License

The project is licensed under the MIT License. See [LICENSE](LICENSE) for details.

## Acknowledgements

- The book itself: Terence Tao, [_Analysis I_](https://terrytao.wordpress.com/books/analysis-i/).
- The [Lean](https://lean-lang.org/) and [Mathlib](https://leanprover-community.github.io/) communities for the language, the tooling, and for showing what a modern proof assistant can look like.
- AI assistance from [GitHub Copilot](https://github.com/features/copilot), [Google Gemini](https://gemini.google.com/), and [Anthropic Claude](https://claude.ai/) during formalization.