# Formalization of "Analysis I" by Terence Tao

The goal of this project is to formalize the book ["Analysis I"](https://terrytao.wordpress.com/books/analysis-i/) by Terence Tao, including the main text and the exercises. This is a work in progress. The formalization is done in [Lean 4](https://lean-lang.org/). The repository pins a [Mathlib](https://leanprover-community.github.io/) version in `lakefile.lean` to anchor the toolchain, but **no module inside [Lean4AnalysisTao/](Lean4AnalysisTao/) imports Mathlib**; the development rebuilds every structure it needs from the Peano axioms upward, so that the Lean proofs can mirror Tao's axiomatic development.

> **Note.** Tao himself has since begun [a Lean companion to _Analysis I_](https://github.com/teorth/analysis), which started later than this project but is far more advanced and is the canonical reference. This repository is mostly a personal learning exercise, kept around as an alternative take rather than a competitor. Two main scope differences: (1) Tao's companion uses textbook definitions only at the start and transitions to Mathlib from Chapter 3 onward, while this project keeps the from-scratch, no-Mathlib rule in force throughout, which naturally leads to different design choices from Tao's; (2) Tao deliberately leaves the end-of-section exercises as `sorry` for readers, while this project also formalizes the exercise solutions.

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

Proofs in this repo follow specific rules, grouped by concern.

### Scope and faithfulness

- Nothing under `Lean4AnalysisTao/` may `import Mathlib.*`. If a lemma is needed, re-derive it from the axioms of the current chapter.
- Main-text `S*.lean` files contain only what Tao states: the axioms, definitions, lemmas, and theorems from his text, in his order. Anything the formalization needs that is not in the book (strengthened axioms, bridging lemmas, type-hierarchy facts, other scaffolding) goes into the section's `S*_Extras.lean` or the chapter's `Util.lean`, never into the main `S*` file.
- Proofs in the main-text `S*` files must mirror the argument Tao gives in the book; don't substitute a shorter or different proof just to make type-checking work. Exercise solutions (`Solutions_S*`) are free to prove the result any way, but should reach first for the lemmas and techniques introduced earlier in the same chapter.

### Tactic restrictions

- Every tactic block (`by …`) may only use: `intro`, `have`, `let`, `exact`, `refine`, `rw`, `rcases`, `by_contra`, `by_cases`, `use`, `constructor`, `dsimp only [defs]`, and `rfl`. Everything else is banned, in particular `simp` / `simp only`, `omega`, `decide`, `tauto`, `linarith`, `aesop`, `norm_num`, `ring`, `field_simp`, `push_neg`, `trivial`, `assumption`, `apply` (use `refine`), the `show` tactic, `exfalso`, `left`, `right`, `cases`, `obtain`, `rintro`, the `match` tactic, `change`, `subst`, `suffices`, `contradiction`, `ext`, the `funext` tactic, `unfold`, and the `<;>` combinator. Two exemptions: macro bodies in `Lean4AnalysisTao/Util.lean` (they define the whitelisted tactics themselves), and term-mode syntax (`match`, `let`, `show … from …`, `funext`, `fun`, anonymous constructors `⟨…⟩`) which is not a tactic and is unrestricted.
- No `▸` in proofs. Use `rw` (tactic) or `Eq.mpr (congrArg _ h) x` (term). `▸` hides direction and the equality it uses.

### Explicitness

- Only `{α : Type}` / `{α : Sort u}` arguments stay implicit. All other arguments (values, elements, sets, predicates, propositions, proofs/hypotheses) become explicit binders `(x : T)`. Type-class args `[Inst]` stay in bracket form. Do not declare non-type arguments implicit even if Lean could infer them. (`rfl` is exempt.)
- Lift leading `∀` into binders. If a declaration's conclusion begins with `∀`, convert to explicit binder form: `theorem foo : ∀ (x : MyNat), P x := …` becomes `theorem foo (x : MyNat) : P x := …`. Internal `∀` inside the conclusion or a hypothesis body stays in ∀-form.
- Call sites pass explicit arguments positionally. Reach for `@` only when unification genuinely can't resolve a type implicit (rare). Numeric literals carry type ascriptions (`(3 : MyNat)`).
- Never pass `_` in an applied position. Spell out every explicit argument at call sites. `_` is allowed only in binding patterns (`intro _`, `rcases … with ⟨_, hb⟩`, `fun _ => …`) to discard an unused name, and in term-level type-hole positions like `congrArg _ h`. `?_` in `refine` reserved for holes discharged by the next tactic.
- No inline proof-producing `fun` in applied positions. A function-valued argument whose body elaborates to a proof of some `Prop` must be lifted to a named `have hfoo : T := fun … => …` above the step and then referenced. Exception: `fun` producing a value or predicate (e.g. `fun y => y ∈ S ∧ P y` as the `p` argument to `choose_spec`) is unrestricted.
- Use the fully-qualified namespace, not dot-projection. Write `Eq.symm h`, `And.left h`, `Iff.mp h`, `Or.elim h f g`, `Or.inl x`; never the dot-projection shorthand (`h.symm`, `h.left`, `h.mp`) nor the leading-dot constructor (`.inl x`).
- Always annotate `have` with a type. Never `have hfoo := proof`; always `have hfoo : T := proof`.

### Naming

- Name every hypothesis and intermediate fact. Avoid the anonymous `this`; introduce descriptive names (`hle`, `hlt`, `hpos`, …) so proofs read linearly and nested `have`s don't shadow each other.
- `by_contra` always names its hypothesis. Write `by_contra hne`, never bare `by_contra`.

### Structure of a proof

- One tactic per line. Don't chain tactics with `;` inside `by` blocks.
- Every subgoal opens with `·`. After `rcases`, `constructor`, `by_cases`, or multi-hole `refine`, every branch must start with `·`. No relying on goal-order fall-through.
- No inline `by` blocks for proofs. Don't write `exact f (by ...)`, `refine ⟨..., by ..., ...⟩`, or `fun z hz => by ...` that produces a proof. Lift the subproof into a named `have hfoo : T := by ...` above. Exception: `by` inside a function-building lambda that elaborates a non-Prop value is allowed.

### Formatting

- Cap line length at roughly 100 characters. Long lines usually mean a step is doing too much; break into multiple `have` / `let`.
- Line break after `:=` for term RHS. Tactic RHS stays inline as `:= by`, tactics on subsequent lines. Term RHS always breaks: `:=` at end of line, term on next indented line. Applies to `have` / `let`, structure fields, and top-level `def` / `theorem` bodies.
- Canonical signature layout. Every `axiom` / `theorem` / `def` / `lemma` / `example` / `instance`: name on line 1; if it has binders, one binder group (`{…}`, `(…)`, or `[…]`) per line indented 4, last binder line ends ` :`; conclusion on its own line indented 4, followed by `:= by` or `:=`. Zero-binder decls also break the conclusion to a new line. No inline `name : concl := body` form.

## License

The project is licensed under the MIT License. See [LICENSE](LICENSE) for details.

## Acknowledgements

- The book itself: Terence Tao, [_Analysis I_](https://terrytao.wordpress.com/books/analysis-i/).
- The [Lean](https://lean-lang.org/) and [Mathlib](https://leanprover-community.github.io/) communities for the language, the tooling, and for showing what a modern proof assistant can look like.
- AI assistance from [GitHub Copilot](https://github.com/features/copilot), [Google Gemini](https://gemini.google.com/), and [Anthropic Claude](https://claude.ai/) during formalization.