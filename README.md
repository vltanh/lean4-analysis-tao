# Formalization of "Analysis I" by Terence Tao

The goal of this project is to formalize the book ["Analysis I"](https://terrytao.wordpress.com/books/analysis-i/) by Terence Tao, including the main text and the exercises. This is a work in progress. The formalization is done in [Lean 4](https://lean-lang.org/). The repository pins a [Mathlib](https://leanprover-community.github.io/) version in `lakefile.lean` to anchor the toolchain, but **no module inside [Lean4AnalysisTao/](Lean4AnalysisTao/) imports Mathlib** — the development rebuilds every structure it needs from the Peano axioms upward, so that the Lean proofs can mirror Tao's axiomatic development.

We acknowledge the use of AI tools to assist in the formalization process, notably GitHub Copilot.

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
    - [ ] 3.2. Russell's Paradox
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

Proofs in this repo follow some specific rules:

1. **No Mathlib.** Nothing under `Lean4AnalysisTao/` may `import Mathlib.*`. If a lemma is needed, re-derive it from the axioms of the current chapter (main-text content goes in the relevant `S*` file; scaffolding goes in a `Util`/`_Extras` file).
2. **Never rely on implicit inference.** Every lemma application — `rw` / `rewrite`, `exact`, `apply`, `refine`, `have := …`, term-mode application, etc. — must spell out its arguments (both explicit and implicit). Use `@foo a b c` or `foo (x := a) (y := b)` to pin implicits, not `foo`. Numeric literals should carry type ascriptions (`(3 : MyNat)`). This keeps proofs readable and robust to elaboration changes, even when Lean could infer the arguments on its own.
3. **Name every hypothesis and intermediate fact.** Avoid the anonymous `this` — introduce descriptive names (`hle`, `hlt`, `hpos`, …) so proofs read linearly and nested `have`s don't shadow each other.
4. **Paraphrase, don't replace.** Proofs in the main-text `S*` files must mirror the argument Tao gives in the book — don't substitute a shorter or different proof just to make type-checking work. Exercise solutions (`Solutions_S*`) are free to prove the result any way, but should reach first for the lemmas and techniques introduced earlier in the same chapter (Tao's hints often point at specific ones).

## License

The project is licensed under the MIT License. See [LICENSE](LICENSE) for details.