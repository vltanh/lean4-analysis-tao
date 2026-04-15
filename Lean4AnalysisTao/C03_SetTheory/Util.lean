import Lean4AnalysisTao.C02_NaturalNumbers.S01_PeanoAxioms

/-- `OfNat MyNat n` instance so numeric literals (e.g. `(3 : MyNat)`)
elaborate via repeated `succ` applications. Chapter 2 works with
`𝟘`/`𝟙`/`𝟚` notation directly and does not need this. -/
noncomputable instance : OfNat MyNat 0 := ⟨MyNat.zero⟩
noncomputable instance {n : Nat} [inst : OfNat MyNat n] : OfNat MyNat (n + 1) :=
  ⟨(inst.ofNat : MyNat)++⟩
