import Lean4AnalysisTao.C03_SetTheory.S02_RussellParadox

-- Exercise 3.2.1
-- Two proofs: via Axiom 3.3, and via Axiom 3.9 with `P x := False`.

example :
    ∃ (E : MySet MyNat), ∀ (x : MyNat), x ∉ E := by
  use (∅ : MySet MyNat)
  intro x
  exact @MySet.not_mem_empty MyNat (MySet MyNat) x

example :
    ∃ (E : MySet MyNat), ∀ (x : MyNat), x ∉ E := by
  use (Axiom_3_9.MySet.univ_spec (fun (_ : MyNat) => False))
  intro x hx
  rw [@Axiom_3_9.MySet.mem_univ_spec MyNat
      (fun (_ : MyNat) => False) x] at hx
  exact hx

-- Exercise 3.2.2 (first half): A ∉ A, via regularity applied to ⦃A⦄.
example
    (A : MySet MyNat) :
    A ∉ A := by
  intro hAA
  have hA_mem_SA :
      A ∈ (⦃A⦄ : MySet MyNat) := by
    rw [@MySet.mem_singleton (MySet MyNat) (MySet MyNat) A A]
  have hnonempty :
      MySet.nonempty (⦃A⦄ : MySet MyNat) := by
    intro hemp
    rw [hemp] at hA_mem_SA
    exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) A hA_mem_SA
  have hreg :
      (∃ (x : MySet MyNat),
          x ∈ (⦃A⦄ : MySet MyNat)
          ∧ MySet.disjoint x (⦃A⦄ : MySet MyNat))
        ∨ (∃ (ν : Type) (x : ν),
            x ∈ (⦃A⦄ : MySet MyNat) ∧ ν ≠ MySet MyNat) :=
    @MySet.regularity MyNat (⦃A⦄ : MySet MyNat) hnonempty
  rcases hreg with ⟨x, hxmem, hdisj⟩ | ⟨ν, x, hxmem, hνne⟩
  · rw [@MySet.mem_singleton (MySet MyNat) (MySet MyNat) A x] at hxmem
    rw [hxmem] at hdisj
    rw [MySet.disjoint] at hdisj
    have hA_inter :
        A ∈ A ∩ (⦃A⦄ : MySet MyNat) := by
      rw [@MySet.mem_inter_obj MyNat A
          (⦃A⦄ : MySet MyNat) (MySet MyNat) A]
      exact And.intro hAA hA_mem_SA
    rw [hdisj] at hA_inter
    exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) A hA_inter
  · rw [@MySet.mem_singleton_obj (MySet MyNat) (MySet MyNat) A ν x] at hxmem
    exact hνne (type_eq_of_heq hxmem)

-- Exercise 3.2.2 (second half), via regularity applied to ⦃A, B⦄.
example
    (A B : MySet MyNat) :
    A ∉ B ∨ B ∉ A := by
  have hA_mem_PAB :
      A ∈ (⦃A, B⦄ : MySet MyNat) := by
    rw [@MySet.mem_pair (MySet MyNat) (MySet MyNat) A B A]
    exact Or.inl rfl
  have hB_mem_PAB :
      B ∈ (⦃A, B⦄ : MySet MyNat) := by
    rw [@MySet.mem_pair (MySet MyNat) (MySet MyNat) A B B]
    exact Or.inr rfl
  have hnonempty :
      MySet.nonempty (⦃A, B⦄ : MySet MyNat) := by
    intro hemp
    rw [hemp] at hA_mem_PAB
    exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) A hA_mem_PAB
  have hreg :
      (∃ (x : MySet MyNat),
          x ∈ (⦃A, B⦄ : MySet MyNat)
          ∧ MySet.disjoint x (⦃A, B⦄ : MySet MyNat))
        ∨ (∃ (ν : Type) (x : ν),
            x ∈ (⦃A, B⦄ : MySet MyNat) ∧ ν ≠ MySet MyNat) :=
    @MySet.regularity MyNat (⦃A, B⦄ : MySet MyNat) hnonempty
  rcases hreg with ⟨x, hxmem, hdisj⟩ | ⟨ν, x, hxmem, hνne⟩
  · rw [@MySet.mem_pair (MySet MyNat) (MySet MyNat) A B x] at hxmem
    rw [MySet.disjoint] at hdisj
    rcases hxmem with hxA | hxB
    · rw [hxA] at hdisj
      refine Or.inr ?_
      intro hBA
      have hB_inter :
          B ∈ A ∩ (⦃A, B⦄ : MySet MyNat) := by
        rw [@MySet.mem_inter_obj MyNat A
            (⦃A, B⦄ : MySet MyNat) (MySet MyNat) B]
        exact And.intro hBA hB_mem_PAB
      rw [hdisj] at hB_inter
      exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) B hB_inter
    · rw [hxB] at hdisj
      refine Or.inl ?_
      intro hAB
      have hA_inter :
          A ∈ B ∩ (⦃A, B⦄ : MySet MyNat) := by
        rw [@MySet.mem_inter_obj MyNat B
            (⦃A, B⦄ : MySet MyNat) (MySet MyNat) A]
        exact And.intro hAB hA_mem_PAB
      rw [hdisj] at hA_inter
      exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) A hA_inter
  · rw [@MySet.mem_pair_obj (MySet MyNat) (MySet MyNat) A B ν x] at hxmem
    rcases hxmem with hxA | hxB
    · exact False.elim (hνne (type_eq_of_heq hxA))
    · exact False.elim (hνne (type_eq_of_heq hxB))

-- Exercise 3.2.3
example :
    ∃ (Ω : MySet MyNat), ∀ (x : MyNat), x ∈ Ω := by
  use MySet.Nat.set
  exact MySet.Nat.is_nat
