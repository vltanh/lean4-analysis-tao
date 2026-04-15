import Lean4AnalysisTao.C03_SetTheory.S02_RussellParadox

-- Solutions for C03/S02: Set Theory – Russell's Paradox.

-- Exercise 3.2.1
-- Two proofs: (a) direct via Axiom 3.3 `MySet.empty`; (b) faithful to Tao's
-- intent, via Axiom 3.9 with `P x := False` so `⦃| P ⦄` is empty.

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

-- Exercise 3.2.2 (first half): A ∉ A.
-- Apply regularity to the singleton ⦃A⦄ (built with the singleton's α
-- pinned to `MySet MyNat` so the result is itself a `MySet MyNat`).
-- Its only element is A; the first disjunct of regularity gives
-- `disjoint A ⦃A⦄`, and if `A ∈ A` then `A ∈ A ∩ ⦃A⦄` (cross-type
-- `mem_inter_obj` from Extras), contradicting disjointness.
-- The second disjunct is impossible: any element of ⦃A⦄ has type
-- `MySet MyNat` by `mem_singleton_obj` + `type_eq_of_heq`.
example
    (A : MySet MyNat) :
    A ∉ A := by
  intro hAA
  have hA_mem_SA :
      A ∈ (@MySet.singleton (MySet MyNat) (MySet MyNat) A) := by
    rw [@MySet.mem_singleton_obj
        (MySet MyNat) (MySet MyNat) A (MySet MyNat) A]
  have hnonempty :
      (@MySet.singleton (MySet MyNat) (MySet MyNat) A :
        MySet MyNat).nonempty := by
    intro hemp
    rw [hemp] at hA_mem_SA
    exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) A hA_mem_SA
  have hreg :
      (∃ (x : MySet MyNat), x ∈ (@MySet.singleton (MySet MyNat) (MySet MyNat) A)
          ∧ MySet.disjoint x (@MySet.singleton (MySet MyNat) (MySet MyNat) A))
        ∨ (∃ (ν : Type) (x : ν),
            x ∈ (@MySet.singleton (MySet MyNat) (MySet MyNat) A)
            ∧ ν ≠ MySet MyNat) :=
    @MySet.regularity MyNat
      (@MySet.singleton (MySet MyNat) (MySet MyNat) A) hnonempty
  rcases hreg with ⟨x, hxmem, hdisj⟩ | ⟨ν, x, hxmem, hνne⟩
  · rw [@MySet.mem_singleton_obj
        (MySet MyNat) (MySet MyNat) A (MySet MyNat) x] at hxmem
    have hxA : x = A :=
      eq_of_heq hxmem
    rw [hxA] at hdisj
    rw [MySet.disjoint] at hdisj
    have hA_inter :
        A ∈ A ∩ (@MySet.singleton (MySet MyNat) (MySet MyNat) A) := by
      rw [@MySet.mem_inter_obj MyNat A
          (@MySet.singleton (MySet MyNat) (MySet MyNat) A)
          (MySet MyNat) A]
      exact ⟨hAA, hA_mem_SA⟩
    rw [hdisj] at hA_inter
    exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) A hA_inter
  · rw [@MySet.mem_singleton_obj
        (MySet MyNat) (MySet MyNat) A ν x] at hxmem
    exact hνne (type_eq_of_heq hxmem)

-- Exercise 3.2.2 (second half): A ∉ B ∨ B ∉ A.
-- Apply regularity to the pair ⦃A, B⦄ (α pinned so the pair is itself a
-- `MySet MyNat`). First disjunct picks one of A, B as disjoint from the
-- pair; cross-type `mem_inter_obj` then refutes membership of the other.
example
    (A B : MySet MyNat) :
    A ∉ B ∨ B ∉ A := by
  have hA_mem_PAB :
      A ∈ (@MySet.pair (MySet MyNat) (MySet MyNat) A B) := by
    rw [@MySet.mem_pair_obj
        (MySet MyNat) (MySet MyNat) A B (MySet MyNat) A]
    exact Or.inl HEq.rfl
  have hB_mem_PAB :
      B ∈ (@MySet.pair (MySet MyNat) (MySet MyNat) A B) := by
    rw [@MySet.mem_pair_obj
        (MySet MyNat) (MySet MyNat) A B (MySet MyNat) B]
    exact Or.inr HEq.rfl
  have hnonempty :
      (@MySet.pair (MySet MyNat) (MySet MyNat) A B :
        MySet MyNat).nonempty := by
    intro hemp
    rw [hemp] at hA_mem_PAB
    exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) A hA_mem_PAB
  have hreg :
      (∃ (x : MySet MyNat), x ∈ (@MySet.pair (MySet MyNat) (MySet MyNat) A B)
          ∧ MySet.disjoint x (@MySet.pair (MySet MyNat) (MySet MyNat) A B))
        ∨ (∃ (ν : Type) (x : ν),
            x ∈ (@MySet.pair (MySet MyNat) (MySet MyNat) A B)
            ∧ ν ≠ MySet MyNat) :=
    @MySet.regularity MyNat
      (@MySet.pair (MySet MyNat) (MySet MyNat) A B) hnonempty
  rcases hreg with ⟨x, hxmem, hdisj⟩ | ⟨ν, x, hxmem, hνne⟩
  · rw [@MySet.mem_pair_obj
        (MySet MyNat) (MySet MyNat) A B (MySet MyNat) x] at hxmem
    rw [MySet.disjoint] at hdisj
    rcases hxmem with hxA | hxB
    · have hxA' : x = A := eq_of_heq hxA
      rw [hxA'] at hdisj
      refine Or.inr ?_
      intro hBA
      have hB_inter :
          B ∈ A ∩ (@MySet.pair (MySet MyNat) (MySet MyNat) A B) := by
        rw [@MySet.mem_inter_obj MyNat A
            (@MySet.pair (MySet MyNat) (MySet MyNat) A B)
            (MySet MyNat) B]
        exact ⟨hBA, hB_mem_PAB⟩
      rw [hdisj] at hB_inter
      exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) B hB_inter
    · have hxB' : x = B := eq_of_heq hxB
      rw [hxB'] at hdisj
      refine Or.inl ?_
      intro hAB
      have hA_inter :
          A ∈ B ∩ (@MySet.pair (MySet MyNat) (MySet MyNat) A B) := by
        rw [@MySet.mem_inter_obj MyNat B
            (@MySet.pair (MySet MyNat) (MySet MyNat) A B)
            (MySet MyNat) A]
        exact ⟨hAB, hA_mem_PAB⟩
      rw [hdisj] at hA_inter
      exact @MySet.not_mem_empty (MySet MyNat) (MySet MyNat) A hA_inter
  · rw [@MySet.mem_pair_obj
        (MySet MyNat) (MySet MyNat) A B ν x] at hxmem
    rcases hxmem with hxA | hxB
    · exact False.elim (hνne (type_eq_of_heq hxA))
    · exact False.elim (hνne (type_eq_of_heq hxB))

-- Exercise 3.2.3
example :
    ∃ (Ω : MySet MyNat), ∀ (x : MyNat), x ∈ Ω := by
  use MySet.Nat.set
  exact MySet.Nat.is_nat
