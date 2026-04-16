import Lean4AnalysisTao.Util
import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals

-- Remarks 3.1.8
example
    (a : α)
    (S : MySet α)
    (h : ∀ (y : α), y ∈ S ↔ y = a) :
    S = ⦃a⦄ := by
  rw [MySet.ext]
  intro x
  rw [h x]
  rw [MySet.mem_singleton a]

example
    (a b : α) :
    (⦃a, b⦄ : MySet α) = ⦃b, a⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_pair a b]
  rw [MySet.mem_pair b a]
  exact Or.comm

example
    (a : α) :
    (⦃a, a⦄ : MySet α) = ⦃a⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_pair a a]
  rw [MySet.mem_singleton a]
  rw [or_self (x = a)]

-- Example 3.1.9
example :
    (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
  intro h
  have hmem :
      (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
    rw [MySet.mem_singleton ∅ ∅]
  have habs :
      ∅ ∈ ∅ :=
    Iff.mpr (Iff.mp (@MySet.ext γ γ ∅ ⦃∅⦄) h ∅) hmem
  exact @MySet.not_mem_empty γ γ ∅ habs

example :
    (∅ : γ) ≠ ⦃(⦃(∅ : γ)⦄ : γ)⦄ := by
  intro h
  have hmem :
      (⦃(∅ : γ)⦄ : γ) ∈ (⦃(⦃(∅ : γ)⦄ : γ)⦄ : γ) := by
    rw [MySet.mem_singleton ⦃∅⦄ ⦃∅⦄]
  have habs :
      ⦃∅⦄ ∈ ∅ :=
    Iff.mpr (Iff.mp (@MySet.ext γ γ ∅ ⦃⦃∅⦄⦄) h ⦃∅⦄) hmem
  exact @MySet.not_mem_empty γ γ ⦃∅⦄ habs

example :
    (∅ : γ) ≠ ⦃(∅ : γ), (⦃(∅ : γ)⦄ : γ)⦄ := by
  intro h
  have hmem :
      (⦃(∅ : γ)⦄ : γ) ∈ (⦃(∅ : γ), (⦃(∅ : γ)⦄ : γ)⦄ : γ) := by
    rw [MySet.mem_pair ∅ ⦃∅⦄]
    exact Or.inr rfl
  have habs :
      ⦃∅⦄ ∈ ∅ :=
    Iff.mpr (Iff.mp (@MySet.ext γ γ ∅ ⦃∅, ⦃∅⦄⦄) h ⦃∅⦄) hmem
  exact @MySet.not_mem_empty γ γ ⦃∅⦄ habs

example :
    (⦃(∅ : γ)⦄ : γ) ≠ ⦃(⦃(∅ : γ)⦄ : γ)⦄ := by
  intro h
  have hmem :
      (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
    rw [MySet.mem_singleton ∅ ∅]
  have h' : ∅ ∈ ⦃⦃∅⦄⦄ :=
    Iff.mp (Iff.mp (@MySet.ext γ γ ⦃∅⦄ ⦃⦃∅⦄⦄) h ∅) hmem
  rw [MySet.mem_singleton ⦃∅⦄ ∅] at h'
  have hne :
      (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
    intro heq
    have hmem2 :
        (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
      rw [MySet.mem_singleton ∅ ∅]
    have habs :
        ∅ ∈ ∅ :=
      Iff.mpr (Iff.mp (@MySet.ext γ γ ∅ ⦃∅⦄) heq ∅) hmem2
    exact @MySet.not_mem_empty γ γ ∅ habs
  exact hne h'

example :
    (⦃(∅ : γ)⦄ : γ) ≠ ⦃(∅ : γ), ⦃(∅ : γ)⦄⦄ := by
  intro h
  have hmem :
      (⦃(∅ : γ)⦄ : γ) ∈ (⦃(∅ : γ), ⦃(∅ : γ)⦄⦄ : γ) := by
    rw [MySet.mem_pair ∅ ⦃∅⦄]
    exact Or.inr rfl
  have h' : ⦃∅⦄ ∈ ⦃∅⦄ :=
    Iff.mpr (Iff.mp (@MySet.ext γ γ ⦃∅⦄ ⦃∅, ⦃∅⦄⦄) h ⦃∅⦄) hmem
  rw [MySet.mem_singleton ∅ ⦃∅⦄] at h'
  have hne :
      (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
    intro heq
    have hmem2 :
        (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
      rw [MySet.mem_singleton ∅ ∅]
    have habs :
        ∅ ∈ ∅ :=
      Iff.mpr (Iff.mp (@MySet.ext γ γ ∅ ⦃∅⦄) heq ∅) hmem2
    exact @MySet.not_mem_empty γ γ ∅ habs
  exact Ne.symm hne h'

example :
    (⦃(⦃(∅ : γ)⦄ : γ)⦄ : γ) ≠ ⦃(∅ : γ), (⦃(∅ : γ)⦄ : γ)⦄ := by
  intro h
  have hmem :
      (∅ : γ) ∈ (⦃(∅ : γ), ⦃(∅ : γ)⦄⦄ : γ) := by
    rw [MySet.mem_pair ∅ ⦃∅⦄]
    exact Or.inl rfl
  have h' : ∅ ∈ ⦃⦃∅⦄⦄ :=
    Iff.mpr (Iff.mp (@MySet.ext γ γ ⦃⦃∅⦄⦄ ⦃∅, ⦃∅⦄⦄) h ∅) hmem
  rw [MySet.mem_singleton ⦃∅⦄ ∅] at h'
  have hne :
      (∅ : γ) ≠ ⦃(∅ : γ)⦄ := by
    intro heq
    have hmem2 :
        (∅ : γ) ∈ (⦃(∅ : γ)⦄ : γ) := by
      rw [MySet.mem_singleton ∅ ∅]
    have habs :
        ∅ ∈ ∅ :=
      Iff.mpr (Iff.mp (@MySet.ext γ γ ∅ ⦃∅⦄) heq ∅) hmem2
    exact @MySet.not_mem_empty γ γ ∅ habs
  exact hne h'

-- Remark 3.1.11
example
    (A A' B : MySet α)
    (h : A = A') :
    A ∪ B = A' ∪ B := by
  have hiff
      (x : α) :
      x ∈ A ∪ B ↔ x ∈ A' ∪ B := by
    rw [MySet.mem_union A B]
    rw [MySet.mem_union A' B]
    rw [h]
  exact Iff.mpr (@MySet.ext α (MySet α) (A ∪ B) (A' ∪ B)) hiff

example
    (A B B' : MySet α)
    (h : B = B') :
    A ∪ B = A ∪ B' := by
  have hiff
      (x : α) :
      x ∈ A ∪ B ↔ x ∈ A ∪ B' := by
    rw [MySet.mem_union A B]
    rw [MySet.mem_union A B']
    rw [h]
  exact Iff.mpr (@MySet.ext α (MySet α) (A ∪ B) (A ∪ B')) hiff

-- Lemma 3.1.12
example
    (a b : α) :
    (⦃a, b⦄ : MySet α) = ⦃a⦄ ∪ ⦃b⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_pair a b]
  rw [MySet.mem_union ⦃a⦄ ⦃b⦄]
  rw [MySet.mem_singleton a]
  rw [MySet.mem_singleton b]

example
    (A B : MySet α) :
    A ∪ B = B ∪ A := by
  have hiff
      (x : α) :
      x ∈ A ∪ B ↔ x ∈ B ∪ A := by
    rw [MySet.mem_union A B]
    rw [MySet.mem_union B A]
    exact Or.comm
  exact Iff.mpr (@MySet.ext α (MySet α) (A ∪ B) (B ∪ A)) hiff

example
    (A : MySet α) :
    A ∪ A = A := by
  have hiff
      (x : α) :
      x ∈ A ∪ A ↔ x ∈ A := by
    rw [MySet.mem_union A A]
    rw [or_self (x ∈ A)]
  exact Iff.mpr (@MySet.ext α (MySet α) (A ∪ A) A) hiff

example
    (A : MySet α) :
    A ∪ ∅ = A := by
  have hiff
      (x : α) :
      x ∈ A ∪ ∅ ↔ x ∈ A := by
    rw [MySet.mem_union A ∅]
    constructor
    · intro h
      rcases h with (h | h)
      · exact h
      · exact False.elim (@MySet.not_mem_empty α (MySet α) x h)
    · intro h
      exact Or.inl h
  exact Iff.mpr (@MySet.ext α (MySet α) (A ∪ ∅) A) hiff

example
    (A : MySet α) :
    ∅ ∪ A = A := by
  have hcomm :
      ∅ ∪ A = A ∪ ∅ := by
    have hiff
        (x : α) :
        x ∈ ∅ ∪ A ↔ x ∈ A ∪ ∅ := by
      rw [MySet.mem_union ∅ A]
      rw [MySet.mem_union A ∅]
      exact Or.comm
    exact Iff.mpr (@MySet.ext α (MySet α) (∅ ∪ A) (A ∪ ∅)) hiff
  rw [hcomm]
  have hiff
      (x : α) :
      x ∈ A ∪ ∅ ↔ x ∈ A := by
    rw [MySet.mem_union A ∅]
    constructor
    · intro h
      rcases h with (h | h)
      · exact h
      · exact False.elim (@MySet.not_mem_empty α (MySet α) x h)
    · intro h
      exact Or.inl h
  exact Iff.mpr (@MySet.ext α (MySet α) (A ∪ ∅) A) hiff

-- Proposition 3.1.17
example
    (A B C : MySet α)
    (hAB : A ⊆ B)
    (hBC : B ⊆ C) :
    A ⊆ C := by
  rw [MySet.subset] at hAB
  rw [MySet.subset] at hBC
  rw [MySet.subset]
  intro x hxA
  have hxB :
      x ∈ B :=
    hAB x hxA
  exact hBC x hxB

example
    (A B : MySet α)
    (hAB : A ⊆ B)
    (hBA : B ⊆ A) :
    A = B := by
  rw [MySet.subset] at hAB
  rw [MySet.subset] at hBA
  rw [MySet.ext]
  intro x
  constructor
  · exact hAB x
  · exact hBA x

example
    (A B C : MySet α)
    (hAB : A ⊊ B)
    (hBC : B ⊊ C) :
    A ⊊ C := by
  constructor
  · exact @MySet.subset_trans α A B C (And.left hAB) (And.left hBC)
  · intro hAC
    have hCB :
        C ⊆ B := by
      rw [hAC] at hAB
      exact And.left hAB
    have hBC_eq :
        B = C :=
      @MySet.subset_antisymm α B C (And.left hBC) hCB
    exact And.right hBC hBC_eq

-- Axiom 3.6
example
    (A : MySet α)
    (P : α → Prop) :
    ⦃A | P⦄ ⊆ A := by
  rw [MySet.subset]
  intro x h
  rw [MySet.mem_spec A P x] at h
  exact And.left h

example
    (A A' : MySet α)
    (P : α → Prop)
    (h : A = A') :
    ⦃A | P⦄ = ⦃A' | P⦄ := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_spec A P x]
  rw [MySet.mem_spec A' P x]
  rw [h]

-- Example 3.1.21
namespace Example_3_1_21

-- TODO: port; needs a MyNat numeric decision procedure for `<` on literals.

end Example_3_1_21

-- Proposition 3.1.27
example :
    MySet.disjoint (∅ : MySet α) ∅ := by
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec ∅ (fun x => x ∈ ∅)]
  rw [and_self (x ∈ ∅)]

-- (a)
example
    (A : MySet α) :
    A ∩ ∅ = ∅ := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ ∅)]
  constructor
  · intro h
    exact False.elim (@MySet.not_mem_empty α (MySet α) x (And.right h))
  · intro h
    exact False.elim (@MySet.not_mem_empty α (MySet α) x h)

-- (b)
example
    (X A : MySet α)
    (hA : A ⊆ X) :
    A ∪ X = X := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A X]
  constructor
  · intro h
    rcases h with (h | h)
    · rw [MySet.subset] at hA
      exact hA x h
    · exact h
  · intro h
    exact Or.inr h

example
    (X A : MySet α)
    (hA : A ⊆ X) :
    A ∩ X = A := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ X)]
  constructor
  · intro h
    exact And.left h
  · intro h
    constructor
    · exact h
    · rw [MySet.subset] at hA
      exact hA x h

-- (c)
example
    (A : MySet α) :
    A ∩ A = A := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ A)]
  rw [and_self (x ∈ A)]

-- (d)
example
    (A B : MySet α) :
    A ∩ B = B ∩ A := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec B (fun x => x ∈ A)]
  exact and_comm

-- (e)
example
    (A B C : MySet α) :
    (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec (A ∩ B) (fun x => x ∈ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B ∩ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec B (fun x => x ∈ C)]
  exact and_assoc

-- (f)
example
    (A B C : MySet α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B ∪ C)]
  rw [MySet.mem_union B C]
  rw [MySet.mem_union (A ∩ B) (A ∩ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ C)]
  exact and_or_left

example
    (A B C : MySet α) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A (B ∩ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec B (fun x => x ∈ C)]
  rw [MySet.inter]
  rw [MySet.mem_spec (A ∪ B) (fun x => x ∈ A ∪ C)]
  rw [MySet.mem_union A B]
  rw [MySet.mem_union A C]
  exact or_and_left

-- (g)
example
    (X A : MySet α)
    (hA : A ⊆ X) :
    A ∪ (X \ A) = X := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A (X \ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  constructor
  · intro h
    rcases h with (h | h)
    · rw [MySet.subset] at hA
      exact hA x h
    · exact And.left h
  · intro h
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr ⟨h, hxA⟩

example
    (X A : MySet α) :
    A ∩ (X \ A) = ∅ := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ X \ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  constructor
  · intro h
    exact False.elim (And.right (And.right h) (And.left h))
  · intro h
    exact False.elim (@MySet.not_mem_empty α (MySet α) x h)

example
    (X A B : MySet α) :
    X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  rw [MySet.ext]
  intro x
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A ∪ B)]
  rw [MySet.mem_union A B]
  rw [MySet.inter]
  rw [MySet.mem_spec (X \ A) (fun x => x ∈ X \ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ B)]
  constructor
  · intro h
    constructor
    · constructor
      · exact And.left h
      · rw [not_or] at h
        exact And.left (And.right h)
    · constructor
      · exact And.left h
      · rw [not_or] at h
        exact And.right (And.right h)
  · intro h
    constructor
    · exact And.left (And.left h)
    · rw [not_or]
      constructor
      · exact And.right (And.left h)
      · exact And.right (And.right h)

example
    (X A B : MySet α) :
    X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  rw [MySet.ext]
  intro x
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A ∩ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.mem_union (X \ A) (X \ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ B)]
  constructor
  · intro h
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B
      · rcases h with ⟨hxX, hxAB⟩
        rw [not_and] at hxAB
        exact Or.inr ⟨hxX, hxAB hxA⟩
      · exact Or.inr ⟨And.left h, hxB⟩
    · exact Or.inl ⟨And.left h, hxA⟩
  · intro h
    rcases h with (h | h)
    · rcases h with ⟨hxX, hxA⟩
      constructor
      · exact hxX
      · rw [not_and_or]
        exact Or.inl hxA
    · rcases h with ⟨hxX, hxB⟩
      constructor
      · exact hxX
      · rw [not_and_or]
        exact Or.inr hxB

-- Example 3.1.30
namespace Example_3_1_30

-- TODO: port; needs numeric rewriting for `3 + 1 = 4` etc. on MyNat.

end Example_3_1_30

-- Example 3.1.31
namespace Example_3_1_31

-- TODO: port.

end Example_3_1_31

section Exercises

-- Exercise 3.1.1
example
    (a b c d : α)
    (h : (⦃a, b⦄ : MySet MyNat) = ⦃c, d⦄) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [MySet.ext] at h
  by_cases hac : a = c
  · have hbd : b = d := by
      have hmemb :
          b ∈ (⦃a, b⦄ : MySet MyNat) := by
        rw [MySet.mem_pair a b]
        exact Or.inr rfl
      have hbcd :
          b ∈ (⦃c, d⦄ : MySet MyNat) :=
        Iff.mp (h b) hmemb
      rw [MySet.mem_pair c d] at hbcd
      rcases hbcd with (hbc | hbd)
      · rw [← hbc] at hac
        have hmemd :
            d ∈ (⦃c, d⦄ : MySet MyNat) := by
          rw [MySet.mem_pair c d]
          exact Or.inr rfl
        have hdab :
            d ∈ (⦃a, b⦄ : MySet MyNat) :=
          Iff.mpr (h d) hmemd
        rw [MySet.mem_pair a b] at hdab
        rcases hdab with (hac' | hbd)
        · rw [hac']
          exact Eq.symm hac
        · exact Eq.symm hbd
      · exact hbd
    exact Or.inl ⟨hac, hbd⟩
  · have haeqd : a = d := by
      have hmema :
          a ∈ (⦃a, b⦄ : MySet MyNat) := by
        rw [MySet.mem_pair a b]
        exact Or.inl rfl
      have hacd :
          a ∈ (⦃c, d⦄ : MySet MyNat) :=
        Iff.mp (h a) hmema
      rw [MySet.mem_pair c d] at hacd
      rcases hacd with (hac' | had)
      · exact False.elim (hac hac')
      · exact had
    have hbeqc :
        b = c := by
      have hmemc :
          c ∈ (⦃c, d⦄ : MySet MyNat) := by
        rw [MySet.mem_pair c d]
        exact Or.inl rfl
      have hcab :
          c ∈ (⦃a, b⦄ : MySet MyNat) :=
        Iff.mpr (h c) hmemc
      rw [MySet.mem_pair a b] at hcab
      rcases hcab with (hac' | hbc)
      · exact False.elim (hac (Eq.symm hac'))
      · exact Eq.symm hbc
    exact Or.inr ⟨haeqd, hbeqc⟩

-- Exercise 3.1.5
example
    (A B : MySet α) :
    ((A ⊆ B) ↔ (A ∪ B = B))
  ∧ ((A ⊆ B) ↔ (A ∩ B = A)) := by
  constructor
  · constructor
    · intro h
      exact @MySet.union_superset α B A h
    · intro h
      rw [MySet.subset]
      intro x hxA
      rw [MySet.ext] at h
      have hmem :
          x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inl hxA
      exact Iff.mp (h x) hmem
  · constructor
    · intro h
      exact @MySet.inter_superset α B A h
    · intro h
      rw [MySet.subset]
      intro x hxA
      rw [MySet.ext] at h
      have hmem :
          x ∈ A ∩ B :=
        Iff.mpr (h x) hxA
      rw [MySet.inter] at hmem
      rw [MySet.mem_spec A (fun x => x ∈ B)] at hmem
      exact And.right hmem

-- Exercise 3.1.7
example
    (A B : MySet α) :
    A ∩ B ⊆ A := by
  rw [MySet.subset]
  intro x hxAB
  rw [MySet.inter] at hxAB
  rw [MySet.mem_spec A (fun x => x ∈ B)] at hxAB
  exact And.left hxAB

example
    (A B : MySet α) :
    A ∩ B ⊆ B := by
  rw [MySet.subset]
  intro x hxAB
  rw [MySet.inter] at hxAB
  rw [MySet.mem_spec A (fun x => x ∈ B)] at hxAB
  exact And.right hxAB

example
    (A B C : MySet α) :
    C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B := by
  constructor
  · intro h
    rw [MySet.subset]
    intro x hxC
    rw [MySet.inter]
    rw [MySet.mem_spec A (fun x => x ∈ B)]
    constructor
    · rw [MySet.subset] at h
      exact And.left h x hxC
    · rw [MySet.subset] at h
      exact And.right h x hxC
  · intro h
    constructor
    · rw [MySet.subset]
      intro x hxC
      rw [MySet.subset] at h
      have hmem :
          x ∈ A ∩ B :=
        h x hxC
      rw [MySet.inter] at hmem
      rw [MySet.mem_spec A (fun x => x ∈ B)] at hmem
      exact And.left hmem
    · rw [MySet.subset]
      intro x hxC
      rw [MySet.subset] at h
      have hmem :
          x ∈ A ∩ B :=
        h x hxC
      rw [MySet.inter] at hmem
      rw [MySet.mem_spec A (fun x => x ∈ B)] at hmem
      exact And.right hmem

example
    (A B : MySet α) :
    A ⊆ A ∪ B := by
  rw [MySet.subset]
  intro x hxA
  rw [MySet.mem_union A B]
  exact Or.inl hxA

example
    (A B : MySet α) :
    B ⊆ A ∪ B := by
  rw [MySet.subset]
  intro x hxB
  rw [MySet.mem_union A B]
  exact Or.inr hxB

example
    (A B C : MySet α) :
    A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  constructor
  · intro h
    rw [MySet.subset]
    intro x hxAB
    rw [MySet.mem_union A B] at hxAB
    rcases hxAB with (hxA | hxB)
    · rw [MySet.subset] at h
      exact And.left h x hxA
    · rw [MySet.subset] at h
      exact And.right h x hxB
  · intro h
    constructor
    · rw [MySet.subset]
      intro x hxA
      rw [MySet.subset] at h
      have hmem :
          x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inl hxA
      exact h x hmem
    · rw [MySet.subset]
      intro x hxB
      rw [MySet.subset] at h
      have hmem :
          x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inr hxB
      exact h x hmem

-- Exercise 3.1.8
example
    (A B : MySet α) :
    A ∩ (A ∪ B) = A := by
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ A ∪ B)]
  rw [MySet.mem_union A B]
  constructor
  · intro h
    exact And.left h
  · intro h
    constructor
    · exact h
    · exact Or.inl h

example
    (A B : MySet α) :
    A ∪ (A ∩ B) = A := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union A (A ∩ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  constructor
  · intro h
    rcases h with (h | h)
    · exact h
    · exact And.left h
  · intro h
    exact Or.inl h

-- Exercise 3.1.9
example
    (A B X : MySet α)
    (hu : A ∪ B = X)
    (hi : A ∩ B = ∅) :
    A = X \ B := by
  rw [MySet.ext]
  intro x
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ B)]
  rw [MySet.ext] at hu
  constructor
  · intro h
    constructor
    · have hmem : x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inl h
      exact Iff.mp (hu x) hmem
    · intro hxB
      have hmem :
          x ∈ A ∩ B := by
        rw [MySet.inter]
        rw [MySet.mem_spec A (fun x => x ∈ B)]
        exact And.intro h hxB
      rw [hi] at hmem
      exact @MySet.not_mem_empty α (MySet α) x hmem
  · intro h
    have hmem :
        x ∈ A ∪ B :=
      Iff.mpr (hu x) (And.left h)
    rw [MySet.mem_union A B] at hmem
    rcases hmem with (hxA | hxB)
    · exact hxA
    · exact False.elim (And.right h hxB)

example
    (A B X : MySet α)
    (hu : A ∪ B = X)
    (hi : A ∩ B = ∅) :
    B = X \ A := by
  rw [MySet.ext]
  intro x
  rw [MySet.diff]
  rw [MySet.mem_spec X (fun x => x ∉ A)]
  rw [MySet.ext] at hu
  constructor
  · intro h
    constructor
    · have hmem : x ∈ A ∪ B := by
        rw [MySet.mem_union A B]
        exact Or.inr h
      exact Iff.mp (hu x) hmem
    · intro hxA
      have hmem :
          x ∈ A ∩ B := by
        rw [MySet.inter]
        rw [MySet.mem_spec A (fun x => x ∈ B)]
        exact And.intro hxA h
      rw [hi] at hmem
      exact @MySet.not_mem_empty α (MySet α) x hmem
  · intro h
    have hmem :
        x ∈ A ∪ B :=
      Iff.mpr (hu x) (And.left h)
    rw [MySet.mem_union A B] at hmem
    rcases hmem with (hxA | hxB)
    · exact False.elim (And.right h hxA)
    · exact hxB

-- Exercise 3.1.10
example
    (A B : MySet α) :
    MySet.disjoint (A \ B) (A ∩ B) := by
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec (A \ B) (fun x => x ∈ A ∩ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec A (fun x => x ∉ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  constructor
  · intro h
    exact False.elim (And.right (And.left h) (And.right (And.right h)))
  · intro h
    exact False.elim (@MySet.not_mem_empty α (MySet α) x h)

example
    (A B : MySet α) :
    MySet.disjoint (A \ B) (B \ A) := by
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec (A \ B) (fun x => x ∈ B \ A)]
  rw [MySet.diff]
  rw [MySet.mem_spec A (fun x => x ∉ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec B (fun x => x ∉ A)]
  constructor
  · intro h
    exact False.elim (And.right (And.right h) (And.left (And.left h)))
  · intro h
    exact False.elim (@MySet.not_mem_empty α (MySet α) x h)

example
    (A B : MySet α) :
    MySet.disjoint (A ∩ B) (B \ A) := by
  rw [MySet.disjoint]
  rw [MySet.ext]
  intro x
  rw [MySet.inter]
  rw [MySet.mem_spec (A ∩ B) (fun x => x ∈ B \ A)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec B (fun x => x ∉ A)]
  constructor
  · intro h
    exact False.elim (And.right (And.right h) (And.left (And.left h)))
  · intro h
    exact False.elim (@MySet.not_mem_empty α (MySet α) x h)

example
    (A B : MySet α) :
    (A \ B) ∪ (A ∩ B) ∪ (B \ A) = A ∪ B := by
  rw [MySet.ext]
  intro x
  rw [MySet.mem_union ((A \ B) ∪ (A ∩ B)) (B \ A)]
  rw [MySet.mem_union (A \ B) (A ∩ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec A (fun x => x ∉ B)]
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  rw [MySet.diff]
  rw [MySet.mem_spec B (fun x => x ∉ A)]
  rw [MySet.mem_union A B]
  constructor
  · intro h
    rcases h with (h | h)
    · rcases h with (h | h)
      · exact Or.inl (And.left h)
      · exact Or.inr (And.right h)
    · exact Or.inr (And.left h)
  · intro h
    rcases h with (h | h)
    · by_cases hxB : x ∈ B
      · exact Or.inl (Or.inr ⟨h, hxB⟩)
      · exact Or.inl (Or.inl ⟨h, hxB⟩)
    · by_cases hxA : x ∈ A
      · exact Or.inl (Or.inr ⟨hxA, h⟩)
      · exact Or.inr ⟨h, hxA⟩

-- Exercise 3.1.11
example
    {α : Type}
    (hrep : ∀ (A : MySet α) {β : Type} (P : α → β → Prop),
    (∀ (x : α), x ∈ A →
      (∃ (y : β), P x y ∧ (∀ (z : β), P x z → y = z))) →
    (∃ (S : MySet β),
      ∀ (y : β), y ∈ S ↔ ∃ (x : α), x ∈ A ∧ P x y))
    (A : MySet α)
    (P : α → Prop) :
    ∃ (S : MySet α),
      ∀ (x : α), x ∈ S ↔ x ∈ A ∧ P x := by
  by_cases h : ∃ (x : α), x ∈ A ∧ P x
  · rcases h with ⟨x', hx'A, hPx'⟩
    let P' : α → α → Prop :=
      fun x y => (P x ∧ y = x) ∨ (¬ P x ∧ y = x')
    have hP'spec
        (x : α)
        (hxA : x ∈ A) :
        ∃ (y : α), P' x y ∧ (∀ (z : α), P' x z → y = z) := by
      by_cases hPx : P x
      · use x
        constructor
        · exact Or.inl ⟨hPx, rfl⟩
        · intro z hP'zx
          rcases hP'zx with (hP'zx | hP'zx)
          · exact Eq.symm (And.right hP'zx)
          · exact False.elim (And.left hP'zx hPx)
      · use x'
        constructor
        · exact Or.inr ⟨hPx, rfl⟩
        · intro z hP'zx
          rcases hP'zx with (hP'zx | hP'zx)
          · exact False.elim (hPx (And.left hP'zx))
          · exact Eq.symm (And.right hP'zx)
    rcases hrep A P' hP'spec with ⟨S, hS⟩
    use S
    intro x
    constructor
    · intro hxS
      rcases Iff.mp (hS x) hxS with ⟨y, hyA, hP'yx⟩
      rcases hP'yx with (hP'yx | hP'yx)
      · rw [And.right hP'yx]
        constructor
        · exact hyA
        · exact And.left hP'yx
      · rw [And.right hP'yx]
        constructor
        · exact hx'A
        · exact hPx'
    · intro hxA
      rcases hxA with ⟨hxA, hPx⟩
      exact Iff.mpr (hS x) ⟨x, hxA, Or.inl ⟨hPx, rfl⟩⟩
  · have hh
        (x : α)
        (hx : x ∈ A)
        (hPx : P x) :
        False :=
      h ⟨x, hx, hPx⟩
    use ∅
    intro x
    constructor
    · intro hxS
      exact False.elim (@MySet.not_mem_empty α (MySet α) x hxS)
    · intro h'
      rcases h' with ⟨hxA, hPx⟩
      have hnotP :
          ¬ P x :=
        hh x hxA
      exact False.elim (hnotP hPx)

-- Exercise 3.1.12
-- (a)
example
    (A B A' B' : MySet α)
    (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    A' ∪ B' ⊆ A ∪ B := by
  rw [MySet.subset]
  intro x hxAB'
  rw [MySet.mem_union A' B'] at hxAB'
  rcases hxAB' with (hxA' | hxB')
  · rw [MySet.subset] at hA
    rw [MySet.mem_union A B]
    exact Or.inl (hA x hxA')
  · rw [MySet.subset] at hB
    rw [MySet.mem_union A B]
    exact Or.inr (hB x hxB')

example
    (A B A' B' : MySet α)
    (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    A' ∩ B' ⊆ A ∩ B := by
  rw [MySet.subset]
  intro x hxAB'
  rw [MySet.inter] at hxAB'
  rw [MySet.mem_spec A' (fun x => x ∈ B')] at hxAB'
  rw [MySet.inter]
  rw [MySet.mem_spec A (fun x => x ∈ B)]
  constructor
  · rw [MySet.subset] at hA
    exact hA x (And.left hxAB')
  · rw [MySet.subset] at hB
    exact hB x (And.right hxAB')

-- (b)
example :
    ∃ (A B A' B' : MySet MyNat),
    A' ⊆ A ∧ B' ⊆ B ∧ ¬ (A' \ B' ⊆ A \ B) := by
  use ⦃(1 : MyNat), (2 : MyNat)⦄, ⦃(1 : MyNat)⦄, ⦃(1 : MyNat)⦄, ∅
  constructor
  · rw [MySet.subset]
    intro x hx
    rw [MySet.mem_pair (1 : MyNat) (2 : MyNat)]
    rw [MySet.mem_singleton (1 : MyNat) x] at hx
    exact Or.inl hx
  · constructor
    · rw [MySet.subset]
      intro x hx
      exact False.elim (@MySet.not_mem_empty MyNat (MySet MyNat) x hx)
    · intro h
      rw [MySet.subset] at h
      have h1 :
          (1 : MyNat) ∈ (⦃(1 : MyNat)⦄ : MySet MyNat) \ ∅ := by
        rw [MySet.diff]
        rw [MySet.mem_spec ⦃(1 : MyNat)⦄ (fun x => x ∉ ∅)]
        constructor
        · rw [MySet.mem_singleton (1 : MyNat) 1]
        · intro h'
          exact False.elim (@MySet.not_mem_empty MyNat (MySet MyNat) 1 h')
      have h2 : (1 : MyNat)
          ∉ (⦃(1 : MyNat), (2 : MyNat)⦄ : MySet MyNat) \ ⦃(1 : MyNat)⦄ := by
        rw [MySet.diff]
        rw [MySet.mem_spec ⦃(1 : MyNat), (2 : MyNat)⦄ (fun x => x ∉ ⦃(1 : MyNat)⦄)]
        intro hmem
        have h1mem :
            (1 : MyNat) ∈ (⦃(1 : MyNat)⦄ : MySet MyNat) := by
          rw [MySet.mem_singleton (1 : MyNat) 1]
        exact And.right hmem h1mem
      exact h2 (h 1 h1)

-- Exercise 3.1.13
example
    (A : MySet α)
    (hA : MySet.nonempty A) :
    ¬ (∃ (B : MySet α), MySet.nonempty B ∧ B ⊊ A) ↔ (∃ (x : α), A = ⦃x⦄) := by
  constructor
  · intro h
    have hh
        (B : MySet α)
        (hB : MySet.nonempty B)
        (hss : B ⊊ A) :
        False :=
      h (Exists.intro B (And.intro hB hss))
    rcases @MySet.single_choice α A hA with ⟨x, hxA⟩
    use x
    have hnonempty :
        (MySet.nonempty (⦃x⦄ : MySet α)) := by
      rw [MySet.nonempty]
      intro h'
      rw [MySet.ext] at h'
      have hmem :
          x ∈ (⦃x⦄ : MySet α) := by
        rw [MySet.mem_singleton x x]
      have habs :
          x ∈ ∅ :=
        Iff.mp (h' x) hmem
      exact @MySet.not_mem_empty α (MySet α) x habs
    have hss :
        ⦃x⦄ ⊆ A := by
      rw [MySet.subset]
      intro y hy
      rw [MySet.mem_singleton x y] at hy
      rw [hy]
      exact hxA
    by_contra hne
    have hne' : ⦃x⦄ ≠ A :=
      fun heq => hne (Eq.symm heq)
    exact hh ⦃x⦄ hnonempty ⟨hss, hne'⟩
  · intro h
    rcases h with ⟨x, hAx⟩
    intro ⟨B, hB, hss⟩
    rcases @MySet.single_choice α B hB with ⟨z, hzB⟩
    have hzA :
        z ∈ A :=
      And.left hss z hzB
    rw [hAx] at hzA
    rw [MySet.mem_singleton x z] at hzA
    have hxB :
        x ∈ B := by
      rw [← hzA]
      exact hzB
    have hAsubB :
        A ⊆ B := by
      rw [MySet.subset]
      intro y hyA
      rw [hAx] at hyA
      rw [MySet.mem_singleton x y] at hyA
      rw [hyA]
      exact hxB
    have hBeqA :
        B = A :=
      @MySet.subset_antisymm α B A (And.left hss) hAsubB
    exact And.right hss hBeqA

end Exercises
