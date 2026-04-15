import Lean4AnalysisTao.C02_NaturalNumbers.S02_Addition

/-!
Auxiliary `MyNat` lemmas used by downstream chapters (e.g. C03).

These are not in Tao's text; they exist to replace Mathlib-`Nat` lemmas
(`Nat.ne_of_lt`, `Nat.not_lt_of_ge`, etc.) with `MyNat` analogues after
stripping chapter 3 of its dependency on `ℕ`.
-/

namespace MyNat

theorem ne_of_lt {a b : MyNat} (h : a < b) : a ≠ b := by
  dsimp only [MyNat.lt] at h
  dsimp only [MyNat.gt] at h
  exact (Ne.symm h.right)

theorem not_lt_of_ge {a b : MyNat} (h : a ≥ b) : ¬(a < b) := by
  intro hlt
  dsimp only [MyNat.lt] at hlt
  dsimp only [MyNat.gt] at hlt
  have heq : a = b := @MyNat.ge_antisymm a b h hlt.left
  exact hlt.right heq.symm

theorem lt_irrefl (a : MyNat) : ¬(a < a) :=
  @not_lt_of_ge a a (@MyNat.ge_refl a)

theorem lt_of_lt_of_le {a b c : MyNat} (hab : a < b) (hbc : b ≤ c) : a < c := by
  dsimp only [MyNat.lt] at hab
  dsimp only [MyNat.gt] at hab
  dsimp only [MyNat.lt]
  dsimp only [MyNat.gt]
  refine ⟨@MyNat.ge_trans c b a hbc hab.left, ?_⟩
  intro hca
  rw [hca] at hbc
  have heq : b = a := @MyNat.ge_antisymm b a hab.left hbc
  exact hab.right heq

theorem zero_lt_succ (n : MyNat) : 𝟘 < n++ := by
  dsimp only [MyNat.lt, MyNat.gt]
  constructor
  · refine ⟨n++, ?_⟩
    rw [@MyNat.zero_add (n++)]
  · exact (@MyNat.succ_ne_zero n)

theorem one_le_succ (n : MyNat) : 𝟙 ≤ n++ := by
  rcases (@MyNat.lt_iff_succ_le 𝟘 (n++)).mp (@zero_lt_succ n) with h
  exact h

end MyNat
