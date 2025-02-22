axiom MyNat : Type

-- Axiom 2.1
axiom MyNat.zero : MyNat
notation "𝟘" => MyNat.zero

-- Axiom 2.2
axiom MyNat.succ : MyNat → MyNat
postfix:max "++" => MyNat.succ

notation "𝟙" => 𝟘++
notation "𝟚" => 𝟙++

-- Axiom 2.3
axiom MyNat.succ_ne_zero :
  ∀ (n : MyNat), n++ ≠ 𝟘

-- Axiom 2.4
axiom MyNat.succ_inj :
  ∀ {n m : MyNat}, n++ = m++ → n = m

axiom MyNat.succ_inj' :
  ∀ {n m : MyNat}, n ≠ m → n++ ≠ m++

-- Axiom 2.5
axiom MyNat.induction {P : MyNat → Prop}
  (hbase : P 𝟘) (hind : ∀ {n : MyNat}, P n → P n++) :
  ∀ (n : MyNat), P n
