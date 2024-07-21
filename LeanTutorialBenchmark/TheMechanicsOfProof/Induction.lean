import Mathlib

namespace Induction

theorem Induction_1 (n : ℕ) : 2 ^ n ≥ n + 1 := by
  sorry

theorem Induction_2 (n : ℕ) : Even n ∨ Odd n := by
  sorry

theorem Induction_3 {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  sorry

theorem Induction_4 (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  sorry

theorem Induction_5 {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  sorry

theorem Induction_6 (n : ℕ) (hn : n ≥ 4) :  2 ^ n ≥ n ^ 2 := by
  sorry

theorem Induction_7 (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  sorry

theorem Induction_8 {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

theorem Induction_9 (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry

theorem Induction_10 (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  sorry

theorem Induction_11 (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  sorry

theorem Induction_12 (n : ℕ) (hn : n ≥ 5) : (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  sorry

theorem Induction_13 (n : ℕ) (hn : n ≥ 5) : 2 ^ n ≥ n ^ 2 + 4 := by
  sorry

theorem Induction_14 (n : ℕ) (hn : n ≥ 10) : 2 ^ n ≥ n ^ 3 := by
  sorry

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  sorry

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  sorry

end Induction
