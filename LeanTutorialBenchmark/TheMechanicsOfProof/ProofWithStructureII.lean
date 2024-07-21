import Mathlib

namespace ProofWithStructureII

theorem ProofWithStructureII_1 {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by norm_num


theorem ProofWithStructureII_2 {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by norm_num
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.pos_of_dvd_of_pos h1 h2


theorem ProofWithStructureII_3 {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  sorry

theorem ProofWithStructureII_4 {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · sorry

theorem ProofWithStructureII_5 : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by sorry
    _ = x ^ 2 - 2 * x := by ring

theorem ProofWithStructureII_6 : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  sorry

theorem ProofWithStructureII_7 (n : ℤ) (hn : n ≥ 5) : n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  sorry

theorem ProofWithStructureII_8 : Prime 2 := by
  sorry

theorem ProofWithStructureII_9 : ¬ Prime 6 := by
  sorry

theorem ProofWithStructureII_10 {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  sorry

theorem ProofWithStructureII_11 {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  sorry

theorem ProofWithStructureII_12 : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry

theorem ProofWithStructureII_13 : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  sorry

theorem ProofWithStructureII_14 (x : ℝ) (h : x ≥ 8) : x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  sorry

theorem ProofWithStructureII_15 : ¬(Prime 45) := by
  sorry

theorem ProofWithStructureII_16 {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by norm_num
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by norm_num

theorem ProofWithStructureII_17 {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring

theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  sorry

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  sorry

theorem ProofWithStructureII_18 {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  sorry

theorem ProofWithStructureII_19 {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  sorry

theorem ProofWithStructureII_20 {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  sorry

theorem ProofWithStructureII_21 {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  sorry

theorem ProofWithStructureII_22 {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  sorry

theorem ProofWithStructureII_23 (n : ℤ) : Even n ∨ Odd n := by
  sorry

theorem ProofWithStructureII_24 {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  sorry

theorem ProofWithStructureII_25 {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  sorry

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  sorry

theorem ProofWithStructureII_26 {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  sorry

theorem ProofWithStructureII_27 {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  sorry

theorem ProofWithStructureII_28 : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · norm_num
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by norm_num

theorem ProofWithStructureII_29 : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  sorry

theorem ProofWithStructureII_30 {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


theorem ProofWithStructureII_31 : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  sorry

theorem ProofWithStructureII_32 : ∃! x : ℚ, 4 * x - 3 = 9 := by
  sorry

theorem ProofWithStructureII_33 : ∃! n : ℕ, ∀ a, n ≤ a := by
  sorry

theorem ProofWithStructureII_34 : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  sorry

theorem ProofWithStructureII_35 {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


theorem ProofWithStructureII_36 {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by linarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by norm_num
  contradiction


theorem ProofWithStructureII_37 {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by linarith [h]
    _ < 3 := h2
  norm_num at H -- this is a contradiction!


theorem ProofWithStructureII_38 (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  sorry

theorem ProofWithStructureII_39 {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  sorry

theorem ProofWithStructureII_40 : Prime 5 := by
  sorry

theorem ProofWithStructureII_41 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  sorry

theorem ProofWithStructureII_42 {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  sorry

theorem ProofWithStructureII_43 (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  sorry

theorem ProofWithStructureII_44 : Prime 7 := by
  sorry

theorem ProofWithStructureII_45 {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by linarith [h1]
  rw [mul_eq_zero] at h3
  sorry

theorem ProofWithStructureII_46 (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  sorry

theorem ProofWithStructureII_47 : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  norm_num at this

theorem ProofWithStructureII_48 : ¬ 3 ∣ 13 := by
  sorry

theorem ProofWithStructureII_49 {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  sorry


theorem ProofWithStructureII_50 : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  sorry

theorem ProofWithStructureII_51 (n : ℤ) : Even n ↔ ¬ Odd n := by
  sorry


theorem ProofWithStructureII_52 (n : ℤ) : Odd n ↔ ¬ Even n := by
  sorry

theorem ProofWithStructureII_53 (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  sorry

theorem ProofWithStructureII_54 {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  sorry


theorem ProofWithStructureII_55 (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  sorry

theorem ProofWithStructureII_56 {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  sorry


theorem ProofWithStructureII_57 : Prime 79 := by
  sorry

theorem ProofWithStructureII_58 : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  sorry

theorem ProofWithStructureII_59 : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  sorry

theorem ProofWithStructureII_60 : ¬ Even 7 := by
  sorry

theorem ProofWithStructureII_61 {n : ℤ} (hn : n + 3 = 7) : ¬ (Even n ∧ n ^ 2 = 10) := by
  sorry

theorem ProofWithStructureII_62 {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  sorry

theorem ProofWithStructureII_63 : ¬ (∃ N : ℕ, ∀ k > N, Even k) := by
  sorry

theorem ProofWithStructureII_64 (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

theorem ProofWithStructureII_65 : ¬ Prime 1 := by
  sorry

theorem ProofWithStructureII_66 : Prime 97 := by
  sorry

end ProofWithStructureII
