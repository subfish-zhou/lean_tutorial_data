import Mathlib

namespace Sets

open Set

notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

theorem Sets_1 : 1 ∈ {n : ℤ | n ≤ 3} := by
  dsimp
  norm_num

theorem Sets_2 : 10 ∉ {n : ℕ | Odd n} := by
  dsimp
  rw [← Nat.even_iff_not_odd]
  use 5


theorem Sets_3 : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  dsimp [Set.subset_def] -- optional
  intro a ha
  obtain ⟨k, hk⟩ := ha
  use 2 * k
  calc a = 4 * k := hk
    _ = 2 * (2 * k) := by ring


theorem Sets_4 : {x : ℝ | 0 ≤ x ^ 2} ⊈ {t : ℝ | 0 ≤ t} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  constructor
  · norm_num
  · norm_num


theorem Sets_5 : {x : ℤ | Odd x} = {a : ℤ | ∃ k, a = 2 * k - 1} := by
  ext x
  dsimp
  constructor
  · intro h
    obtain ⟨l, hl⟩ := h
    use l + 1
    calc x = 2 * l + 1 := by rw [hl]
      _ = 2 * (l + 1) - 1 := by ring
  · intro h
    obtain ⟨k, hk⟩ := h
    use k - 1
    calc x = 2 * k - 1 := by rw [hk]
      _ = 2 * (k - 1) + 1 := by ring


theorem Sets_6 : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  sorry


theorem Sets_7 : {k : ℤ | 8 ∣ 5 * k} = {l : ℤ | 8 ∣ l} := by
  ext n
  dsimp
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


theorem Sets_8 : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      linarith [hx]
    · right
      sorry
  · intro h
    obtain h | h := h
    · calc x ^ 2 - x - 2 = (-1) ^ 2 - (-1) - 2 := by rw [h]
        _ = 0 := by norm_num
    · calc x ^ 2 - x - 2 = 2 ^ 2 - 2 - 2 := by rw [h]
        _ = 0 := by norm_num


theorem Sets_9 : {1, 3, 6} ⊆ {t : ℚ | t < 10} := by
  dsimp [Set.subset_def]
  intro t ht
  obtain h1 | h3 | h6 := ht
  · linarith [h1]
  · linarith [h3]
  · sorry

/-! # Exercises -/


theorem Sets_10 : 4 ∈ {a : ℚ | a < 3} := by
  sorry

theorem Sets_11 : 4 ∉ {a : ℚ | a < 3} := by
  sorry

theorem Sets_12 : 6 ∈ {n : ℕ | n ∣ 42} := by
  sorry

theorem Sets_13 : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry


theorem Sets_14 : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

theorem Sets_15 : 8 ∉ {k : ℤ | 5 ∣ k} := by
  sorry

theorem Sets_16 : 11 ∈ {n : ℕ | Odd n} := by
  sorry

theorem Sets_17 : 11 ∉ {n : ℕ | Odd n} := by
  sorry


theorem Sets_18 : -3 ∈ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  sorry

theorem Sets_19 : -3 ∉ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  sorry


theorem Sets_20 : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  sorry

theorem Sets_21 : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry


theorem Sets_22 : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

theorem Sets_23 : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  sorry

theorem Sets_24 : {r : ℤ | 3 ∣ r} ⊆ {s : ℤ | 0 ≤ s} := by
  sorry

theorem Sets_25 : {r : ℤ | 3 ∣ r} ⊈ {s : ℤ | 0 ≤ s} := by
  sorry

theorem Sets_26 : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  sorry

theorem Sets_27 : {m : ℤ | m ≥ 10} ⊈ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  sorry

theorem Sets_28 : {n : ℤ | Even n} = {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  sorry

theorem Sets_29 : {n : ℤ | Even n} ≠ {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  sorry

theorem Sets_30 : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} = {4} := by
  sorry

theorem Sets_31 : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4} := by
  sorry

theorem Sets_32 : {k : ℤ | 8 ∣ 6 * k} = {l : ℤ | 8 ∣ l} := by
  sorry

theorem Sets_33 : {k : ℤ | 8 ∣ 6 * k} ≠ {l : ℤ | 8 ∣ l} := by
  sorry

theorem Sets_34 : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  sorry

theorem Sets_35 : {k : ℤ | 7 ∣ 9 * k} ≠ {l : ℤ | 7 ∣ l} := by
  sorry

theorem Sets_36 : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  sorry

theorem Sets_37 (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  sorry

theorem Sets_38 : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    norm_num at this
  · sorry


theorem Sets_39 : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  sorry

theorem Sets_40 : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [Int.odd_iff_not_even]
  sorry

theorem Sets_41 (U : Set ℤ) : ∅ ⊆ U := by
  sorry

theorem Sets_42 : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  sorry

theorem Sets_43 : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  sorry

theorem Sets_44 (x : ℤ) : x ∈ univ := by
  sorry

theorem Sets_45 (U : Set ℤ) : U ⊆ univ := by
  sorry

theorem Sets_46 : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  sorry

theorem Sets_47 : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  sorry

theorem Sets_48 : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  sorry

theorem Sets_49 :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  sorry

end Sets
