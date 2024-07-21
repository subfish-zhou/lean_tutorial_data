import Mathlib

namespace Logic

theorem Logic_1 {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


theorem Logic_2 (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP

theorem Logic_3 (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


theorem Logic_4 (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · sorry

theorem Logic_5 {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2

theorem Logic_6 {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


theorem Logic_7 (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

theorem Logic_8 {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  sorry

theorem Logic_9 {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  sorry

theorem Logic_10 (P : Prop) : ¬(P ∧ ¬ P) := by
  sorry

theorem Logic_11 {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  sorry

theorem Logic_12 {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  sorry

theorem Logic_13 {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  sorry

theorem Logic_14 (P : Prop) : (P ∧ P) ↔ P := by
  sorry

theorem Logic_15 (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  sorry

theorem Logic_16 (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  sorry

theorem Logic_17 {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  sorry

theorem Logic_18 {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  sorry

theorem Logic_19 (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  sorry

theorem Logic_20 (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  sorry

theorem Logic_21 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

theorem Logic_22 (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · sorry

theorem Logic_23 :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by
  sorry

theorem Logic_24 : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  sorry

theorem Logic_25 : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  sorry

theorem Logic_26 (P : Prop) : ¬ (¬ P) ↔ P := by
  sorry

theorem Logic_27 (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  sorry

theorem Logic_28 (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  sorry

theorem Logic_29 : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  sorry

theorem Logic_30 : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  sorry

theorem Logic_31 : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  sorry

theorem Logic_32 : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  sorry

theorem Logic_33 : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  sorry

theorem Logic_34 : ¬ Even 7 := by
  dsimp [Even]
  push_neg
  sorry

theorem Logic_35 {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  sorry

theorem Logic_36 : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

theorem Logic_37 {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    sorry
  sorry

end Logic
