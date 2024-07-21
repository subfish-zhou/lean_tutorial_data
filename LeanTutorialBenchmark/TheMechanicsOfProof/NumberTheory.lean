import Mathlib

namespace NumberTheory

theorem NumberTheory_1 (N : ℕ) : ∃ p ≥ N, Prime p := by
  sorry

theorem gauss_lemma {d a b : ℤ} (h1 : d ∣ a * b) (h2 : gcd a d = 1) : d ∣ b := by
  sorry

theorem euclid_lemma {a b p : ℕ} (hp : Prime p) (H : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  sorry

theorem euclid_lemma_pow (a k p : ℕ) (hp : Prime p) (hk : 1 ≤ k) (H : p ∣ a ^ k) :
    p ∣ a := by
  sorry

theorem irrat_aux_wf (b k : ℕ) (hb : k ≠ 0) (hab : b ^ 2 = 2 * k ^ 2) :
    k < b := by
  sorry

theorem irrat_aux (a b : ℕ) (hb : b ≠ 0) : a ^ 2 ≠ 2 * b ^ 2 := by
  sorry

theorem NumberTheory_2 : ¬ ∃ a b : ℕ, b ≠ 0 ∧ a ^ 2 = 2 * b ^ 2 := by
  intro h
  obtain ⟨a, b, hb, hab⟩ := h
  have := irrat_aux a b hb
  contradiction

theorem NumberTheory_3 : ¬ ∃ a b : ℤ, b ≠ 0 ∧ b ^ 2 = 2 * a ^ 2 := by
  sorry

end NumberTheory
