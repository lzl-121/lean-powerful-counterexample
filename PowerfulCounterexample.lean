
Enter file contents here
import Mathlib

/-- A natural number is powerful if the square of every prime divisor divides it. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- A natural number is a perfect square. -/
def IsNatSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, k ^ 2 = n

lemma powerful_12167 : IsPowerful 12167 := by
  intro p hp hdiv
  have hfac : 12167 = 23 ^ 3 := by norm_num
  rw [hfac] at hdiv ⊢
  have hp23dvd : p ∣ 23 := hp.dvd_of_dvd_pow hdiv
  have hp23 : p = 23 :=
    (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23)).mp hp23dvd
  subst p
  norm_num

lemma powerful_12168 : IsPowerful 12168 := by
  intro p hp hdiv
  have hfac : 12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num
  rw [hfac] at hdiv ⊢
  rcases hp.dvd_mul.mp hdiv with hleft | h13pow
  · rcases hp.dvd_mul.mp hleft with h2pow | h3pow
    · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h2pow
      have hp2 : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).mp h2
      subst p
      norm_num
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow h3pow
      have hp3 : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h3
      subst p
      norm_num
  · have h13 : p ∣ 13 := hp.dvd_of_dvd_pow h13pow
    have hp13 : p = 13 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp h13
    subst p
    norm_num

lemma not_square_12167 : ¬ IsNatSquare 12167 := by
  rintro ⟨k, hk⟩
  have hk_lt : k < 111 := by nlinarith
  have hk_le : k ≤ 110 := by omega
  nlinarith

lemma not_square_12168 : ¬ IsNatSquare 12168 := by
  rintro ⟨k, hk⟩
  have hk_lt : k < 111 := by nlinarith
  have hk_le : k ≤ 110 := by omega
  nlinarith

/-- Two consecutive powerful numbers need not include a perfect square. -/
theorem consecutive_powerful_counterexample :
    ∃ a b : ℕ,
      a + 1 = b ∧
      IsPowerful a ∧ IsPowerful b ∧
      ¬ IsNatSquare a ∧ ¬ IsNatSquare b := by
  refine ⟨12167, 12168, ?_, powerful_12167, powerful_12168,
    not_square_12167, not_square_12168⟩
  norm_num
