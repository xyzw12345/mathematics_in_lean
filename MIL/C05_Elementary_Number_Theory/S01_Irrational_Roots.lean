import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    have : 2 ∣ (m * m) := by
      rw [← pow_two m, sqr_eq]; exact dvd_mul_right 2 (n ^ 2)
    have : _ := Nat.prime_two.dvd_mul.mp this
    simp only [or_self] at this; exact this
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by
    exact Nat.mul_left_cancel (by norm_num) this
  have : 2 ∣ n := by
    have : 2 ∣ (n * n) := by
      rw [← pow_two n, ← this]; exact dvd_mul_right 2 (k ^ 2)
    have : _ := Nat.prime_two.dvd_mul.mp this
    simp only [or_self] at this; exact this
  have : 2 ∣ m.gcd n := by
    apply dvd_gcd (by assumption) (by assumption)
  have : 2 ∣ 1 := by
    rw [coprime_mn] at this; exact this
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have : p ∣ m := by
    have : p ∣ (m * m) := by
      rw [← pow_two m, sqr_eq]; exact dvd_mul_right p (n ^ 2)
    have : _ := (Nat.Prime.dvd_mul prime_p).mp this
    simp only [or_self] at this; exact this
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    exact Nat.mul_left_cancel (by exact Nat.Prime.pos prime_p) this
  have : p ∣ n := by
    have : p ∣ (n * n) := by
      rw [← pow_two n, ← this]; exact dvd_mul_right p (k ^ 2)
    have : _ := (Nat.Prime.dvd_mul prime_p).mp this
    simp only [or_self] at this; exact this
  have : p ∣ m.gcd n := by
    apply dvd_gcd (by assumption) (by assumption)
  have : p ∣ 1 := by
    rw [coprime_mn] at this; exact this
  simp only [Nat.dvd_one] at this; rw [this] at prime_p; absurd prime_p; norm_num

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw [Nat.factorization_pow]; simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [Nat.factorization_mul, Nat.factorization_pow, Nat.Prime.factorization]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply, Finsupp.single_eq_same, Pi.mul_apply, Pi.ofNat_apply]
    rw[add_comm]; exact prime_p; exact Nat.Prime.ne_zero prime_p; exact nsqr_nez
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (prime_p : p.Prime) :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw [Nat.factorization_pow]; simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have eq2 : (r.succ * n ^ k).factorization p =
      k * n.factorization p + r.succ.factorization p := by
    rw [Nat.factorization_mul, Nat.factorization_pow]
    simp only [Nat.succ_eq_add_one, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Pi.natCast_def,
      Nat.cast_id, Pi.add_apply, Pi.mul_apply]; rw [add_comm]; simp only [Nat.succ_eq_add_one,
        ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true]; simp only [ne_eq,
          pow_eq_zero_iff', not_and, Decidable.not_not]; simp only [nnz, false_implies]
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  use (m.factorization p - n.factorization p)
  rw [Nat.mul_sub_left_distrib]

#check multiplicity
