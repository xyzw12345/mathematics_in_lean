import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Basic
import MIL.Common

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  simp only [add_tsub_cancel_right, fac]
  induction' n with n ih
  · rw [fac]; norm_num
  · have : 2 ^ (n + 1) = 2 * (2 ^ n) := by exact Nat.pow_succ';; rw [this]
    apply mul_le_mul; omega; exact ih; exact Nat.zero_le (2 ^ n); omega
section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · rw [fac, prod_range_zero]
  rw [fac, ih, prod_range_succ, mul_comm]

example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction' n with n ih
  · simp only [zero_add, range_one, sum_singleton, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one, mul_zero, Nat.zero_div]
  · have : ∑ i in range (n + 1 + 1), i ^ 2 = (n + 1) ^ 2 + ∑ i in range (n + 1), i ^ 2 := by
      exact sum_range_succ_comm (fun x ↦ x ^ 2) (n + 1)
    rw [this, ih]; rw[← Nat.mul_div_left ((n + 1) ^ 2) (n := 6)];
    have : (n + 1) ^ 2 * 6 + n * (n + 1) * (2 * n + 1) = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1) := by ring
    rw [← this]; symm; apply Nat.add_div_of_dvd_right; rw [mul_comm]; use (n + 1) ^ 2; norm_num
end

inductive MyNat
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  induction' m with m ih
  · rw[zero_add, zero_add]
  · rw[succ_add, succ_add, succ_add, ih]

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction' k with k ih
  · rw [mul, add_comm, zero_add, add_comm, zero_add]
  · rw [mul, add_comm, succ_add, mul, add_comm k n, ih, add_assoc]

theorem zero_mul (n : MyNat) : mul zero n = zero := by
  induction' n with n ih
  · rw [mul]
  · rw [mul, add_comm, zero_add, ih]

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  induction' n with n ih
  · rw [mul, mul, zero_add]
  · rw [mul, mul, add_comm, succ_add, add_comm ((m.mul n).add m), succ_add];
    congr 1; rw[ih, add_comm _ n, add_comm _ m, ← add_assoc, ← add_assoc, add_comm m n]

theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  induction' m with m ih
  · rw [zero_mul, mul]
  · rw [mul, succ_mul, ih]

end MyNat
