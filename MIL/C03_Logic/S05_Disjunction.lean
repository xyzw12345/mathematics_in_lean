import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  match le_or_gt 0 x with
    | Or.inl h => rw [abs_of_nonneg h]
    | Or.inr h => rw [abs_of_neg h]; linarith[h]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  have : _ := le_abs_self (-x)
  rw [abs_neg] at this; exact this

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  match le_or_gt 0 (x + y) with
  | Or.inl h => rw [abs_of_nonneg h]; exact add_le_add (le_abs_self x) (le_abs_self y)
  | Or.inr h => rw [abs_of_neg h, neg_add]; exact add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · rintro h; rcases le_or_gt 0 y with (hl | hr)
    · rw [abs_of_nonneg hl] at h; apply Or.inl; exact h;
    · rw [abs_of_neg hr] at h; apply Or.inr; exact h
  · rintro h; rcases h with (hl | hr)
    · exact lt_of_lt_of_le hl (le_abs_self y)
    · exact lt_of_lt_of_le hr (neg_le_abs_self y)
#check neg_lt_neg
theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · rintro h; exact ⟨by
      have : _ := neg_lt_neg (lt_of_le_of_lt (neg_le_abs_self x) h)
      rw [neg_neg] at this; exact this, lt_of_le_of_lt (le_abs_self x) h⟩
  · rintro h; rcases le_or_gt 0 x with (hl | hr)
    · rw [abs_of_nonneg hl]; exact h.2
    · rw [abs_of_neg hr]; have : _ := neg_lt_neg h.1; rw[← neg_neg y]; exact this

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, (hl | hr)⟩
  · rw [hl]; linarith [pow_two_nonneg x, pow_two_nonneg y]
  · rw [hr]; linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by
    calc
    _= x ^ 2 - 1 := by ring
    _= 0 := by rw[h]; ring
  simp only [mul_eq_zero] at this
  rcases this with (hl | hr)
  · left; rw[← sub_self 1, sub_eq_add_neg, sub_eq_add_neg] at hl; exact add_right_cancel hl
  · right; rw[← add_left_neg 1] at hr; exact add_right_cancel hr

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by
    calc
    _= x ^ 2 - y ^ 2 := by ring
    _= 0 := by rw[h]; ring
  simp only [mul_eq_zero] at this
  rcases this with (hl | hr)
  · left; rw[← sub_self y, sub_eq_add_neg, sub_eq_add_neg] at hl; exact add_right_cancel hl
  · right; rw[← add_left_neg y] at hr; exact add_right_cancel hr

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by
    calc
    _= x ^ 2 - 1 := by ring
    _= 0 := by rw[h]; ring
  simp only [mul_eq_zero] at this
  rcases this with (hl | hr)
  · left; rw[← sub_self 1, sub_eq_add_neg, sub_eq_add_neg] at hl; exact add_right_cancel hl
  · right; rw[← add_left_neg 1] at hr; exact add_right_cancel hr

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by
    calc
    _= x ^ 2 - y ^ 2 := by ring
    _= 0 := by rw[h]; ring
  simp only [mul_eq_zero] at this
  rcases this with (hl | hr)
  · left; rw[← sub_self y, sub_eq_add_neg, sub_eq_add_neg] at hl; exact add_right_cancel hl
  · right; rw[← add_left_neg y] at hr; exact add_right_cancel hr

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h₁
    rcases em P with (h | hn)
    · right; exact h₁ h
    · left; exact hn
  · intro h₂ hp
    rcases h₂ with (hl | hr)
    · exfalso; exact hl hp
    · exact hr
