import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm (max_le _ _) (max_le _ _)
  exact le_max_right b a
  exact le_max_left b a
  exact le_max_right a b
  exact le_max_left a b

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm (le_min _ (le_min _ _)) (le_min (le_min _ _) _)
  exact le_trans (min_le_left _ _) (min_le_left _ _)
  exact le_trans (min_le_left _ _) (min_le_right _ _)
  exact min_le_right _ _
  exact min_le_left _ _
  exact le_trans (min_le_right _ _) (min_le_left _ _)
  exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  exact le_min (add_le_add_right (min_le_left a b) c) (add_le_add_right (min_le_right a b) c)

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm (aux a b c)
  have : min a b = a ∨ min a b = b := by exact min_choice a b
  rcases this with (hl | hr)
  rw [hl]; apply min_le_left
  rw [hr]; apply min_le_right

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have : _ := abs_add (a - b) b
  rw [sub_add a b b, sub_self, sub_zero] at this
  rw [tsub_le_iff_right]; exact this

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add (dvd_add _ _) _
  rw [← mul_assoc, mul_comm y x, mul_assoc]; exact dvd_mul_right x _
  rw [pow_two]; exact dvd_mul_right x _
  rw [pow_two]; exact dvd_mul_of_dvd_left h _

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm (dvd_gcd _ _) (dvd_gcd _ _)
  exact gcd_dvd_right m n
  exact gcd_dvd_left m n
  exact gcd_dvd_right n m
  exact gcd_dvd_left n m


end
