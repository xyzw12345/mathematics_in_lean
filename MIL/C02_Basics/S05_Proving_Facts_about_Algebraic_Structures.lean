import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · exact le_inf inf_le_right inf_le_left
  · exact le_inf inf_le_right inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    exact le_trans inf_le_left inf_le_left
    exact le_inf (le_trans inf_le_left inf_le_right) inf_le_right
  · apply le_inf
    exact le_inf inf_le_left (le_trans inf_le_right inf_le_left)
    exact le_trans inf_le_right inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · exact sup_le le_sup_right le_sup_left
  · exact sup_le le_sup_right le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    exact sup_le le_sup_left (le_trans le_sup_left le_sup_right)
    exact le_trans le_sup_right le_sup_right
  · apply sup_le
    exact le_trans le_sup_left le_sup_left
    exact sup_le (le_trans le_sup_right le_sup_left) le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  exact inf_le_left
  exact le_inf (le_refl x) le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  exact sup_le (le_refl x) inf_le_left
  exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · apply sup_le
    · exact le_inf le_sup_left le_sup_left
    · apply le_inf
      · exact le_trans inf_le_left le_sup_right
      · exact le_trans inf_le_right le_sup_right
  · rw [h (a ⊔ b) _ _, inf_comm, absorb1]; apply sup_le
    · exact le_sup_left
    · rw [inf_comm, h]; apply sup_le
      · exact le_trans inf_le_right le_sup_left
      · rw [inf_comm]; exact le_sup_right

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  · rw [sup_comm (a ⊓ b), h, sup_comm _ a, absorb2]; apply le_inf
    · exact inf_le_left
    · rw [sup_comm _ b, h b]; apply le_inf
      · exact le_trans inf_le_left le_sup_right
      · exact inf_le_right
  · apply le_inf
    · exact sup_le inf_le_left inf_le_left
    · apply sup_le
      · exact le_trans inf_le_right le_sup_left
      · exact le_trans inf_le_right le_sup_right

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have : _ := add_le_add_left h (-a)
  rw [add_left_neg, add_comm, ← sub_eq_add_neg] at this
  exact this

example (h: 0 ≤ b - a) : a ≤ b := by
  have : _ := add_le_add_left h a
  rw [add_zero, add_comm, sub_add, sub_self, sub_zero] at this
  exact this

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  exact mul_le_mul_of_nonneg_right h h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have : _ := dist_triangle x y x
  rw [dist_self x, ← dist_comm x y] at this
  linarith

end
