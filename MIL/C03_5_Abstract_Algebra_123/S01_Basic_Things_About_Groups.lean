import MIL.Common

section Axioms_of_Groups

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  rw [← one_mul (a * a⁻¹)]
  nth_rw 1 [← mul_left_inv (a * a⁻¹)]
  rw [mul_assoc, mul_assoc, ← mul_assoc a⁻¹, mul_left_inv, one_mul, mul_left_inv]

theorem mul_one (a : G) : a * 1 = a := by
  rw[← mul_left_inv a, ← mul_assoc, mul_right_inv a, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← mul_one (b⁻¹ * a⁻¹), ← mul_right_inv (a * b), ← mul_assoc, mul_assoc b⁻¹, ← mul_assoc a⁻¹, mul_left_inv, one_mul, mul_left_inv, one_mul]

end MyGroup

end Axioms_of_Groups


section From_SemiGroup_To_Group

theorem exist_left_identity {G : Type*} [Semigroup G] (u : G) (h : ∀ a b : G, (∃ x : G, x * a = b) ∧ (∃ y : G, a * y = b)) : ∃ (e : G), (∀ g : G, e * g = g) := by
  rcases (h u u).1 with ⟨e, he⟩
  use e
  intro g
  rcases (h u g).2 with ⟨x, hx⟩
  rw [← hx, ← mul_assoc, he]

theorem exist_right_identity {G : Type*} [Semigroup G] (u : G) (h : ∀ a b : G, (∃ x : G, x * a = b) ∧ (∃ y : G, a * y = b)) : ∃ (e : G), (∀ g : G, g * e = g) := by
  rcases (h u u).2 with ⟨e, he⟩
  use e
  intro g
  rcases (h u g).1 with ⟨x, hx⟩
  rw [← hx, mul_assoc, he]

theorem unique_identity {G : Type*} [Semigroup G] (e1 e2 : G) (he1 : ∀ g : G, g * e1 = g) (he2 : ∀ g : G, e2 * g = g) : e1 = e2 := by
  rw [← (he1 e2), he2 e1]


noncomputable instance {G : Type*} [Semigroup G] [h_nonempty : Nonempty G] (h : ∀ a b : G, (∃ x : G, x * a = b) ∧ (∃ y : G, a * y = b)) : Group G := by
  let u := h_nonempty.1
  rcases (h u u).2 with ⟨e, he⟩
  exact {
    one := e,
    one_mul := (by
      intro
      ),
    mul_one := sorry,
    inv := sorry
    mul_left_inv := sorry
  }
