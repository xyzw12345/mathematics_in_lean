import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

instance (S : Type*) : Mul {f : S → S // f.Bijective} where
  mul := fun f g ↦ ⟨fun x ↦ f.1 (g.1 x), ⟨fun x y hxy ↦ g.2.1 (f.2.1 hxy), fun x ↦ ⟨Classical.choose (g.2.2 (Classical.choose (f.2.2 x))), by
    set u := Classical.choose (f.2.2 x) with hu
    set v := Classical.choose (g.2.2 u)
    show (f.1 (g.1 (Classical.choose (g.2.2 (Classical.choose (f.2.2 x)))))) = x
    rw [← hu]
    rw [Classical.choose_spec (g.2.2 u), Classical.choose_spec (f.2.2 x)]
    ⟩⟩⟩

instance (S : Type*): One {f : S → S // f.Bijective} where
  one := ⟨fun x ↦ x, ⟨fun _ _ h ↦ h, fun x ↦ ⟨x, rfl⟩⟩⟩

noncomputable instance (S : Type*): Inv {f : S → S // f.Bijective} where
  inv := fun f ↦ ⟨fun x ↦ (Classical.choose (f.2.2 x)), ⟨fun x y hxy ↦ (by
    rw [← Classical.choose_spec (f.2.2 x), ← Classical.choose_spec (f.2.2 y)]
    show f.1 (Classical.choose (f.2.2 x)) = f.1 (Classical.choose (f.2.2 y))
    have : Classical.choose (f.2.2 x) = Classical.choose (f.2.2 y) := by exact hxy
    rw [this]
    ), (fun x ↦ ⟨f.1 x, (by
      apply f.2.1
      exact Classical.choose_spec (f.2.2 (f.1 x))
      )⟩
    )⟩⟩

noncomputable instance (S : Type*) : Group {f : S → S // f.Bijective} where
  mul := (· * ·)
  mul_assoc := fun f g h ↦ rfl
  one := 1
  one_mul := fun x ↦ rfl
  mul_one := fun x ↦ rfl
  inv := fun f ↦ f⁻¹
  mul_left_inv := fun f ↦ (by
    ext x
    show (Classical.choose (f.2.2 (f.1 x))) = x
    have : _ := (Classical.choose_spec (f.2.2 (f.1 x)))
    apply f.2.1
    rw [this]
  )
