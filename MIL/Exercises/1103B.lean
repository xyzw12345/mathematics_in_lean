import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Basic

variable {α : Type}

@[ext]
structure Sym (S : Set α) where
  Fun : {x // x ∈ S} → {x // x ∈ S}
  invFun : {x // x ∈ S} → {x // x ∈ S}
  left_inv : ∀ x : {x // x ∈ S}, invFun (Fun x) = x
  right_inv : ∀ x : {x // x ∈ S}, Fun (invFun x) = x

#check Sym.ext
#check Sym.ext_iff

structure Sym' {S T : Set α} (h : T ⊆ S) extends Sym S where
  T_invariant : ∀ x : {x // x ∈ T}, Fun ((fun ⟨x, xt⟩ ↦ ⟨x, h xt⟩) x) = (fun ⟨x, xt⟩ ↦ ⟨x, h xt⟩) x

instance (S : Set α) : One (Sym S) where
  one := ⟨fun (x : {x // x ∈ S}) ↦ x, fun (x : {x // x ∈ S}) ↦ x, by intro x; rfl, by intro x; rfl⟩

instance (S : Set α) : Mul (Sym S) where
  mul := fun f g ↦ {
    Fun := fun (x : {x // x ∈ S}) ↦ f.Fun (g.Fun x)
    invFun := fun (x : {x // x ∈ S}) ↦ g.invFun (f.invFun x)
    left_inv := fun ⟨x, xs⟩ ↦ (by
      dsimp
      rw [f.left_inv, g.left_inv]
    )
    right_inv := fun ⟨x, xs⟩ ↦ (by
      dsimp
      rw [g.right_inv, f.right_inv]
    )
  }

instance (S : Set α) : Inv (Sym S) where
  inv := fun f ↦ ⟨f.invFun, f.Fun, f.right_inv, f.left_inv⟩

instance (S : Set α): Group (Sym S) where
  mul := (· * ·)
  mul_assoc := fun f g h ↦ rfl
  one := ⟨fun (x : {x // x ∈ S}) ↦ x, fun (x : {x // x ∈ S}) ↦ x, by intro x; rfl, by intro x; rfl⟩
  one_mul := fun f ↦ rfl
  mul_one := fun f ↦ rfl
  inv := fun f ↦ f⁻¹
  mul_left_inv := fun f ↦ (by
    ext x
    · show (f.invFun (f.Fun x)).val = x.val
      congr 1
      exact f.left_inv x
    · show (f.invFun (f.Fun x)).val = x.val
      congr 1
      exact f.left_inv x
  )

instance {S T : Set α} (ssubt : T ⊆ S) : Mul (Sym' ssubt) where
  mul := fun f g ↦ {
    Fun := fun (x : {x // x ∈ S}) ↦ f.Fun (g.Fun x)
    invFun := fun (x : {x // x ∈ S}) ↦ g.invFun (f.invFun x)
    left_inv := fun (x : {x // x ∈ S}) ↦ (by
      show g.invFun (f.invFun (f.Fun (g.Fun x))) = x
      rw [f.left_inv, g.left_inv])
    right_inv := fun (x : {x // x ∈ S}) ↦ (by
      show f.Fun (g.Fun (g.invFun (f.invFun x))) = x
      rw [g.right_inv, f.right_inv])
    T_invariant := fun (⟨x, xt⟩ : {x // x ∈ T}) ↦ (by
      show f.Fun (g.Fun ⟨x, _⟩) = ⟨x, _⟩
      have hg : g.Fun ⟨x, ssubt xt⟩ = ⟨x, ssubt xt⟩ := g.T_invariant ⟨x, xt⟩
      have hf : f.Fun ⟨x, ssubt xt⟩ = ⟨x, ssubt xt⟩ := f.T_invariant ⟨x, xt⟩
      rw [hg, hf]
    )
  }


instance {S T : Set α} (ssubt : T ⊆ S) : One (Sym' ssubt) where
  one := ⟨(1 : Sym S), fun ⟨_, _⟩ ↦ rfl⟩

instance {S T : Set α} (ssubt : T ⊆ S) : Inv (Sym' ssubt) where
  inv := fun ⟨f, h⟩ ↦ ⟨f⁻¹, fun ⟨x, xt⟩ ↦ (by
    sorry
  )⟩

instance {S T : Set α} (ssubt : T ⊆ S) : Group (Sym' ssubt) where
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry

instance (S T : Set α) (ssubt : S ⊆ T) : Sym (S \ T) ≃* Sym' ssubt where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
