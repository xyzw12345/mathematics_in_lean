import MIL.Common
import Mathlib.Data.Real.Basic

namespace C06S02

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

structure Group₁Cat where
  α : Type*
  str : Group₁ α

section
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl

end

example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl

def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

structure AddGroup₁ (α : Type*) where
  (add : α → α → α)
  -- fill in the rest
  zero : α
  neg : α → α
  add_comm : ∀ x y : α, add x y = add y x
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  add_neg : ∀ x : α, add x (neg x) = zero

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : Point) : Point :=
  ⟨-a.x, -a.y, -a.z⟩

def zero : Point :=
  ⟨0, 0, 0⟩

def addGroupPoint : AddGroup₁ Point :=
  ⟨add, zero, neg, by intro a b; rw [add, add]; ext; repeat' simp only; rw[add_comm] ,
    by intro a b c; rw [add, add, add, add]; ext; repeat' simp only; rw [add_assoc],
    by intro a; rw [add, zero]; ext; repeat' simp only; rw [add_zero],
    by intro a; rw [add, neg, zero]; ext; repeat' simp only; rw [add_comm, add_left_neg]⟩

end Point

section
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_right_inv, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g

end

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl

instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end

instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end

class AddGroup₂ (α : Type*) where
  add : α → α → α
  -- fill in the rest
  zero : α
  neg : α → α
  add_comm : ∀ x y : α, add x y = add y x
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  add_neg : ∀ x : α, add x (neg x) = zero

instance hasAddAddGroup₂ {α : Type*} [AddGroup₂ α] : Add α :=
  ⟨AddGroup₂.add⟩

instance hasZeroAddGroup₂ {α : Type*} [AddGroup₂ α] : Zero α :=
  ⟨AddGroup₂.zero⟩

instance hasNegAddGroup₂ {α : Type*} [AddGroup₂ α] : Neg α :=
  ⟨AddGroup₂.neg⟩

instance : AddGroup₂ Point where
  add := Point.add
  zero := Point.zero
  neg := Point.neg
  add_comm := by intro a b; rw [Point.add, Point.add]; ext; repeat' simp only; rw[add_comm]
  add_assoc := by intro a b c; rw [Point.add, Point.add, Point.add, Point.add]; ext; repeat' simp only; rw [add_assoc]
  add_zero := by intro a; rw [Point.add, Point.zero]; ext; repeat' simp only; rw [add_zero]
  add_neg := by intro a; rw [Point.add, Point.neg, Point.zero]; ext; repeat' simp only; rw [add_comm, add_left_neg]

variable (x y : Point)
#check x + (-y) + 0
