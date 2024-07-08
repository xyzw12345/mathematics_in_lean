import Mathlib.Tactic

noncomputable section

namespace C06

section structure_point

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  · exact hx
  · exact hy
  · exact hz

def myPoint1 : Point where
  x := 2
  y := - 1
  z := 4

def myPoint2 : Point :=
  ⟨2, - 1, 4⟩

def myPoint3 :=
  Point.mk 2 (- 1) 4

structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build

#check Point'.build 2 (- 1) 4

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by
  simp only [add, add_comm]

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  simp only [add]
  ext <;> dsimp
  · exact add_assoc a.x b.x c.x
  · exact add_assoc a.y b.y c.y
  · exact add_assoc a.z b.z c.z

-- r • (x, y, z) = (r * x, r * y, r * z)
def smul (r : ℝ) (a : Point) : Point :=
  ⟨r * a.x, r * a.y, r * a.z⟩

theorem smul_distrib (r : ℝ) (a b : Point) : (smul r a).add (smul r b) = smul r (a.add b) := by
  simp only [smul, add]
  ext
  · exact Eq.symm (left_distrib r a.x b.x)
  · exact Eq.symm (left_distrib r a.y b.y)
  · exact Eq.symm (left_distrib r a.z b.z)

end Point

def Point'' :=
  ℝ × (ℝ × ℝ)

variable {a : Point''}

#check a.1

--#check a.3

#check a.2.2



def PReal :=
  { x : ℝ // 0 < x }

structure PReal' where
  val : ℝ
  property : 0 < val

variable (x : PReal')

#check x.val

#check x.property

#check x.1

#check x.2

end structure_point



section structure_group

structure AddGroup₀ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  add_left_neg : ∀ x : α, add (neg x) x = zero

namespace Point

-- `-(x, y, z) = (-x, -y, -z)`
def neg (a : Point) : Point := ⟨- a.x, - a.y, - a.z⟩

def zero : Point := ⟨0, 0, 0⟩

def addGroupPoint : AddGroup₀ Point where
  add := add
  zero := zero
  neg := neg
  add_assoc := C06.Point.add_assoc
  add_zero := by
    intro a
    simp only [add, zero, add_zero]
  zero_add := by
    intro a
    simp only [add, zero, zero_add]
  add_left_neg := by
    intro a
    simp only [neg, add, zero]
    ext <;> dsimp
    · exact neg_add_self a.x
    · exact neg_add_self a.y
    · exact neg_add_self a.z

end Point

structure Group₀ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

end structure_group


section class_group

class AddGroup₂ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  add_left_neg : ∀ x : α, add (neg x) x = zero

open AddGroup₂

theorem add_right_neg {α : Type*} [AddGroup₂ α] (x : α) : add x (neg x) = zero := by
  calc
    _ = add (neg (add x (neg x))) (add (add x (neg x)) (add x (neg x))) := by
      rw [← AddGroup₂.add_assoc, AddGroup₂.add_left_neg, AddGroup₂.zero_add]
    _ = _ := by
      nth_rw 2 [← AddGroup₂.add_assoc, AddGroup₂.add_assoc]
      rw [AddGroup₂.add_left_neg, AddGroup₂.add_zero, AddGroup₂.add_left_neg]

namespace Point

instance addGroupPoint' : AddGroup₂ Point where
  add := add
  zero := zero
  neg := neg
  add_assoc := C06.Point.add_assoc
  add_zero := by
    intro a
    simp only [add, zero, add_zero]
  zero_add := by
    intro a
    simp only [add, zero, zero_add]
  add_left_neg := by
    intro a
    simp only [neg, add, zero]
    ext <;> dsimp
    · exact neg_add_self a.x
    · exact neg_add_self a.y
    · exact neg_add_self a.z

theorem add_right_neg (x : Point) : add x (neg x) = zero :=
  C06.add_right_neg x

variable (a b : Point)

instance instAdd : Add Point where
  add a b := add a b

#check a + b

end Point

end class_group



section hierachies

-- only for notation
class One₁ (α : Type) where
  /-- The element one -/
  one : α

#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

example (α : Type) [One₁ α] : α := One₁.one

example (α : Type) [One₁ α] := (One₁.one : α)

@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl


class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia


class Semigroup₂ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

variable {a : Type*} [Semigroup₂ α] (a b : α)

--#check a ⋄ b

attribute [instance] Semigroup₂.toDia₁

#check a ⋄ b

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b


class Semigroup₁ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α


class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α


example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl


/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk


#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁


class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]

open DiaOneClass₁ Semigroup₁ Group₁

example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]

lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  apply left_inv_eq_right_inv₁ (inv_dia a) h

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  rw [← inv_dia a⁻¹, inv_eq_of_dia (inv_dia a)]

class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1


attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

open Group₃

@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv' (Group₃.inv_mul a) h

@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  rw [← inv_mul a⁻¹, inv_eq_of_mul (inv_mul a)]

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

end hierachies



section subgroup

#check Subgroup
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Basic.html#Subgroup

#check Subgroup.ext

variable (G : Type*) [Group G] (H : Subgroup G) (K : Subgroup G)

-- The subgroup `H` is contained in the subgroup `K`.
#check H ≤ K

-- The intersection of two subgroups.
#check H ⊓ K

example (G : Type*) [Group G] (H : Subgroup G) (K : Subgroup G) : H ⊓ K = H ↔ H ≤ K := by
  constructor
  · intro h
    rw [← h]
    exact inf_le_right
  · intro h
    ext x
    constructor
    · intro hx
      have : H ⊓ K ≤ H := by exact inf_le_left
      exact this hx
    · intro hx
      have : x ∈ K := h hx
      exact ⟨hx, this⟩

/-- If `H` is a subgroup of `G` and `K` is a subgroup of `H`, then `K` can be viewed as a subgroup
of `G`. -/
def Subgroup.to_subgroup (G : Type*) [Group G] {H : Subgroup G} (K : Subgroup H) : Subgroup G where
  carrier := { g : G | ∃ x : H, x ∈ K ∧ x.val = g}
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨x, ⟨hx, ha⟩⟩
    rcases hb with ⟨y, ⟨hy, hb⟩⟩
    use x * y
    constructor
    · exact (Subgroup.mul_mem_cancel_right K hy).mpr hx
    · rw [← ha, ← hb]
      rfl
  one_mem' := by
    use 1
    constructor
    · exact Subgroup.one_mem K
    · rfl
  inv_mem' := by
    intro a ha
    rcases ha with ⟨x, ⟨hx, ha⟩⟩
    use x⁻¹
    constructor
    · exact (Subgroup.inv_mem_iff K).mpr hx
    · rw [← ha]
      rfl

variable (G : Type*) [Group G] {H : Subgroup G} (K : Subgroup H)

theorem Subgroup.to_subgroup_le : to_subgroup G K ≤ H := by
  intro a ha
  rcases ha with ⟨x, ⟨_, ha⟩⟩
  rw [← ha]
  exact x.property

#check Subtype.val_inj

theorem Subgroup.to_subgroup_mem (g : H) : g.1 ∈ to_subgroup G K ↔ g ∈ K := by
  constructor
  · intro hg
    rcases hg with ⟨x, ⟨hx, hg⟩⟩
    apply Subtype.val_inj.mp at hg
    rw [← hg]
    exact hx
  · intro hg
    use g

end subgroup



section examples

-- Let `G` be the set of pairs of real numbers `(x, y)`with `x ≠ 0`. Define the multiplication on `G` by `(x, y)(z, w) = (xz, xw + y)`. Prove that `G` is a group.
structure pt where
  -- fill in the rest



-- Let `G` be an abelian group. Then all elements of finite order in `G` forms a subgroup of `G`.
def fin_order : sorry := sorry



#check CommGroup.mk

-- Every cyclic group is a abelian group.
instance : sorry := sorry

end examples

end C06
