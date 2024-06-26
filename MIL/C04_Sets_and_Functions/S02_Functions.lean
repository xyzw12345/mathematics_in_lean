import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  apply Iff.intro;
  · rintro h x xs; unfold preimage; simp only [mem_setOf_eq];
    have : f x ∈ f '' s := by simp only [mem_image]; use x
    exact h this
  · rintro h x ⟨y, ys, hy⟩; have : _ := h ys; rw [← hy];
    assumption

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x ⟨y, ys, hy⟩; have : _ := h hy; rw[← this]; exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x ⟨y, ys, hy⟩; rw [← hy]; assumption

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x xu; rcases h x with ⟨y, hy⟩;
  have : y ∈ f⁻¹' u := by show f y ∈ u; rw [hy]; exact xu
  use y

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x ⟨y, ys, hy⟩; rw [← hy]; use y; exact ⟨h ys, by rfl⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx; simp only [mem_preimage] at hx; show f x ∈ v; exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  apply Subset.antisymm;
  · intro x hx; simp only [preimage_union, mem_union, mem_preimage] at hx; assumption
  · rintro x (hu | hv); left; exact hu; right; exact hv;

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x ⟨y, ⟨ys, yt⟩, hy⟩; exact ⟨⟨y, ys, hy⟩, ⟨y, yt, hy⟩⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by apply h; rw [hy, hz];
  rw [← this] at zt; exact ⟨y, ⟨ys, zt⟩, hy⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x h; rcases h.1 with ⟨y, ys, hy⟩;
  use y; exact ⟨⟨ys, fun yt ↦ h.2 ⟨y, yt, hy⟩⟩, hy⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x h; assumption

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  apply Subset.antisymm
  · intro x ⟨⟨y, ys, hy⟩, xv⟩; use y; rw[← hy] at xv; exact ⟨⟨ys, xv⟩, hy⟩
  · intro x ⟨y, ⟨ys, yv⟩, hy⟩; simp only [mem_preimage] at yv; rw [hy] at yv
    exact ⟨⟨y, ys, hy⟩, yv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x ⟨y, ⟨ys, xu⟩, hy⟩; simp only [mem_preimage] at xu; rw [hy] at xu;
  exact ⟨⟨y, ys, hy⟩, xu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, yu⟩; simp only [mem_preimage] at yu; show f x ∈ f '' s ∩ u
  exact ⟨⟨x, xs, by rfl⟩, yu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | yu)
  · left; exact ⟨x, xs, by rfl⟩
  · right; exact yu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  apply Subset.antisymm
  · intro x ⟨y, yai, hy⟩; have : ∃ i, y ∈ A i := by exact exists_exists_eq_and.mp yai;; rcases this with ⟨i, yi⟩
    simp only [mem_iUnion, mem_image]; exact ⟨i, ⟨y, yi, hy⟩⟩
  · simp only [iUnion_subset_iff, image_subset_iff]; intro i x xi;
    show f x ∈ f '' ⋃ i, A i; simp only [mem_image, mem_iUnion];
    exact ⟨x, ⟨i, xi⟩, by rfl⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x ⟨y, yai, hy⟩
  simp only [mem_iInter] at yai; simp only [mem_iInter, mem_image];
  exact fun i ↦ ⟨y, ⟨yai i, hy⟩⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x xai; simp only [mem_iInter, mem_image] at xai;
  rcases xai i with ⟨y, _, hy⟩; use y; constructor
  · simp only [mem_iInter]; intro j; rcases xai j with ⟨y', y'ai, hy'⟩
    have : y' = y := by apply injf; rw [hy, hy']
    rw [this] at y'ai; exact y'ai
  · exact hy

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  apply Subset.antisymm
  · intro x; simp only [preimage_iUnion, mem_iUnion, mem_preimage, imp_self]
  · intro x; simp only [mem_iUnion, mem_preimage, preimage_iUnion, imp_self]

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  apply Subset.antisymm
  · intro x; simp only [mem_preimage, mem_iInter, imp_self]
  · intro x; simp only [mem_iInter, mem_preimage, imp_self]

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnng y ynng h
  calc
   _= x.sqrt ^ 2 := by exact (sq_sqrt xnng).symm
   _= y.sqrt ^ 2 := by rw [h]
   _= y := by exact sq_sqrt ynng

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnng y ynng h; simp only at h
  calc
    x = (x ^ 2).sqrt := by exact (sqrt_sq xnng).symm
      _= (y ^ 2).sqrt := by rw [h]
      _= y := by exact sqrt_sq ynng

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  apply Subset.antisymm
  · intro x ⟨z, _, hz⟩
    simp only [ge_iff_le, mem_setOf_eq]; rw [← hz]; positivity
  · intro y ynng; simp only [ge_iff_le, mem_setOf_eq] at ynng
    use y ^ 2; exact ⟨by rw [mem_setOf_eq]; exact pow_two_nonneg y, by exact sqrt_sq ynng⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  apply Subset.antisymm;
  · intro x ⟨y, hy⟩; simp only at hy; simp only [ge_iff_le, mem_setOf_eq];
    rw [← hy]; positivity
  · intro y hy; simp only [mem_range]; simp only [ge_iff_le, mem_setOf_eq] at hy
    use y.sqrt; exact sq_sqrt hy


end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  apply Iff.intro;
  · intro h; unfold LeftInverse; intro x
    apply h; rw [inverse_spec (f := f) (f x) ⟨x, by rfl⟩]
  · intro h; intro x y heq; rw [← h x, ← h y, heq]

example : Surjective f ↔ RightInverse (inverse f) f := by
  apply Iff.intro
  · intro h; intro x; exact inverse_spec (f := f) x (h x)
  · intro h; intro y; use (inverse f) y; exact h y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    show j ∈ { i | i ∉ f i }; simp only [Set.mem_setOf_eq]; exact h₁
  have h₃ : j ∉ S := by
    rw [← h]; exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
