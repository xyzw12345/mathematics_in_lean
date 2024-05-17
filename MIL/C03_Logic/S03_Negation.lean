import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro ⟨a, ha⟩; rcases h a with ⟨x, hx⟩; exact lt_irrefl a (lt_of_le_of_lt (ha x) hx)

example : ¬FnHasUb fun x ↦ x := by
  intro ⟨a, ha⟩; have : a + 1 ≤ a := by exact ha (a + 1);; linarith [this]

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra h''; push_neg at h''; have : _ := h h''; exact not_le_of_gt h' this

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  by_contra h''; exact not_le_of_gt h' (h'' h)

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by rintro x y _; have hx: f x = 0 := by rfl;; have _: f y = 0 := by rfl;; rw[hx]
  have h' : f 1 ≤ f 0 := le_refl _
  have : 1 ≤ 0 := h monof h'
  absurd this; norm_num

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt; rintro hx; have : _ := h x hx
  exact lt_irrefl x this

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x :=
  fun x hx ↦ h ⟨x, hx⟩

example (h : ∀ x, ¬P x) : ¬∃ x, P x :=
  fun ⟨x, hx⟩ ↦ h x hx

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'; apply h; intro x; by_contra h''; apply h'; exact ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  rcases h with ⟨x, nh⟩
  exact fun hh ↦ nh (hh x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

#check not_not
example (h : ¬¬Q) : Q := by
  exact not_not.mp h

example (h : Q) : ¬¬Q := by
  exact not_not.mpr h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  unfold FnHasUb at h; unfold FnUb at h; push_neg at h; exact h

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  unfold Monotone at h; push_neg at h; exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
