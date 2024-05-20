import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  . right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · exact ⟨xs, by left; exact xt⟩
  · exact ⟨xs, Or.inr xu⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  exact ⟨⟨xs, fun h ↦ xntu (Or.inl h)⟩, fun h ↦ xntu (Or.inr h)⟩

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun _ h ↦ ⟨h.2, h.1⟩) (fun _ h ↦ ⟨h.2, h.1⟩)

example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  · exact fun _ h ↦ h.1
  · exact fun _ h ↦ ⟨h, Or.inl h⟩

example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  · rintro x (hl | hr); exact hl; exact hr.1
  · exact fun _ h ↦ Or.inl h

example : s \ t ∪ t = s ∪ t := by
  apply Subset.antisymm
  · rintro x (hl | hr); left; exact hl.1; right; exact hr
  · rintro x (hl | hr);
    · rcases em (x ∈ t) with (h1 | h2); right; exact h1; left; exact ⟨hl, h2⟩
    · right; exact hr

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  · rintro x (h1 | h2)
    · exact ⟨Or.inl h1.1, fun h ↦ h1.2 h.2⟩
    · exact ⟨Or.inr h2.1, fun h ↦ h2.2 h.1⟩
  · rintro x ⟨(h1 | h2), h3⟩
    · left; exact ⟨h1, fun h ↦ h3 ⟨h1, h⟩⟩
    · right; exact ⟨h2, fun h ↦ h3 ⟨h, h2⟩⟩

example (A B C D : Set α) : (A ∩ B) \ (C ∩ D) ⊆ (A \ C) ∪ (B \ D) := by
  rintro x ⟨⟨xA, xB⟩, h⟩
  rcases em (x ∈ C) with (xc | xnc)
  · right; exact ⟨xB, fun xd ↦ h ⟨xc, xd⟩⟩
  · left; exact ⟨xA, xnc⟩


def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  rintro x ⟨xp, xge2⟩; simp only [mem_setOf_eq] at xp;
  simp only [gt_iff_lt, mem_setOf_eq] at xge2;
  simp only [mem_setOf_eq]; rintro xeven; absurd xp
  unfold Nat.Prime; unfold Even at xeven; rcases xeven with ⟨r, hr⟩;rw [← two_mul] at hr; rintro irrx
  have : 1 < r := by linarith
  have h1: ¬ IsUnit r := by simp only [Nat.isUnit_iff]; linarith [this]
  have h2: ¬ IsUnit 2 := by norm_num
  have : _ := irrx.2 2 r hr;
  rcases this with (hl | hr); exact h2 hl; exact h1 hr



#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  exact fun x xs ↦ ⟨h₀ x (ssubt xs), h₁ x (ssubt xs)⟩

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _, hp⟩; exact ⟨x, ssubt xs, hp⟩

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  apply Subset.antisymm
  · intro x; simp only [mem_union, mem_iInter]; intro h;
    rcases h with (hl | hr)
    · exact fun _ ↦ Or.inr hl
    · exact fun i ↦ Or.inl (hr i)
  · intro x; simp only [mem_iInter, mem_union]; intro h;
    rcases em (x ∈ s) with (xs | xns)
    · left; exact xs
    · right; intro i; have : _ := h i;
      rcases this with (xai | xs)
      · exact xai
      · exfalso; exact xns xs

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  ext x; apply Iff.intro
  · intro _; simp only [mem_univ]
  · simp only [mem_univ, mem_iUnion, mem_setOf_eq, exists_prop, true_implies]
    have h : _ := Nat.exists_infinite_primes x
    rcases h with ⟨u, ⟨h1, h2⟩⟩
    unfold primes; simp only [mem_setOf_eq]; exact ⟨u, ⟨h2, h1⟩⟩


end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
