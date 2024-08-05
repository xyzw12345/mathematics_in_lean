import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order
import MIL.common

-- Finset.sum ∧ Finset.prod
section

variable {α : Type*} {β : Type*} [AddCommMonoid β] [CommMonoid β] (s' : Finset α) (f' : α → β)

-- basic usage

/-
 -  ∑\∏ x, f x                -- x's type should be a Fintype
 -  ∑\∏ x ∈ s, f x            -- s should be a Finset
 -  ∑\∏ x ∈ s with p x, f x   -- p is some property for ele in s
-/

-- example
variable (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)
open BigOperators
open Finset
example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl

example (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, mul_add 2, ← ih]
    ring

#check BigOperators.bigprod

def p : ℕ → Prop := fun n ↦ Odd n

noncomputable instance : DecidablePred p := fun n ↦ Classical.propDecidable (p n)

example (n : ℕ) : ∑ i ∈ range (2 * n) with p i, i = n * n := by
  sorry

-- practice
example (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := sorry


def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with d hd
  · simp only [range_zero, prod_empty]; rfl
  · show (d + 1) * fac d = ∏ i ∈ range (d + 1), (i + 1)
    rw [hd, Finset.prod_range_succ, mul_comm (d + 1) _]

variable {X : Type*} [MetricSpace X]
open Set Filter
open Topology Filter

example {u : ℕ → X} (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry

end
