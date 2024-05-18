import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos


theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have h1 : n ≥ Ns := ge_trans nge (Nat.le_max_left Ns Nt)
  have h2 : n ≥ Nt := ge_trans nge (Nat.le_max_right Ns Nt)
  have h3 : _ := hs n h1; have h4 : _ := ht n h2
  have : ε = ε / 2 + ε / 2 := by field_simp;; rw [this]
  have : (s n - a) + (t n - b) = s n + t n - (a + b) := by ring;; rw [← this]
  exact lt_of_le_of_lt (abs_add (s n - a) (t n - b)) (add_lt_add h3 h4)


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro e epos; rcases cs (|c|⁻¹ * e) (by positivity) with ⟨N, hN⟩; dsimp
  use N; intro n nge; have h': _ := hN n nge
  have : |c * s n - c * a| = |c| * |s n - a| := by rw [← mul_sub, abs_mul];; rw [this]
  have : e = |c| * (|c|⁻¹ * e) := by field_simp;; rw [this]
  apply (mul_lt_mul_left _).mpr; exact h'; exact acpos

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn; have h': _ := h n hn
  have : s n = a + (s n - a) := by ring;; rw [this];
  exact lt_of_le_of_lt (abs_add a (s n - a)) (by linarith[h'])

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁; intro n nge;
  have h1 : n ≥ N₀ := ge_trans nge (Nat.le_max_left N₀ N₁)
  have h2 : n ≥ N₁ := ge_trans nge (Nat.le_max_right N₀ N₁)
  have h3 : _ := h₀ n h1; have h4 : _ := h₁ n h2; rw[sub_zero] at h4;
  rw[sub_zero, abs_mul];
  have : ε = B * (ε / B) := by field_simp;; rw [this];
  have : |s n| * |t n| ≤ B * |t n| := mul_le_mul_of_nonneg_right (le_of_lt h3) (abs_nonneg (t n))
  apply lt_of_le_of_lt this _; exact (mul_lt_mul_left Bpos).mpr h4


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply abs_pos.mpr; intro h'; have : a = (a - b) + b := by ring;
    apply abne; rw[this, h', zero_add]
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by exact hNa N (Nat.le_max_left Na Nb)
  have absb : |s N - b| < ε := by exact hNb N (Nat.le_max_right Na Nb)
  have : |a - b| < |a - b| := by
    have : a - b = (a - s N) + (s N - b) := by ring;; nth_rw 1 [this]
    apply lt_of_le_of_lt (abs_add _ _) _
    have : a - s N = -(s N - a) := by ring;; rw[this, abs_neg];
    apply lt_of_lt_of_le (add_lt_add absa absb) _; apply le_of_eq;
    show |a - b| / 2 + |a - b| / 2 = |a - b|; field_simp
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
