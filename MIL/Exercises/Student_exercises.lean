import Mathlib

-- lemma upup (d s t: ℕ) (a b : ℤ) (ha: a ≥ 0) (hb: b ≥ 0) (h: s * a + d = t * b) : ∃ m n : ℕ, s * m + d =  t * n := by
--   refine' ⟨(Int.natAbs a), (Int.natAbs b), _⟩
--   rw [← (Int.natAbs_of_nonneg ha), ← (Int.natAbs_of_nonneg hb)] at h
--   exact Int.ofNat_inj.1 h

-- theorem Nat.bezout {s t : ℕ } (h₂: 0 < t): ∃ m : ℕ ,∃ n : ℕ , s * m + Nat.gcd s t = t * n:= by
--   by_cases h₁: s ≤ 0
--   · have h : s = 0 := by exact le_zero.mp h₁
--     use 0,1
--     simp only [h, mul_zero, gcd_zero_left, zero_add, mul_one]
--   · push_neg at h₁
--     let x := Nat.gcdA s t
--     let y := Nat.gcdB s t
--     have L1 : s * (t * (|x| + |y|) - x) +  s.gcd t = t * (s *(|x| + |y|) + y) := by
--       rw [Nat.gcd_eq_gcd_ab]
--       simp only
--       linarith
--     have L2 : 0 ≤ (t * (|x| + |y|) - x):= by
--       simp only [sub_nonneg]
--       have : t ≥ 1 := by exact h₂
--       nth_rw 1 [← one_mul (gcdA s t)]
--       apply mul_le_mul
--       simp only [one_le_cast]
--       apply this
--       apply le_add_of_le_of_nonneg
--       exact le_abs_self (gcdA s t)
--       apply abs_nonneg
--     have L3 : 0 ≤ (s * (|x| + |y|) + y) := by
--       have h1 : s ≥ 1 := by exact h₁
--       simp only [ge_iff_le]
--       rw[mul_add,add_assoc]
--       apply le_add_of_le_of_nonneg
--       rw [← zero_mul 0]
--       apply mul_le_mul
--       linarith
--       apply abs_nonneg
--       linarith
--       linarith
--       have :  |gcdB s t| ≥ gcdB s t := by exact le_abs_self (gcdB s t)
--       nth_rw 2 [← one_mul (gcdB s t)]
--       have h2 : 1 * (-gcdB s t) ≤ ↑s * |gcdB s t| := by
--         rw[mul_comm, mul_comm ↑s |gcdB s t|]
--         apply mul_le_mul
--         have h3 : |gcdB s t| = |-gcdB s t| := by exact (abs_neg (gcdB s t)).symm
--         rw [h3]
--         exact le_abs_self (-gcdB s t)
--         simp only [one_le_cast]
--         exact  h1
--         linarith
--         apply abs_nonneg
--       linarith

--     exact upup (Nat.gcd s t) s t (t * (|x| + |y|) - x) (s * (|x| + |y|) + y) L2 L3 L1

example {G : Type*} [Group G] (h: ∀ (x y : G), (x * y)⁻¹ = x⁻¹ * y⁻¹) : CommGroup G := by
refine CommGroup.mk ?mul_comm
intro a b
nth_rw 1 [←DivisionMonoid.inv_inv a ]
nth_rw 1 [←DivisionMonoid.inv_inv b]
rw[←DivisionMonoid.mul_inv_rev,←h,DivisionMonoid.inv_inv]
