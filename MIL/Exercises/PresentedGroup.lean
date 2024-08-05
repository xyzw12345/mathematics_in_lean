import Mathlib
set_option profiler true

def u : Fin 2 := ⟨0, by norm_num⟩
def v : Fin 2 := ⟨1, by norm_num⟩

variable (n : ℕ) [Fact (1 < n)]
def r : FreeGroup (Fin 2) := FreeGroup.of u
def s : FreeGroup (Fin 2) := FreeGroup.of v

def GeneratingRelforDihedral : Set (FreeGroup (Fin 2)) := fun x ↦ (
  if x = r ^ n then True else
    if x = s ^ 2 then True else
      if x = s * r * s * r then True else False
)

lemma rn_in_GenRel : r ^ n ∈ GeneratingRelforDihedral n := by
  unfold GeneratingRelforDihedral
  simp only [if_false_right, and_true, if_true_left]
  tauto

lemma s2_in_GenRel : s ^ 2 ∈ GeneratingRelforDihedral n := by
  unfold GeneratingRelforDihedral
  simp only [if_false_right, and_true, if_true_left]
  tauto

lemma srsr_in_GenRel : s * r * s * r ∈ GeneratingRelforDihedral n := by
  unfold GeneratingRelforDihedral
  simp only [if_false_right, and_true, if_true_left]
  tauto

def Presented_Dihedral_Group : PresentedGroup (GeneratingRelforDihedral n) ≃* DihedralGroup n := by
  have liftable : ∀ r ∈ GeneratingRelforDihedral n, (FreeGroup.lift fun x ↦ if x = u then (DihedralGroup.r (1 : ZMod n)) else (DihedralGroup.sr (0 : ZMod n))) r = 1 := by
    have lift_r : (FreeGroup.lift fun x ↦ if x = u then DihedralGroup.r 1 else DihedralGroup.sr 0) r = DihedralGroup.r (1 : ZMod n) := by
      show (FreeGroup.lift fun x ↦ if x = u then DihedralGroup.r 1 else DihedralGroup.sr 0) (FreeGroup.of u) = DihedralGroup.r (1 : ZMod n)
      exact FreeGroup.lift.of
    have lift_s : (FreeGroup.lift fun x ↦ if x = u then DihedralGroup.r 1 else DihedralGroup.sr 0) s = DihedralGroup.sr (0 : ZMod n) := by
      show (FreeGroup.lift fun x ↦ if x = u then DihedralGroup.r 1 else DihedralGroup.sr 0) (FreeGroup.of v) = DihedralGroup.sr (0 : ZMod n)
      simp only [FreeGroup.lift.of, ite_eq_right_iff, imp_false]
      decide
    intro x hx
    have : (x = r ^ n) ∨ (x = s ^ 2) ∨ (x = s * r * s * r) := by
      unfold GeneratingRelforDihedral at hx
      simp only [if_false_right, and_true, if_true_left] at hx
      tauto
    rcases this with (h1 | h2 | h3)
    · rw [h1, map_pow]
      rw [lift_r, DihedralGroup.r_one_pow, DihedralGroup.one_def, CharP.cast_eq_zero]
    · rw [h2, map_pow]
      rw [lift_s, pow_two]
      show DihedralGroup.r (0 - 0) = 1
      rw [sub_zero, DihedralGroup.one_def]
    · rw [h3, map_mul, map_mul, map_mul, lift_s, lift_r, DihedralGroup.one_def, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r]
      rw [zero_add, zero_sub, add_left_neg]
  set f := fun x ↦ if x = u then DihedralGroup.r (1 : ZMod n) else DihedralGroup.sr (0 : ZMod n)
  let π1 : PresentedGroup (GeneratingRelforDihedral n) →* DihedralGroup n := (PresentedGroup.toGroup liftable)
  let r' : PresentedGroup (GeneratingRelforDihedral n) := Quot.mk _ r
  let s' : PresentedGroup (GeneratingRelforDihedral n) := Quot.mk _ s
  have helper {x : FreeGroup (Fin 2)} (h : x ∈ (GeneratingRelforDihedral n)) :
    ((Quot.mk _ x) : PresentedGroup (GeneratingRelforDihedral n)) = (Quot.mk _ 1) := by
    apply Quot.sound
    unfold Setoid.r QuotientGroup.leftRel MulAction.orbitRel MulAction.orbit
    simp? says simp only [Set.mem_range, Subtype.exists, Submonoid.mk_smul, MulOpposite.smul_eq_mul_unop, Subgroup.mem_op, exists_prop, one_mul]
    unfold MulOpposite.unop PreOpposite.unop'
    use .op' x
    simp? says simp only [and_true]
    exact (Subgroup.subset_normalClosure (s := GeneratingRelforDihedral n)) h
  have h1 : r' ^ n = 1 := by
    unfold_let r'
    show Quot.mk _ (r ^ n) = Quot.mk _ 1
    exact helper (rn_in_GenRel n)
  have h2 : s' ^ 2 = 1 := by
    unfold_let s'
    show Quot.mk _ (s ^ 2) = Quot.mk _ 1
    exact helper (s2_in_GenRel n)
  have h3 : s' * r' * s' * r' = 1 := by
    unfold_let r' s'
    show Quot.mk _ (s * r * s * r) = Quot.mk _ 1
    exact helper (srsr_in_GenRel n)
  have h5 (i j : ZMod n) : r' ^ i.val * r' ^ j.val = r' ^ (i + j).val := by
    repeat rw [← zpow_natCast]
    rw [← zpow_add]
    have : r' ^ ((i.val : ℤ) + j.val - (i + j).val) = 1 := by
      rw [← zpow_natCast] at h1
      rw [← orderOf_dvd_iff_zpow_eq_one (x := r') (i := n)] at h1
      rw [← orderOf_dvd_iff_zpow_eq_one (x := r') (i := (i.val : ℤ) + j.val - (i + j).val)]
      apply dvd_trans h1
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (↑(i + j).val) (↑i.val + ↑j.val) n).mp
      norm_cast
      simp? says simp only [ZMod.natCast_val, ZMod.cast_add', ZMod.cast_id', id_eq, Nat.cast_add]
    calc
    _ = r' ^ ((i.val : ℤ) + j.val - (i + j).val) *  r' ^ ((i + j).val : ℤ) := by
      rw [← zpow_add]
      congr 1
      abel
    _ = _ := by rw [this, one_mul]
  have h4_helper (i : ZMod n) : r' ^ (-i).val = (r'⁻¹) ^ i.val := by
    rw [inv_pow]
    have : r' ^ (-i).val * r' ^ i.val = 1 := by
      rw [h5 (-i) i, add_left_neg, ZMod.val_zero, pow_zero]
    calc
    _ = r' ^ (-i).val * r' ^ i.val * (r' ^ i.val)⁻¹ := by rw [mul_assoc, mul_right_inv, mul_one]
    _ = _ := by rw [this, one_mul]
  have h4 (i : ZMod n) : r' ^ i.val * s' = s' * r' ^ (-i).val := by
    have h11 : s' * r' ^ i.val * s'⁻¹ = (s' * r' * s'⁻¹) ^ i.val := by symm; apply conj_pow
    have h12 : s'⁻¹ = s' := by
      calc
      _ = s'⁻¹ * s' ^ 2 := by rw [h2, mul_one]
      _ = _ := by group
    have h13 : s' * r' * s' = r'⁻¹ := by
      calc
      _ = (s' * r' * s' * r') * r'⁻¹ := by group
      _ = _ := by rw [h3, one_mul]
    rw [h12, h13, ← h4_helper] at h11
    rw [← h11, ← mul_assoc, ← mul_assoc, ← pow_two, h2, one_mul]
  let π2 : DihedralGroup n →* PresentedGroup (GeneratingRelforDihedral n) := {
    toFun := fun x ↦ (
      match x with
      | .r i => r' ^ i.val
      | .sr i => s' * r' ^ i.val
    )
    map_one' := by
      have : (1 : DihedralGroup n) = .r 0 := rfl
      rw [this]
      simp? says simp only [ZMod.val_zero, pow_zero]
    map_mul' := fun x y ↦ (
      match x, y with
      | .r i, .r j => by
        simp? says simp only [DihedralGroup.r_mul_r]
        rw [h5 i j]
      | .r i, .sr j => by
        simp? says simp only [DihedralGroup.r_mul_sr]
        rw [← mul_assoc, h4 i, mul_assoc, h5 (-i) j, add_comm _ j, sub_eq_add_neg j i]
      | .sr i, .r j => by
        simp? says simp only [DihedralGroup.sr_mul_r]
        rw [mul_assoc, h5 i j]
      | .sr i, .sr j => by
        simp? says simp only [DihedralGroup.sr_mul_sr]
        rw [mul_assoc, ← mul_assoc _ s' _, h4 i, mul_assoc s' _ _, h5 (-i) j, ← mul_assoc, ← pow_two, h2, one_mul, add_comm _ j, sub_eq_add_neg j i]
    )
  }
  have h1 : π1 r' = .r 1 := by apply PresentedGroup.toGroup.of
  have h2 : π1 s' = .sr 0 := by apply PresentedGroup.toGroup.of
  apply π1.toMulEquiv π2
  · ext x
    simp? says simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply]
    have : x = u ∨ x = v := by
      unfold u v
      have : x.1 = 0 ∨ x.1 = 1 := by
        have := x.2
        omega
      rcases this with (h1 | h2)
      · left; ext; exact h1
      · right; ext; exact h2
    rcases this with (h1 | h2)
    · rw [h1]
      unfold_let π1 π2
      simp? says simp only [PresentedGroup.toGroup.of, ↓reduceIte, MonoidHom.coe_mk, OneHom.coe_mk]
      show r' ^ ZMod.val (1 : ZMod n) = r'
      rw [← pow_one r']
      congr 1
      refine ZMod.val_one n
    · rw [h2]
      unfold_let π1 π2
      have : v ≠ u := by decide
      unfold_let f
      simp? [this] says simp only [PresentedGroup.toGroup.of, this, ↓reduceIte, MonoidHom.coe_mk, OneHom.coe_mk, ZMod.val_zero, pow_zero, mul_one]
      rfl
  · ext x
    simp? says simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply]
    match x with
    | .r i =>
      unfold_let π1 π2
      simp? says simp only [MonoidHom.coe_mk, OneHom.coe_mk, map_pow]
      have : DihedralGroup.r i = (DihedralGroup.r 1) ^ i.val := by
        rw [DihedralGroup.r_one_pow]
        congr 1
        simp? says simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
      rw [this]
      congr 1
    | .sr i =>
      unfold_let π1 π2
      simp? says simp only [MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_pow]
      have : DihedralGroup.sr i = (DihedralGroup.sr 0) * (DihedralGroup.r 1) ^ i.val := by
        rw [DihedralGroup.r_one_pow]
        simp? says simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, DihedralGroup.sr_mul_r,zero_add]
      rw [this]
      congr
