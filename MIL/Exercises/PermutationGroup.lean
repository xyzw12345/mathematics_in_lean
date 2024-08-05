import Mathlib

namespace MyPermutationGroup

scoped notation "S " n:60 => Equiv.Perm (Fin n)

scoped notation "A " n:60 => alternatingGroup (Fin n)

set_option maxHeartbeats 3000000

#eval Equiv.Perm.cycleType (⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩ : Equiv.Perm (Fin 3))
#check Group.exists_list_of_mem_closure
#check Equiv.Perm.IsThreeCycle.alternating_normalClosure
#check Equiv.swap
#check Equiv.Perm.support_conj
#check Equiv.Perm.viaEmbeddingHom
#check IsConj.normalClosure_eq_top_of
#check Subgroup.subgroupOf

-- lemma alternating_group_center_trivial (n : ℕ) (h : n ≥ 5) : Subgroup.center (A n) = ⊥ := by
--   letI : OfNat (Fin n) 0 := {ofNat := ⟨0, lt_of_lt_of_le (show 0 < 5 from by decide) h⟩}
--   letI : OfNat (Fin n) 1 := {ofNat := ⟨1, lt_of_lt_of_le (show 1 < 5 from by decide) h⟩}
--   letI : OfNat (Fin n) 2 := {ofNat := ⟨2, lt_of_lt_of_le (show 2 < 5 from by decide) h⟩}
--   letI : OfNat (Fin n) 3 := {ofNat := ⟨3, lt_of_lt_of_le (show 3 < 5 from by decide) h⟩}
--   letI : OfNat (Fin n) 4 := {ofNat := ⟨4, lt_of_lt_of_le (show 4 < 5 from by decide) h⟩}
--   apply (Subgroup.eq_bot_iff_forall (Subgroup.center (A n))).mpr
--   intro τ ht
--   rw [Subgroup.mem_center_iff] at ht
--   have : ∀ (σ : (A n)), (σ.1.support).map τ.1.toEmbedding = σ.1.support := by
--     intro σ
--     rw [← Equiv.Perm.support_conj]
--     congr 1
--     norm_cast
--     rw [← ht σ, mul_assoc, mul_right_inv, mul_one]
--   suffices h : ∀ i : Fin n, ∃ u v : (A n), u.1.support ∩ v.1.support = {i} by
--     have : ∀ i : Fin n, τ.1 i = i := by
--       intro i
--       obtain ⟨u, v, huv⟩ := h i
--       have : Finset.map (Equiv.toEmbedding ↑τ) {i} = {i} := by
--         rw [← huv]
--         nth_rw 2 [← this u, ← this v]
--         apply Finset.map_inter
--       simp? at this says simp only [Finset.map_singleton, Equiv.coe_toEmbedding, Finset.singleton_inj] at this
--       exact this
--     apply Subtype.val_inj.mp
--     rw [Equiv.Perm.ext_iff]
--     simp? says simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
--     exact this
--   have h_transitive : ∀ i : Fin n, ∃ σ : A n, σ.1 0 = i := by
--     intro i
--     by_cases h' : i = (1 : Fin n)
--     · use ⟨(Equiv.swap (2 : Fin n) (1 : Fin n)) * ((Equiv.swap (2 : Fin n) (0 : Fin n))), by
--       apply Equiv.Perm.IsThreeCycle.mem_alternatingGroup
--       apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
--       <;> (rw [ne_eq, Fin.mk.injEq]; unfold OfNat.ofNat; unfold_let; dsimp; decide)
--       ⟩
--       exact id h'.symm
--     · use (⟨(Equiv.swap (1 : Fin n) i) * (Equiv.swap (1 : Fin n) (0 : Fin n)), by
--       apply Equiv.Perm.mem_alternatingGroup.mpr
--       rw [map_mul, Equiv.Perm.sign_swap, Equiv.Perm.sign_swap, mul_neg, mul_one, neg_neg]
--       · rw [ne_eq, Fin.mk.injEq]; unfold OfNat.ofNat; unfold_let; dsimp; decide
--       · exact fun h'' ↦ h' (h''.symm)⟩)
--       rfl
--   have h_0 : ∃ u v : (A n), u.1.support ∩ v.1.support = {0} := by
--     use ⟨(Equiv.swap (0 : Fin n) (1 : Fin n)) * ((Equiv.swap (0 : Fin n) (2 : Fin n))) , by
--       apply Equiv.Perm.IsThreeCycle.mem_alternatingGroup
--       apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
--       <;> (rw [ne_eq, Fin.mk.injEq]; unfold OfNat.ofNat; unfold_let; dsimp; decide)⟩
--     use ⟨(Equiv.swap (0 : Fin n) (3 : Fin n)) * Equiv.swap (0 : Fin n) (4 : Fin n) , by
--       apply Equiv.Perm.IsThreeCycle.mem_alternatingGroup
--       apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
--       <;> (rw [ne_eq, Fin.mk.injEq]; unfold OfNat.ofNat; unfold_let; dsimp; decide)⟩
--     have helper {α : Type} [DecidableEq α] [Fintype α] {x : α} {y : α} {z : α} (h : List.Nodup [x, y, z]) : Equiv.Perm.support (Equiv.swap y x * Equiv.swap y z) = {x, y, z} := Equiv.swap_comm x y ▸ Equiv.Perm.support_swap_mul_swap h
--     have h1 : List.Nodup [(1 : Fin n),(0 : Fin n), (2 : Fin n)] := by
--       unfold OfNat.ofNat; unfold_let;
--       simp? says simp only [List.nodup_cons, List.mem_cons, Fin.mk.injEq, one_ne_zero, List.mem_singleton, OfNat.one_ne_ofNat, or_self, not_false_eq_true, OfNat.zero_ne_ofNat, List.not_mem_nil, List.nodup_nil, and_self]
--     have h2 : List.Nodup [(3 : Fin n), (0 : Fin n), (4 : Fin n)] := by
--       unfold OfNat.ofNat; unfold_let;
--       simp? says simp only [List.nodup_cons, List.mem_cons, Fin.mk.injEq, OfNat.ofNat_ne_zero, List.mem_singleton, Nat.reduceEqDiff, or_self, not_false_eq_true, OfNat.zero_ne_ofNat, List.not_mem_nil, List.nodup_nil, and_self]
--     rw [helper h1, helper h2]
--     exact rfl
--   intro i
--   obtain ⟨u₀, v₀, h₀⟩ := h_0
--   obtain ⟨σ, h⟩ := h_transitive i
--   use (σ * u₀ * σ⁻¹), (σ * v₀ * σ⁻¹)
--   push_cast
--   rw [Equiv.Perm.support_conj, Equiv.Perm.support_conj, ← Finset.map_inter, h₀]
--   simp? says simp only [Finset.map_singleton, Equiv.coe_toEmbedding, Finset.singleton_inj]
--   exact h

lemma centralizer_closure {G : Type*} [Group G] (s : Set G) : Subgroup.centralizer s = Subgroup.centralizer (Subgroup.closure s) := by
  apply le_antisymm
  · intro x hx'
    rw [Subgroup.mem_centralizer_iff] at *
    intro h hx
    apply Subgroup.closure_induction (k := s) (p := fun y ↦ (y * x = x * y)) hx hx' (by rw [one_mul, mul_one])
    · intro a b ha hb
      rw [← mul_assoc, ← ha, mul_assoc a b x, hb, mul_assoc]
    · intro a ha
      apply_fun (fun y ↦ a⁻¹ * y * a⁻¹) at ha
      rw [← mul_assoc a⁻¹ a x, mul_left_inv, one_mul, mul_assoc a⁻¹ (x * a) _, mul_assoc x _ _, mul_right_inv, mul_one] at ha
      exact ha.symm
  · apply Subgroup.centralizer_le
    exact Subgroup.subset_closure

lemma closure_singleton {G : Type*} [Group G] {s : G} : s ∈ Subgroup.normalClosure {s} := by
  have : {s} ⊆ (Subgroup.normalClosure {s} : Set G) := by exact Subgroup.subset_normalClosure
  simp? at this says simp only [Set.singleton_subset_iff, SetLike.mem_coe] at this
  exact this

lemma closure_singleton' {G : Type*} [Group G] (H : Subgroup G) [hH : H.Normal] (s : G) (h : s ∈ H) (h' : Subgroup.normalClosure {s} = ⊤) : H = ⊤ := by
  rw [← top_le_iff] at h' ⊢
  apply le_trans h'
  rw [← Subgroup.normalClosure_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  exact h

lemma closure_eq_top_of_support_card_le_5 (n : ℕ) (h : n ≥ 5) : ∀ τ : A n, τ ≠ 1 → τ.1.support.card ≤ 5 → (Subgroup.normalClosure {τ} = ⊤) := by
  letI : OfNat (Fin n) 0 := {ofNat := ⟨0, lt_of_lt_of_le (show 0 < 5 from by decide) h⟩}
  letI : OfNat (Fin n) 1 := {ofNat := ⟨1, lt_of_lt_of_le (show 1 < 5 from by decide) h⟩}
  letI : OfNat (Fin n) 2 := {ofNat := ⟨2, lt_of_lt_of_le (show 2 < 5 from by decide) h⟩}
  letI : OfNat (Fin n) 3 := {ofNat := ⟨3, lt_of_lt_of_le (show 3 < 5 from by decide) h⟩}
  letI : OfNat (Fin n) 4 := {ofNat := ⟨4, lt_of_lt_of_le (show 4 < 5 from by decide) h⟩}
  let F : S 5 →* S n := (Equiv.Perm.viaEmbeddingHom ⟨fun (x : Fin 5) ↦ ⟨x.1, lt_of_lt_of_le x.2 h⟩, by
    sorry⟩)
  let A5_img : Subgroup (A n) := Subgroup.subgroupOf (Subgroup.map F (A 5)) (A n)
  let iso_A5_img : (A 5) ≃* A5_img := by
    have h1 : Subgroup.subgroupOf (Subgroup.map F (A 5)) (A n) ≃* Subgroup.map F (A 5) := by
      apply Subgroup.subgroupOfEquivOfLe
      unfold_let F
      intro x ⟨s, ⟨hs, heq⟩⟩
      show Equiv.Perm.sign x = 1
      sorry
    have h2 : Subgroup.map F (A 5) ≃* (A 5) := by
      apply ((A 5).equivMapOfInjective F _).symm
      unfold_let F
      apply Equiv.Perm.viaEmbeddingHom_injective
    exact MulEquiv.trans h2.symm h1.symm
  have A5_img_simple : IsSimpleGroup A5_img := by
    letI : Nontrivial A5_img := by
      apply Equiv.nontrivial (β := (A 5))
      exact iso_A5_img.1.symm
    apply IsSimpleGroup.isSimpleGroup_of_surjective (G := A 5) (H := A5_img) iso_A5_img
    exact EquivLike.surjective iso_A5_img
  have closure_three_cycle_eq_top : ∀ τ : A n, τ.1.IsThreeCycle → (Subgroup.normalClosure {τ} = ⊤) := by
    intro t ht
    apply Equiv.Perm.IsThreeCycle.alternating_normalClosure
    · rw [Fintype.card_fin]; exact h
    · exact ht
  have exist_conj_in_A5_img : ∀ τ : A n, τ.1.support.card ≤ 5 → (∃ σ : A n, σ * τ * σ⁻¹ ∈ A5_img) := by sorry
  intro τ h1 h2
  obtain ⟨σ, hs⟩ := exist_conj_in_A5_img τ h2
  apply IsConj.normalClosure_eq_top_of (N := A n) (g := (σ * τ * σ⁻¹).1) (g' := τ.1)  (hg := (σ * τ * σ⁻¹).2) (hg' := τ.2) (show IsConj (σ * τ * σ⁻¹).1 τ.1 from by
    rw [isConj_iff]; use σ.1⁻¹; dsimp; group)
  set τ := σ * τ * σ⁻¹
  show Subgroup.normalClosure {τ} = ⊤
  have : τ ≠ 1 := by
    unfold_let τ; simp? says simp only [ne_eq, conj_eq_one_iff]; exact h1
  set K := Subgroup.normalClosure {τ}
  have hK' := Subgroup.Normal.subgroupOf (H := K) (K := A5_img)
    (show K.Normal from by
      unfold_let K; exact Subgroup.normalClosure_normal)
  set K' := Subgroup.subgroupOf K A5_img
  have h' : K' = ⊤ := by
    have h' := A5_img_simple.2 K' hK'
    have : K' ≠ ⊥ := by
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      use ⟨⟨τ, hs⟩, by
        unfold_let K'; apply Subgroup.mem_subgroupOf.mpr
        unfold_let K; show τ ∈ Subgroup.normalClosure {τ}
        have := Subgroup.subset_normalClosure (s := {τ})
        simp? at this says simp only [Set.singleton_subset_iff, SetLike.mem_coe] at this; exact this⟩
      simp? says simp only [ne_eq, Submonoid.mk_eq_one]
      exact this
    simp? [this] at h' says simp only [this, false_or] at h'
    exact h'
  let φ : A n := ⟨Equiv.swap 1 2 * Equiv.swap 1 3, by
    apply Equiv.Perm.IsThreeCycle.mem_alternatingGroup
    apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
    <;> (rw [ne_eq, Fin.mk.injEq]; unfold OfNat.ofNat; unfold_let; dsimp; decide)⟩
  have : φ ∈ A5_img := by
    sorry
    -- unfold_let A5_img
    -- show (Equiv.swap (1 : Fin n) (2 : Fin n) * Equiv.swap (1 : Fin n) (3 : Fin n)).support ⊆ ({0, 1, 2, 3, 4} : Finset (Fin n))
    -- have : (Equiv.swap (1 : Fin n) (2 : Fin n) * Equiv.swap (1 : Fin n) (3 : Fin n)).support = {2, 1, 3} := by
    --   rw [Equiv.swap_comm 1 2]
    --   have : [(2 : Fin n), (1 : Fin n), (3 : Fin n)].Nodup := by
    --     simp? says simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, and_true]
    --     rw [Fin.mk.injEq, Fin.mk.injEq, Fin.mk.injEq]
    --     unfold OfNat.ofNat; unfold_let; dsimp; decide
    --   exact Equiv.Perm.support_swap_mul_swap this
    -- rw [this]
    -- intro x
    -- simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
    -- tauto
  have : φ ∈ K := by
    have : ⟨φ, this⟩ ∈ K' := by rw [h']; trivial
    unfold_let K' at this
    exact (Subgroup.mem_subgroupOf (H := K) (K := A5_img)).mp this
  have phi_three_cycle : φ.1.IsThreeCycle := by
    unfold_let φ
    apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
    <;> (rw [ne_eq, Fin.mk.injEq]; unfold OfNat.ofNat; unfold_let; dsimp; decide)
  apply closure_singleton' _ φ this (closure_three_cycle_eq_top φ phi_three_cycle)

-- lemma support_mul_subs_union_support {α : Type*} [Fintype α] [DecidableEq α] (f g : Equiv.Perm α) : (f * g).support ⊆ f.support ∪ g.support := by
--   intro x
--   contrapose!
--   simp? says simp only [Finset.mem_union, Equiv.Perm.mem_support, ne_eq, not_or, Decidable.not_not, Equiv.Perm.coe_mul, Function.comp_apply, and_imp]
--   exact (fun h1 h2 ↦ (by rw [h2, h1]))

/- Probably can be shortened -/
-- lemma is_swap_mul_swap_same_of_IsThreeCycle {α : Type*} [Fintype α] [DecidableEq α] (f : Equiv.Perm α) (h : f.IsThreeCycle) : ∃ x y z : α, [x, y, z].Nodup ∧ f = Equiv.swap x y * Equiv.swap y z := by
  -- rw [← card_support_eq_three_iff, Finset.card_eq_three] at h
  -- obtain ⟨a, b, c, hab, hac, hbc, heq⟩ := h
  -- have hfa : f a ∈ ({b, c} : Finset α) := by
  --   have h1 : f a ≠ a := by
  --     have : a ∈ f.support := by rw [heq]; simp
  --     simp? at this says simp only [Equiv.Perm.mem_support, ne_eq] at this
  --     exact this
  --   have h2 : f a ∈ ({a, b, c} : Finset α) := by
  --     rw [← heq]; simp? says simp only [Equiv.Perm.mem_support, ne_eq, EmbeddingLike.apply_eq_iff_eq]; exact h1
  --   simp? at h2 says simp only [Finset.mem_insert, Finset.mem_singleton] at h2
  --   simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
  --   tauto
  -- have hfb : f b ∈ ({c, a} : Finset α) := by
  --   have h1 : f b ≠ b := by
  --     have : b ∈ f.support := by rw [heq]; simp
  --     simp? at this says simp only [Equiv.Perm.mem_support, ne_eq] at this
  --     exact this
  --   have h2 : f b ∈ ({a, b, c} : Finset α) := by
  --     rw [← heq]; simp? says simp only [Equiv.Perm.mem_support, ne_eq, EmbeddingLike.apply_eq_iff_eq]; exact h1
  --   simp? at h2 says simp only [Finset.mem_insert, Finset.mem_singleton] at h2
  --   simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
  --   tauto
  -- have hfc : f c ∈ ({a, b} : Finset α) := by
  --   have h1 : f c ≠ c := by
  --     have : c ∈ f.support := by rw [heq]; simp
  --     simp? at this says simp only [Equiv.Perm.mem_support, ne_eq] at this
  --     exact this
  --   have h2 : f c ∈ ({a, b, c} : Finset α) := by
  --     rw [← heq]; simp? says simp only [Equiv.Perm.mem_support, ne_eq, EmbeddingLike.apply_eq_iff_eq]; exact h1
  --   simp? at h2 says simp only [Finset.mem_insert, Finset.mem_singleton] at h2
  --   simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
  --   tauto
  -- have hfab : f a ≠ f b := by
  --   intro h; change f.toFun a = f.toFun b at h; apply_fun f.2 at h; rw [f.3, f.3] at h; exact hab h
  -- have hfbc : f b ≠ f c := by
  --   intro h; change f.toFun b = f.toFun c at h; apply_fun f.2 at h; rw [f.3, f.3] at h; exact hbc h
  -- have hfca : f c ≠ f a := by
  --   intro h; change f.toFun c = f.toFun a at h; apply_fun f.2 at h; rw [f.3, f.3] at h; exact hac h.symm
  -- simp only [Finset.mem_insert, Finset.mem_singleton] at hfa hfb hfc
  -- rcases hfa with (h1 | h1)
  -- · have h3 : f c = a := by rw [h1] at hfca; simp only [hfca, or_false] at hfc; exact hfc;
  --   have h2 : f b = c := by rw [h3] at hfbc; simp only [hfbc, or_false] at hfb; exact hfb;
  --   use a, b, c
  --   have hndp : [a, b, c].Nodup := by
  --     unfold List.Nodup
  --     simp? says simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil, false_implies, implies_true, List.Pairwise.nil, and_self, and_true]
  --     exact ⟨⟨hab, hac⟩, hbc⟩
  --   constructor
  --   · exact hndp
  --   · have : (Equiv.swap a b * Equiv.swap b c).support = {a, b, c} := Equiv.Perm.support_swap_mul_swap hndp
  --     apply Equiv.Perm.support_congr
  --     · rw [this, heq]
  --     · rw [this]
  --       intro x xs
  --       simp only [Finset.mem_insert, Finset.mem_singleton] at xs
  --       rcases xs with (h' | h' | h')
  --       · rw [h']; simp? says simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  --         rw [h1, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
  --       · rw [h']; simp? says simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  --         rw [h2, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  --       · rw [h']; simp? says simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  --         rw [h3, Equiv.swap_apply_right, Equiv.swap_apply_right]
  -- · have h2 : f b = a := by rw [h1] at hfab; simp only [hfab.symm, false_or] at hfb; exact hfb;
  --   have h3 : f c = b := by rw [h2] at hfbc; simp only [hfbc.symm, false_or] at hfc; exact hfc;
  --   use a, c, b
  --   have hndp : [a, c, b].Nodup := by
  --     unfold List.Nodup
  --     simp? says simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil, false_implies, implies_true, List.Pairwise.nil, and_self, and_true]
  --     exact ⟨⟨hac, hab⟩, hbc.symm⟩
  --   constructor
  --   · exact hndp
  --   · have : (Equiv.swap a c * Equiv.swap c b).support = {a, b, c} := by
  --       rw [Equiv.Perm.support_swap_mul_swap hndp]; ext x
  --       simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  --     apply Equiv.Perm.support_congr
  --     · rw [this, heq]
  --     · rw [this]
  --       intro x xs
  --       simp only [Finset.mem_insert, Finset.mem_singleton] at xs
  --       rcases xs with (h' | h' | h')
  --       · rw [h']; simp? says simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  --         rw [h1, Equiv.swap_apply_of_ne_of_ne hac hab, Equiv.swap_apply_left]
  --       · rw [h']; simp? says simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  --         rw [h2, Equiv.swap_apply_right, Equiv.swap_apply_right]
  --       · rw [h']; simp? says simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  --         rw [h3, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab.symm hbc]

-- lemma helper_1 {α : Type*} (x y z a b c : α) [Fintype α] [DecidableEq α] : {y, z, a} ⊆ ({a, b, c, x, y, z} : Finset α) := by
--   intro s xs
--   simp? at xs says simp only [Finset.mem_insert, Finset.mem_singleton] at xs
--   simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
--   tauto

-- lemma helper_2 {α : Type*} (x y z a b c : α) [Fintype α] [DecidableEq α] : {x, y, z} ⊆ ({a, b, c, x, y, z} : Finset α) := by
--   intro s xs
--   simp? at xs says simp only [Finset.mem_insert, Finset.mem_singleton] at xs
--   simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
--   tauto

-- lemma helper_3 {α : Type*} (x y z a b c : α) [Fintype α] [DecidableEq α] : {a, b, c} ⊆ ({a, b, c, x, y, z} : Finset α) := by
--   intro s xs
--   simp? at xs says simp only [Finset.mem_insert, Finset.mem_singleton] at xs
--   simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
--   tauto

-- lemma helper_4 {α : Type*} (x y z : α) [Fintype α] [DecidableEq α] : {x, y, z} = ({y, x, z} : Finset α) := by
--   ext s
--   simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
--   tauto

-- lemma helper_5 {α : Type*} (x y z : α) [Fintype α] [DecidableEq α] : {x, y, z} = ({z, x, y} : Finset α) := by
--   ext s
--   simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
--   tauto

-- lemma exist_commutator_support_card_le_5 {n : ℕ} (f : A n) (g : A n) (hf : f.1.IsThreeCycle) (hg : g.1.IsThreeCycle) (hninter : f.1.support ∩ g.1.support = ∅) : ∃ φ : A n, (φ * (f * g) * φ⁻¹ * (f * g)⁻¹) ≠ 1 ∧ (φ * (f * g) * φ⁻¹ * (f * g)⁻¹).1.support.card ≤ 5 := by
--   obtain ⟨x, y, z, hxyz, heq1⟩ := is_swap_mul_swap_same_of_IsThreeCycle f.1 hf -- (x y z)
--   obtain ⟨a, b, c, habc, heq2⟩ := is_swap_mul_swap_same_of_IsThreeCycle g.1 hg-- (a b c)
--   have h_support_1 : f.1.support = {x, y, z} := by rw [heq1]; exact Equiv.Perm.support_swap_mul_swap hxyz
--   have h_support_2 : g.1.support = {a, b, c} := by rw [heq2]; exact Equiv.Perm.support_swap_mul_swap habc
--   rw [h_support_1, h_support_2] at hninter
--   have a_ne_x : a ≠ x := by intro h; absurd hninter; rw [h]; simp
--   have a_ne_y : a ≠ y := by intro h; absurd hninter; rw [h]; simp
--   have a_ne_z : a ≠ z := by intro h; absurd hninter; rw [h]; simp
--   have b_ne_y : b ≠ y := by intro h; absurd hninter; rw [h]; rw [helper_4 x y z]; simp
--   have b_ne_z : b ≠ z := by intro h; absurd hninter; rw [h]; rw [helper_5 x y z]; simp
--   have b_ne_a : b ≠ a := by intro h; absurd habc; rw [h]; simp
--   have c_ne_x : c ≠ x := by intro h; absurd hninter; rw [h]; simp
--   have c_ne_y : c ≠ y := by intro h; absurd hninter; rw [h]; rw [helper_4 x y z]; simp
--   have c_ne_z : c ≠ z := by intro h; absurd hninter; rw [h]; rw [helper_5 x y z]; simp
--   have c_ne_a : c ≠ a := by intro h; absurd habc; rw [h]; simp
--   have c_ne_b : c ≠ b := by intro h; absurd habc; rw [h]; simp
--   have z_ne_y : z ≠ y := by intro h; absurd hxyz; rw [h]; simp
--   let φ : A n := ⟨Equiv.swap y z * Equiv.swap z a, by
--     rw [Equiv.swap_comm y z]
--     apply Equiv.Perm.IsThreeCycle.mem_alternatingGroup
--     apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
--     · exact z_ne_y
--     · symm; exact a_ne_z
--     · symm; exact a_ne_y⟩
--   -- (y z a) (x y z) (a b c) (y a z) (a c b) (x z y) = (a y z b x)
--   use φ
--   set ψ : A n := φ * (f * g) * φ⁻¹ * (f * g)⁻¹
--   have h00 : [y, z, a].Nodup := by
--     unfold List.Nodup
--     simp? says simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil, false_implies, implies_true, List.Pairwise.nil, and_self, and_true]
--     exact ⟨⟨z_ne_y.symm, a_ne_y.symm⟩, a_ne_z.symm⟩
--   have h0 : φ.1.support ⊆ {a, b, c, x, y, z} := by
--     have : φ.1.support = {y, z, a} := Equiv.Perm.support_swap_mul_swap h00
--     rw [this]
--     exact helper_1 x y z a b c
--   have h0' : f.1.support ⊆ {a, b, c, x, y, z} := by
--     rw [h_support_1]
--     exact helper_2 x y z a b c
--   have h0'' : g.1.support ⊆ {a, b, c, x, y, z} := by
--     rw [h_support_2]
--     exact helper_3 x y z a b c
--   have h1 : ψ.1.support ⊆ {a, b, c, x, y, z} := by
--     apply subset_trans (support_mul_subs_union_support _ _); apply Finset.union_subset
--     apply subset_trans (support_mul_subs_union_support _ _); apply Finset.union_subset
--     apply subset_trans (support_mul_subs_union_support _ _); apply Finset.union_subset
--     · exact h0
--     · apply subset_trans (support_mul_subs_union_support _ _);
--       exact Finset.union_subset h0' h0''
--     · show φ.1⁻¹.support ⊆ {a, b, c, x, y, z}; rw [Equiv.Perm.support_inv]; exact h0
--     · show ((f * g).1⁻¹).support ⊆ {a, b, c, x, y, z}; rw [Equiv.Perm.support_inv];
--       apply subset_trans (support_mul_subs_union_support _ _);
--       exact Finset.union_subset h0' h0''
--   have h2 : ψ.1 a = y := by
--     unfold_let ψ φ
--     simp? [heq1, heq2] says simp only [mul_inv_rev, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, heq1, heq2, InvMemClass.coe_inv, Equiv.swap_inv, Equiv.Perm.coe_mul, Function.comp_apply]
--     rw [show (Equiv.swap x y) a = a from (Equiv.swap_apply_of_ne_of_ne a_ne_x a_ne_y)]
--     rw [show (Equiv.swap y z) a = a from (Equiv.swap_apply_of_ne_of_ne a_ne_y a_ne_z)]
--     rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
--     rw [show (Equiv.swap y z) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_y c_ne_z)]
--     rw [show (Equiv.swap z a) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_z c_ne_a)]
--     rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
--     rw [show (Equiv.swap y z) a = a from (Equiv.swap_apply_of_ne_of_ne a_ne_y a_ne_z)]
--     rw [show (Equiv.swap x y) a = a from (Equiv.swap_apply_of_ne_of_ne a_ne_x a_ne_y)]
--     rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
--   have h3 : c ∉ ψ.1.support := by
--     simp? says simp only [Equiv.Perm.mem_support, ne_eq, Decidable.not_not]
--     unfold_let ψ φ
--     simp? [heq1, heq2] says simp only [mul_inv_rev, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, heq1, heq2, InvMemClass.coe_inv, Equiv.swap_inv, Equiv.Perm.coe_mul, Function.comp_apply]
--     rw [show (Equiv.swap x y) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_x c_ne_y)]
--     rw [show (Equiv.swap y z) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_y c_ne_z)]
--     rw [show (Equiv.swap a b) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_a c_ne_b)]
--     rw [Equiv.swap_apply_right]
--     rw [show (Equiv.swap y z) b = b from (Equiv.swap_apply_of_ne_of_ne b_ne_y b_ne_z)]
--     rw [show (Equiv.swap z a) b = b from (Equiv.swap_apply_of_ne_of_ne b_ne_z b_ne_a)]
--     rw [Equiv.swap_apply_left]
--     rw [show (Equiv.swap a b) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_a c_ne_b)]
--     rw [show (Equiv.swap y z) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_y c_ne_z)]
--     rw [show (Equiv.swap x y) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_x c_ne_y)]
--     rw [show (Equiv.swap z a) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_z c_ne_a)]
--     rw [show (Equiv.swap y z) c = c from (Equiv.swap_apply_of_ne_of_ne c_ne_y c_ne_z)]
--   have h4 : ψ.1.support ⊆ {a, b, x, y, z} := by
--     intro s xs
--     have : s = a ∨ s = b ∨ s = c ∨ s = x ∨ s = y ∨ s = z := by
--       have := h1 xs
--       simp? says simp only [Finset.mem_insert, Finset.mem_singleton] at this
--       exact this
--     have : ¬ s = c := fun h ↦ (h.symm ▸ h3) xs
--     simp? says simp only [Finset.mem_insert, Finset.mem_singleton]
--     tauto
--   constructor
--   · intro h
--     rw [h] at h2
--     change a = y at h2
--     rw [h2] at hninter
--     absurd hninter
--     simp? says simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, Finset.inter_insert_of_mem, Finset.insert_ne_empty, not_false_eq_true]
--   · apply le_trans (Finset.card_le_card h4)
--     exact Finset.card_le_five

-- lemma closure_three_cycles_eq_top {α : Type*} [Fintype α] [DecidableEq α] :
--   Subgroup.closure {f : alternatingGroup α | f.1.IsThreeCycle} = ⊤ := by
--     apply eq_top_iff.2
--     have hi : Function.Injective (alternatingGroup α).subtype := Subtype.coe_injective
--     refine' eq_top_iff.1 (Subgroup.map_injective hi (le_antisymm (Subgroup.map_mono le_top) _))
--     have h1 : Subgroup.map (alternatingGroup α).subtype ⊤ = (alternatingGroup α) := by
--       ext x
--       simp? says simp only [Subgroup.mem_map, Subgroup.mem_top, Subgroup.coeSubtype, true_and, Subtype.exists, Equiv.Perm.mem_alternatingGroup, exists_prop, exists_eq_right]
--     have h2 : Subgroup.map (alternatingGroup α).subtype (Subgroup.closure {f | f.1.IsThreeCycle}) = (Subgroup.closure {f : Equiv.Perm α | f.IsThreeCycle}) := by
--       convert MonoidHom.map_closure (alternatingGroup α).subtype {f | f.1.IsThreeCycle}
--       ext x
--       simp? says simp only [Set.mem_setOf_eq, Subgroup.coeSubtype, Set.mem_image, Subtype.exists, Equiv.Perm.mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right, iff_self_and]
--       exact fun a ↦ Equiv.Perm.IsThreeCycle.sign a
--     rw [h1, h2]
--     simp? says simp only [Equiv.Perm.closure_three_cycles_eq_alternating, le_refl]

-- theorem alternating_group_isSimple (n : ℕ) (h : n ≥ 5) : IsSimpleGroup (A n) := by
--   apply IsSimpleGroup.mk (toNontrivial := alternatingGroup.nontrivial_of_three_le_card ( by rw [Fintype.card_fin]; exact le_trans (show 3 ≤ 5 from by decide) h))
--   letI : OfNat (Fin n) 0 := {ofNat := ⟨0, lt_of_lt_of_le (show 0 < 5 from by decide) h⟩}
--   letI : OfNat (Fin n) 1 := {ofNat := ⟨1, lt_of_lt_of_le (show 1 < 5 from by decide) h⟩}
--   letI : OfNat (Fin n) 2 := {ofNat := ⟨2, lt_of_lt_of_le (show 2 < 5 from by decide) h⟩}
--   letI : OfNat (Fin n) 3 := {ofNat := ⟨3, lt_of_lt_of_le (show 3 < 5 from by decide) h⟩}
--   letI : OfNat (Fin n) 4 := {ofNat := ⟨4, lt_of_lt_of_le (show 4 < 5 from by decide) h⟩}
--   intro H hH
--   by_cases h : ∃ g : H, g ≠ 1
--   · right
--     obtain ⟨⟨σ, hsh⟩, hne⟩ := h
--     simp? at hg says simp only [ne_eq, Submonoid.mk_eq_one] at hne
--     suffices h_closure_eq_top : ∀ τ : A n, τ ≠ 1 → (Subgroup.normalClosure {τ} = ⊤) by
--       specialize h_closure_eq_top σ hne
--       apply closure_singleton' _ _ hsh h_closure_eq_top
--     intro τ ht
--     set H : Subgroup (A n) := Subgroup.normalClosure {τ}
--     have hH : H.Normal := by exact Subgroup.normalClosure_normal
--     have exist_prod_three_cycle_elem : ∃ g : A n, (g ∈ H) ∧ (g ≠ 1) ∧ (∃ f1 f2 : A n, f1.1.IsThreeCycle ∧ f2.1.IsThreeCycle ∧ g = f1 * f2) := by
--       by_contra h
--       push_neg at h
--       have : ∀ h : H, ∀ f : A n, f.1.IsThreeCycle → f * h.1 * f⁻¹ * h.1⁻¹ = 1 := by
--         intro h1 f hf
--         have h1' : (f * h1.1 * f⁻¹ * h1.1⁻¹) ∈ H := by
--           rw [show (f * h1.1 * f⁻¹ * h1.1⁻¹) = (f * h1.1 * f⁻¹) * h1.1⁻¹ from by group]
--           exact H.mul_mem' (hH.conj_mem h1.1 h1.2 f) (H.inv_mem' h1.2)
--         have h2 : (f * h1.1 * f⁻¹ * h1.1⁻¹) = f * (h1.1 * f⁻¹ * h1.1⁻¹) := by group
--         have h3 : (h1.1 * f⁻¹ * h1.1⁻¹).1.IsThreeCycle := by
--           rw [← card_support_eq_three_iff]
--           simp? says simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, InvMemClass.coe_inv, Equiv.Perm.support_conj, Equiv.Perm.support_inv, Finset.card_map]
--           rw [card_support_eq_three_iff]
--           exact hf
--         by_cases h4 : (f * h1.1 * f⁻¹ * h1.1⁻¹) = 1
--         · exact h4
--         · specialize h (f * h1.1 * f⁻¹ * h1.1⁻¹) h1' h4 f (h1.1 * f⁻¹ * h1.1⁻¹) hf h3 h2
--           contradiction
--       have : H ≤ Subgroup.centralizer {f : A n | f.1.IsThreeCycle} := by
--         intro x xh
--         rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
--         intro f hf
--         exact this ⟨x, xh⟩ f hf
--       rw [centralizer_closure {f : A n | f.1.IsThreeCycle}] at this
--       have h : Subgroup.closure {f : A n | f.1.IsThreeCycle} = ⊤ := by
--         apply closure_three_cycles_eq_top
--       rw [h] at this
--       have h : Subgroup.centralizer (⊤ : Subgroup (A n)) = Subgroup.center (A n) := by apply Subgroup.centralizer_univ
--       rw [h, alternating_group_center_trivial n (by assumption), le_bot_iff, (Subgroup.eq_bot_iff_forall H)] at this
--       have h : τ ∈ H := by apply closure_singleton
--       exact ht (this τ h)
--     obtain ⟨g, hgH, hne1, ⟨f1, f2, hf1, hf2, heq⟩⟩ := exist_prod_three_cycle_elem
--     have : g.1.support ⊆ f1.1.support ∪ f2.1.support := by
--       intro x
--       contrapose!
--       simp? [heq] says simp only [Finset.mem_union, Equiv.Perm.mem_support, ne_eq, not_or, Decidable.not_not, heq, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Equiv.Perm.coe_mul, Function.comp_apply, and_imp]
--       exact (fun h1 h2 ↦ (by rw [h2, h1]))
--     by_cases h_empty_inter : f1.1.support ∩ f2.1.support = ∅
--     · obtain ⟨g', hne1, hle1⟩ := exist_commutator_support_card_le_5 f1 f2 hf1 hf2 h_empty_inter
--       rw [← heq] at hle1 hne1
--       let g'' : A n := g' * g * g'⁻¹ * g⁻¹
--       have hg'' : g'' ∈ H := by
--         unfold_let g''
--         rw [show (g' * g * g'⁻¹ * g⁻¹) = (g' * g * g'⁻¹) * g⁻¹ from by group]
--         exact H.mul_mem' (hH.conj_mem g hgH g') (H.inv_mem hgH)
--       have : g''.1.support.card ≤ 5 := hle1
--       have h_gne1 : g'' ≠ 1 := hne1
--       exact closure_singleton' H g'' hg'' (closure_eq_top_of_support_card_le_5 n h g'' h_gne1 this)
--     · have : g.1.support.card ≤ 5 := by
--         apply le_trans (Finset.card_le_card this)
--         have : (f1.1.support ∪ f2.1.support).card = f1.1.support.card + f2.1.support.card - (f1.1.support ∩ f2.1.support).card := by exact Finset.card_union f1.1.support f2.1.support
--         rw [this, card_support_eq_three_iff.mpr hf1, card_support_eq_three_iff.mpr hf2]
--         have h5 : (f1.1.support ∩ f2.1.support).card ≥ 1 := by
--           by_contra h
--           simp? at h says simp only [ge_iff_le, not_le, Nat.lt_one_iff, Finset.card_eq_zero] at h
--           exact (h_empty_inter h)
--         simp? says simp only [Nat.reduceAdd, tsub_le_iff_right, ge_iff_le]
--         rw [show 6 = 5 + 1 from by decide]
--         exact Nat.add_le_add_left h5 5
--       exact closure_singleton' H g hgH (closure_eq_top_of_support_card_le_5 n h g hne1 this)
--   · left
--     push_neg at h
--     apply (Subgroup.eq_bot_iff_forall H).mpr
--     exact fun x hx ↦ (by
--       have := h ⟨x, hx⟩
--       simp? at this says simp only [Submonoid.mk_eq_one] at this
--       exact this)
