import Mathlib

set_option profiler true

open BigOperators

def List.FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : Finset α :=
  match L with
  | [] => ∅
  | x :: [] => A x
  | x1 :: x2 :: xs => A x1 ∩ List.FinInter A (x2 :: xs)

def List.FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : Finset α :=
  match L with
  | [] => ∅
  | x :: xs => A x ∪ (xs.FinUnion A)

lemma List.eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) (h : L ≠ []) : ∀ x : α, x ∈ L.FinInter A ↔ ∀ i ∈ L, x ∈ A i :=
  match L with
  | [] => (by absurd h; rfl)
  | x :: [] => (by
    unfold List.FinInter
    simp? says simp only [mem_singleton, forall_eq, implies_true])
  | x1 :: x2 :: xs => (by
    unfold List.FinInter
    simp? says simp only [Finset.mem_inter, mem_cons, forall_eq_or_imp, and_congr_right_iff]
    intro x _
    have := List.eq_FinInter A (x2 :: xs) (by simp? says simp only [ne_eq, not_false_eq_true])
    specialize this x
    rw [this]
    simp? says simp only [mem_cons, forall_eq_or_imp]
    )

lemma List.eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : ∀ x : α, x ∈ L.FinUnion A ↔ ∃ i ∈ L, x ∈ A i :=
  match L with
  | [] => (by
    intro x
    unfold List.FinUnion
    simp? says simp only [Finset.not_mem_empty, not_mem_nil, false_and, exists_false])
  | y :: ys => (by
    intro x
    unfold List.FinUnion
    simp? says simp only [Finset.mem_union, mem_cons, exists_eq_or_imp]
    rw [ys.eq_FinUnion A x])

def Multiset.FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Multiset β → Finset α :=
  Quot.lift (α := List β) (List.FinInter A) (by
    intro a b hab
    unfold Setoid.r List.isSetoid at hab
    ext x
    by_cases h : a = []
    · simp? [h] at hab says simp only [h, List.nil_perm] at hab
      rw [h, hab]
    · have : b ≠ [] := by
        intro h
        simp? [h] at hab says simp only [h, List.perm_nil] at hab
        contradiction
      rw [List.eq_FinInter A a h, List.eq_FinInter A b this]
      change a.Perm b at hab
      simp_rw [List.Perm.mem_iff hab]
    )

def Multiset.FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Multiset β → Finset α :=
  Quot.lift (α := List β) (List.FinUnion A) (by
    intro a b hab
    unfold Setoid.r List.isSetoid at hab
    ext x
    rw [List.eq_FinUnion, List.eq_FinUnion]
    change a.Perm b at hab
    simp_rw [List.Perm.mem_iff hab]
  )

lemma Multiset.eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (M : Multiset β) (h : M ≠ ∅) : ∀ x : α, x ∈ M.FinInter A ↔ ∀ m ∈ M, x ∈ A m := by
  intro x
  have : x ∈ M.FinInter A ↔ x ∈ M.toList.FinInter A := by
    have : M.FinInter A = M.toList.FinInter A := by
      have : M.toList = M := by
        simp? says simp only [coe_toList]
      unfold Multiset.FinInter
      rw [← this]
      apply Finset.val_inj.mp
      set f := List.FinInter A with hf
      set L := M.toList
      simp_rw [← hf]
      simp? says simp only [lift_coe, Finset.val_inj]
      congr 1
      rw [this]
    rw [this]
  rw [this]
  rw [List.eq_FinInter]
  · simp? says simp only [mem_toList]
  · simp? at h says simp only [empty_eq_zero, ne_eq] at h
    simp? says simp only [ne_eq, toList_eq_nil]
    exact h

lemma Multiset.eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (M : Multiset β) : ∀ x : α, x ∈ M.FinUnion A ↔ ∃ m ∈ M, x ∈ A m := by
  intro x
  have : M.FinUnion A = M.toList.FinUnion A := by
    have : M.toList = M := by
      simp? says simp only [coe_toList]
    unfold Multiset.FinUnion
    rw [← this]
    apply Finset.val_inj.mp
    set f := List.FinUnion A with hf
    set L := M.toList
    simp_rw [← hf]
    simp? says simp only [lift_coe, Finset.val_inj]
    congr 1
    rw [this]
  rw [this]
  rw [List.eq_FinUnion]
  simp? says simp only [mem_toList]

def FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) : Finset α := Multiset.FinInter A (Finset.univ).1

def FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Finset α := Multiset.FinUnion A (Finset.univ).1

lemma eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [h : Nonempty β] (A : β → Finset α) :
  FinInter A = ⋂ (i : β), (A i : Set α) := by
  unfold FinInter
  ext x
  simp? says simp only [Finset.mem_coe, Set.mem_iInter]
  rw [Multiset.eq_FinInter]
  simp? says simp only [Finset.mem_val, Finset.mem_univ, true_implies]
  simp? says simp only [Multiset.empty_eq_zero, ne_eq, Finset.val_eq_zero]
  apply Finset.nonempty_iff_ne_empty.mp
  exact Finset.univ_nonempty_iff.mpr h

lemma eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  FinUnion A = ⋃ (i : β), (A i : Set α) := by
  unfold FinUnion
  ext x
  simp? says simp only [Finset.mem_coe, Set.mem_iUnion]
  rw [Multiset.eq_FinUnion]
  simp? says simp only [Finset.mem_val, Finset.mem_univ, true_and]

instance FinInter_Fin {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) :
  Fintype (⋂ (i : β), (A i : Set α)) := by
  rw [← eq_FinInter]
  exact FinsetCoe.fintype (FinInter fun i ↦ A i)

instance FinUnion_Fin {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  Fintype (⋃ (i : β), (A i : Set α)) := by
  rw [← eq_FinUnion]
  exact FinsetCoe.fintype (FinUnion fun i ↦ A i)

def Finset.powerset₀ {α : Type*} (A : Finset α) : Finset (Finset α) :=
  Finset.filter (fun S ↦ (Fintype.card S ≠ 0)) A.powerset

instance powerset₀_nonempty {α : Type*} {A : Finset α} (S : A.powerset₀) : Nonempty S := by
  have : Fintype.card S.1 ≠ 0 := by
    unfold Finset.powerset₀ at *
    have : S.1 ∈ Finset.filter (fun S ↦ Fintype.card { x // x ∈ S } ≠ 0) A.powerset := S.2
    simp only [ne_eq, Fintype.card_coe, Finset.card_eq_zero, Finset.mem_filter,
      Finset.mem_powerset] at this
    simp only [ne_eq, Fintype.card_coe, Finset.card_eq_zero]
    exact this.2
  apply Finset.Nonempty.coe_sort
  simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero] at this
  exact Finset.nonempty_iff_ne_empty.mpr this

def toInt (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

lemma toInt_and {P Q : Prop} [Decidable P] [Decidable Q] : toInt (P ∧ Q) = toInt P * toInt Q := by
  unfold toInt
  by_cases h : P
  · by_cases h' : Q
    · simp only [h, h', and_self, ↓reduceIte, mul_one]
    · simp only [h, h', and_false, ↓reduceIte, mul_zero]
  · by_cases h' : Q
    · simp only [h, h', and_true, ↓reduceIte, mul_one]
    · simp only [h, h', and_self, ↓reduceIte, mul_zero]

lemma toInt_not (P : Prop) [Decidable P] : toInt (¬ P) = 1 - toInt P := by
  unfold toInt
  by_cases h : P
  · simp only [h, not_true_eq_false, ↓reduceIte, sub_self]
  · simp only [h, not_false_eq_true, ↓reduceIte, sub_zero]

def char_fun {α : Type*} [DecidableEq α] (A : Finset α) (x : α) : ℤ := toInt (x ∈ A)

lemma card_eq_sum_char_fun {α : Type*} [DecidableEq α] {A B : Finset α} (h : B ⊆ A) :
  Fintype.card B = Finset.sum A (char_fun B) := by
  have : Fintype.card B = ∑ _ : B, (1 : ℤ) := by
    trans ∑ _ : B, (1 : ℕ)
    norm_cast
    rw [Fintype.card_eq_sum_ones]
    norm_cast
  rw [this]
  unfold char_fun toInt
  simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one,Finset.sum_ite_mem, Nat.cast_inj]
  congr 1
  symm
  rw [Finset.inter_eq_right]
  exact h

lemma char_fun_inter {α : Type*} [DecidableEq α] (A B : Finset α) (x : α) :
  char_fun (A ∩ B) x = (char_fun A x) * (char_fun B x) := by
    show toInt (x ∈ (A ∩ B)) = toInt (x ∈ A) * toInt (x ∈ B)
    simp_rw [← Finset.mem_coe, Finset.coe_inter]
    rw [← toInt_and]; congr 1

lemma char_fun_union {α : Type*} [DecidableEq α] (A B : Finset α) (x : α) :
  char_fun (A ∪ B) x = 1 - (1 - char_fun A x) * (1 - char_fun B x) := by
    show toInt (x ∈ A ∪ B) = 1 - (1 - toInt (x ∈ A)) * (1 - toInt (x ∈ B))
    simp_rw [← Finset.mem_coe, Finset.coe_union]
    rw [← toInt_not, ← toInt_not, ← toInt_and, ← toInt_not]; congr 1
    simp only [Set.mem_union, Finset.mem_coe, not_and, Decidable.not_not, eq_iff_iff]
    tauto

lemma char_fun_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) (x : α) : char_fun (FinInter A) x = ∏ (i : β), (char_fun (A i) x) := by
  by_cases h : ∃ (i : β), char_fun (A i) x = 0
  · obtain ⟨y, hy⟩ := h
    have : ∏ i : β, char_fun (A i) x = 0 := by
      apply Finset.prod_eq_zero (a := y)
      · exact Finset.mem_univ y
      · rw [hy]
    rw [this]
    unfold char_fun toInt
    simp? says simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    rw [← Finset.mem_coe, eq_FinInter]
    simp? says simp only [Set.mem_iInter, Finset.mem_coe, not_forall]
    unfold char_fun toInt at hy
    simp? at hy says simp only [ite_eq_right_iff, one_ne_zero, imp_false] at hy
    exact ⟨y, hy⟩
  · unfold char_fun toInt at h
    simp? at h says
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_exists, Decidable.not_not] at h
    have h' : ∀ (y : β), char_fun (A y) x = 1 := by
      unfold char_fun toInt
      intro y
      simp? [h y] says simp only [h y, ↓reduceIte]
    simp_rw [h']
    simp? says simp only [Finset.prod_const_one]
    unfold char_fun toInt
    simp? says simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [← Finset.mem_coe, eq_FinInter]
    simp? says simp only [Set.mem_iInter, Finset.mem_coe]
    exact h

lemma char_fun_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (x : α) :
  char_fun (FinUnion A) x = 1 - ∏ (i : β), (1 - char_fun (A i) x) := by
  by_cases h : ∃ (i : β), char_fun (A i) x = 1
  · obtain ⟨y, hy⟩ := h
    have : ∏ i : β, (1 - char_fun (A i) x) = 0 := by
      apply Finset.prod_eq_zero (a := y)
      · exact Finset.mem_univ y
      · rw [hy, sub_self]
    rw [this, sub_zero]
    unfold char_fun toInt
    simp? says simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [← Finset.mem_coe, eq_FinUnion]
    simp? says simp only [Set.mem_iUnion, Finset.mem_coe]
    unfold char_fun toInt at hy
    simp? at hy says simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not] at hy
    exact ⟨y, hy⟩
  · unfold char_fun toInt at h
    simp? at h says
      simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not, not_exists] at h
    have h' : ∀ (y : β), char_fun (A y) x = 0 := by
      unfold char_fun toInt
      intro y
      simp? [h y] says simp only [h y, ↓reduceIte]
    simp_rw [h']
    simp? says simp only [sub_zero, Finset.prod_const_one, sub_self]
    unfold char_fun toInt
    simp? says simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    rw [← Finset.mem_coe, eq_FinUnion]
    simp? says simp only [Set.mem_iUnion, Finset.mem_coe, not_exists]
    exact h

lemma card_eq {α : Type*} (A : Finset α) (B : Set α) [Fintype B] (h : A = B) :
  Fintype.card B = Fintype.card A := by
  simp_rw [← h]
  simp only [Finset.coe_sort_coe, Fintype.card_coe]

lemma card_eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) :
  Fintype.card (⋂ (i : β), (A i : Set α)) = Fintype.card (FinInter A) := by
    exact card_eq _ _ (eq_FinInter A)

lemma card_eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  Fintype.card (⋃ (i : β), (A i : Set α)) = Fintype.card (FinUnion A) := by
    exact card_eq _ _ (eq_FinUnion A)

lemma mul_expand''' (n : ℕ) (g : ℕ → ℤ) : ∏ i ∈ Finset.range n, (1 - g i) = ∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S) * ∏ j : S, g j := by
  induction' n with n ih
  · simp? says
      simp only [Finset.range_zero, Finset.prod_empty, Finset.powerset_empty, Int.reduceNeg, Fintype.card_coe, Finset.univ_eq_attach, Finset.sum_singleton, Finset.card_empty, pow_zero, Finset.attach_empty, mul_one]
  · rw [Finset.prod_range_succ]
    have (n : ℕ) : (∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S) * ∏ j : S, g j) = Multiset.sum (Multiset.map (fun (S : Multiset ℕ) ↦ (-1) ^ (Fintype.card S) * Multiset.prod (Multiset.map g S)) (Multiset.range n).powerset) := by
      unfold Finset.powerset
      unfold Finset.sum
      simp
      congr 1
      apply Multiset.map_eq_map_of_bij_of_nodup
      · apply Multiset.Nodup.pmap
        · intro a b b1 hb1 heq
          show (@Finset.mk ℕ a b).val = (@Finset.mk ℕ b1 hb1).val
          rw [heq]
        · apply Multiset.Nodup.powerset
          exact Multiset.nodup_range n
      · apply Multiset.Nodup.powerset
        exact Multiset.nodup_range n
      pick_goal 5
      · use fun x _ ↦ x.1
      · intro a ha
        simp at ha
        obtain ⟨a1, ha1, heq⟩ := ha
        apply Multiset.mem_powerset.mpr
        rw [← heq]
        exact ha1
      · intro _ _ _ _ heq
        exact Finset.val_inj.mp heq
      · intro b hb
        simp at hb
        have : b.Nodup := by
          exact Multiset.nodup_of_le hb (Multiset.nodup_range n)
        use Finset.mk b this
        simp
        exact hb
      · intro a ha
        simp at ha
        obtain ⟨a1, ha1, heq⟩ := ha
        simp
        rw [← heq]
        apply Finset.prod_attach
    rw [this] at *
    simp only [Multiset.range_succ, Multiset.powerset_cons, Int.reduceNeg, Multiset.card_coe,
      Multiset.map_add, Multiset.map_map, Function.comp_apply, Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_add]
    simp only [Int.reduceNeg, Multiset.card_coe] at ih
    conv => {
    rhs
    congr
    · skip
    · congr
      · congr
        ext x
        · rw [← mul_assoc, pow_succ, mul_assoc _ (-1) _, mul_comm _ (-1 * g n), ← Int.neg_eq_neg_one_mul, mul_assoc]}
    conv => {
    rhs
    congr
    · skip
    · rw [Multiset.sum_map_mul_left]}
    rw [← ih, mul_sub, mul_one, neg_mul, sub_eq_add_neg, mul_comm]

lemma mul_expand'' (n : ℕ) (g : ℕ → ℤ) : 1 - ∏ i ∈ Finset.range n, (1 - g i) = ∑ S ∈ (Finset.range n).powerset₀, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j := by
  have : ∑ S ∈ (Finset.range n).powerset₀, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j = (∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) + 1 := by
    have : (fun (S : Finset ℕ) ↦ (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) = (fun (S : Finset ℕ) ↦ if S = ∅ then (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j else (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) := by
      simp? says
        simp only [Int.reduceNeg, Fintype.card_coe, Finset.univ_eq_attach, ite_self]
    nth_rw 2 [this]
    rw [Finset.sum_ite]
    unfold Finset.powerset₀
    simp? says
      simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero, Int.reduceNeg, Finset.univ_eq_attach]
    set u := ∑ x ∈ Finset.filter (fun S ↦ ¬S = ∅) (Finset.range n).powerset, (-1) ^ (x.card + 1) * ∏ j ∈ x.attach, g ↑j
    set v := ∑ x ∈ Finset.filter (fun S ↦ S = ∅) (Finset.range n).powerset, (-1) ^ (x.card + 1) * ∏ j ∈ x.attach, g ↑j with hv
    rw [add_comm v u, add_assoc]
    nth_rw 1 [← add_zero u]
    congr 1
    rw [hv]
    have : Finset.filter (fun S ↦ S = ∅) (Finset.range n).powerset = ({∅} : Finset (Finset ℕ)) := by
      ext S
      simp? says
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton, and_iff_right_iff_imp]
      intro h
      rw [h]
      exact Finset.empty_subset (Finset.range n)
    rw [this]
    simp? says
      simp only [Int.reduceNeg, Finset.sum_singleton, Finset.card_empty, zero_add, pow_one, Finset.attach_empty, Finset.prod_empty, mul_one, add_left_neg]
  rw [this, sub_eq_add_neg, Int.neg_eq_neg_one_mul, mul_expand''' n g, Finset.mul_sum, add_comm 1 _]
  congr 2
  ext S
  rw [← mul_assoc, pow_succ']

lemma mul_expand' (n : ℕ) (g : ℕ → ℤ) :
  1 - ∏ (i : Fin n), (1 - g i) =
    ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))),
      (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
  have hl : ∏ (i : Fin n), (1 - g i) = ∏ i in Finset.range n, (1 - g i) := by
    exact (Finset.prod_range fun i ↦ 1 - g i).symm
  have hr : ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) = ∑ (S : Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
    apply Finset.sum_bij
    pick_goal 5
    · intro a _
      use Finset.map ⟨fun (x : Fin n) ↦ x.1, by exact Fin.val_injective⟩ a.1
      unfold Finset.powerset₀ at *
      obtain ⟨a1, ha1⟩ := a
      simp? at ha1 says
        simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero, Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and] at ha1
      simp? [ha1] says
        simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero, Finset.mem_filter,Finset.mem_powerset, Finset.map_eq_empty, ha1, not_false_eq_true, and_true]
      intro x hx
      simp at hx
      obtain ⟨a2, ⟨_, ha2⟩⟩ := hx
      rw [← ha2]
      simp? says simp only [Finset.mem_range, Fin.is_lt]
    · simp? says simp only [Finset.univ_eq_attach, Finset.mem_attach, imp_self, implies_true]
    · intro _ _ _ _ heq
      simp? at heq says
        simp only [Subtype.mk.injEq, Finset.map_inj] at heq
      exact SetCoe.ext heq
    · simp? says
        simp only [Finset.univ_eq_attach, Finset.mem_attach, exists_true_left, Subtype.exists, true_implies, Subtype.forall, Subtype.mk.injEq, exists_prop]
      unfold Finset.powerset₀
      simp? says
        simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero, Finset.mem_filter, Finset.mem_powerset, Finset.powerset_univ, Finset.mem_univ, true_and, and_imp]
      intro a ha hnempa
      have : ∀ (x : ℕ), x ∈ a → x < n := by
        intro x hx
        have := ha hx
        simp? at this says simp only [Finset.mem_range] at this
        exact this
      let a' : Finset (Fin n) := a.attachFin (fun n' hn' ↦ this n' hn')
      use a'
      constructor
      · have : a'.card ≠ 0 := by
          unfold_let a'
          rw [Finset.card_attachFin]
          simp? says simp only [ne_eq, Finset.card_eq_zero]
          exact hnempa
        exact ne_of_apply_ne Finset.card this
      · ext x
        simp? says simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
        unfold_let a'
        constructor
        · rintro ⟨a1, ha1, heq⟩
          rw [← heq]
          simp?  at ha1 says simp only [Finset.mem_attachFin] at ha1
          exact ha1
        · intro hx
          use ⟨x, this x hx⟩
          simp? says simp only [Finset.mem_attachFin, and_true]
          exact hx
    · intro a ha
      simp? says
        simp only [Int.reduceNeg, Fintype.card_coe, Finset.univ_eq_attach, Finset.mem_map, Function.Embedding.coeFn_mk, ne_eq, eq_mp_eq_cast, id_eq, eq_mpr_eq_cast, Finset.card_map, mul_eq_mul_left_iff, add_eq_zero, Finset.card_eq_zero, one_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff, neg_eq_zero, or_false]
      rw [Finset.prod_attach]
      simp? says simp only [Finset.prod_map, Function.Embedding.coeFn_mk]
      rw [Finset.prod_attach a.1 (fun (x : Fin n) ↦ g x.val)]
  have hr' : ∑ (S : Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) = ∑ (S ∈ Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
    symm
    apply Finset.sum_subtype
    simp? says simp only [implies_true]
  rw [hl, hr, hr']
  exact mul_expand'' n g

lemma mul_expand (n : ℕ) (g : (Fin n) → ℤ) :
  1 - ∏ (i : Fin n), (1 - g i) =
    ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))),
      (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
        set g' : ℕ → ℤ := fun x ↦ if h : x < n then g ⟨x, h⟩ else 0
        have (x : Fin n) : g' x = g x := by
          show (fun x ↦ if h : x < n then g ⟨x, h⟩ else 0) x = g x
          simp? says simp only [Fin.is_lt, ↓reduceDite, Fin.eta]
        simp_rw [← this]
        exact mul_expand' n g'

theorem Principle_of_Inclusion_Exclusion {α : Type*} [DecidableEq α] (n : ℕ) (A : (Fin n) → Finset α) :
  (Fintype.card (⋃ (i : Fin n), ((A i) : Set α)))
    = Finset.sum
      (Finset.univ (α := (Finset.powerset₀ (Finset.univ (α := Fin n)))))
        (fun S ↦ (-1 : ℤ) ^ (Fintype.card S + 1) * Fintype.card (⋂ (i : S.1), ((A i) : Set α))) := by
  set U : Finset α := FinUnion A
  rw [card_eq_FinUnion]
  simp_rw [card_eq_FinInter]
  have hU1 : FinUnion A ⊆ U := by rfl
  have hU2 (S : (Finset.powerset₀ (Finset.univ (α := Fin n)))) :
    @FinInter α S _ _ _ (fun i ↦ A i) ⊆ U := by
    rw [← Finset.coe_subset, eq_FinInter, eq_FinUnion]
    intro x hx
    let s : S.1 := Classical.choice (by infer_instance)
    simp? says simp only [Set.mem_iInter, Finset.mem_coe, Subtype.forall] at hx
    simp? says simp only [Set.mem_iUnion, Finset.mem_coe]
    exact ⟨s.1, hx s.1 s.2⟩
  rw [card_eq_sum_char_fun hU1]
  conv => {
    rhs
    congr
    · skip
    · ext S
      rw [card_eq_sum_char_fun (hU2 S)]
      rw [Finset.mul_sum]}
  rw [Finset.sum_comm]
  congr 1
  ext x
  set g := fun (i : Fin n) ↦ char_fun (A i) x
  have hg (i : Fin n) : g i = char_fun (A i) x := rfl
  conv => {
    congr
    · rw [char_fun_FinUnion]
      congr
      · skip
      · congr
        · skip
        · ext i
          · rw [← hg i]
    · congr
      · skip
      · ext S
        rw [char_fun_FinInter]
        congr
        · skip
        · congr
          · skip
          · ext i
            · rw [← hg i]}
  apply mul_expand
