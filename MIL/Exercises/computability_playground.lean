import Mathlib

def V : Subgroup (Equiv.Perm (Fin 4)) := {
  carrier := {1, c[1, 2] * c[3, 4], c[1, 3] * c[2, 4], c[1, 4] * c[2, 3]}
  mul_mem' := by simp; decide
  one_mem' := by simp;
  inv_mem' := by simp; decide
}

set_option trace.Meta.synthInstance true in
#eval decide (@Fintype.card V (by unfold V; infer_instance) = 4)
lemma card_v : @Fintype.card V (by unfold V; infer_instance) = 4 := by exact of_decide_eq_true (Eq.refl true)

def fin_1 : Fintype V := by unfold V; infer_instance

open Classical in
set_option trace.Meta.synthInstance true in
noncomputable def fin_2 : Fintype V := by unfold V; infer_instance

open Classical in
set_option trace.Meta.synthInstance true in
-- #eval decide (@Fintype.card V (by unfold V; infer_instance) = 4)

example : @Fintype.card V (by unfold V; infer_instance) = 4 := by
  rw [show @Fintype.card V fin_2 = @Fintype.card V fin_1 from by apply @Fintype.card_congr' V V fin_2 fin_1 rfl]
  exact card_v
