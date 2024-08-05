import Mathlib

#check WellFoundedRelation

def Mygcd (m n : ℕ) : ℕ :=
  if m = 0 then
    n
  else
    Mygcd (n % m) m
  termination_by m
  decreasing_by
    simp_wf
    apply Nat.mod_lt
    apply Nat.zero_lt_of_ne_zero
    assumption
