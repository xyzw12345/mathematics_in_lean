import Mathlib

/-
If $I, J$ are ideals of $R$, let $I J$ be the set of all sums of elements of the form $i j$, where $i \in I, j \in J$. Prove that $I J$ is an ideal of $R$.

Proof:
1. To Prove that $I J$ is and ideal of $R$, we have to first define the underlying set to be the set of all sums of elements of the form $i j$, where $i \in I, j \in J$. So that we can then proceed to prove that it satisfies all the properties an ideal has to possess, i.e. $I J$ is closed under addition, $0 \in I J$ and $\forall c \in R, a \in I J$, we have $c a \in I J$.
2. First we prove that $I J$ is closed under addition. Suppose $a = \displaystyle \sum_{(i, j) \in T_a} i * j$, $b = \displaystyle \sum_{(i, j) \in T_b} i * j$, where $T_a, T_b$ are multisets whose elements belongs to $I \prod J$, then we will have $a + b = \displaystyle \sum_{(i, j) \in (T_a \uplus T_b)} i * j$, which yields that $a + b \in I J$.
3. Then we know that $0 \in I J$, since $0$ is simply the result of an empty sum.
4. Finally, we prove that $\forall c \in R, a \in I$, we have $c a \in I$. Suppose $a = \displaystyle \sum_{(i, j) \in T_a} i * j$, if we take $T_b = \{(c i, j) | (i, j) \in T_a\}$, then $c a = c (\displaystyle \sum_{(i, j) \in T_a} i * j) = \displaystyle \sum_{(i, j) \in T_a} c * (i * j) = \displaystyle \sum_{(i, j) \in T_a} (c * i) * j = \displaystyle \sum_{(i, j) \in T_b} i * j$, and therefore $c a \in I J$.


-/
variable {R : Type*} [Ring R]

def Product_ideal (I : Ideal R) (J : Ideal R) : Ideal R where
  -- To Prove that $I J$ is and ideal of $R$, we have to first define the underlying set to be the set of all sums of elements of the form $i j$, where $i \in I, j \in J$. So that we can then proceed to prove that it satisfies all the properties an ideal has to possess, i.e. $I J$ is closed under addition, $0 \in I J$ and $\forall c \in R, a \in I J$, we have $c a \in I J$.
  carrier := {x | ∃ T : Multiset (I × J), x = Multiset.sum (Multiset.map (fun (t : I × J) ↦ (t.1 : R) * (t.2 : R)) T)}
  -- First we prove that $I J$ is closed under addition. Suppose $a = \displaystyle \sum_{(i, j) \in T_a} i * j$, $b = \displaystyle \sum_{(i, j) \in T_b} i * j$, where $T_a, T_b$ are multisets whose elements belongs to $I \prod J$, then we will have $a + b = \displaystyle \sum_{(i, j) \in (T_a \uplus T_b)} i * j$, which yields that $a + b \in I J$.
  add_mem' {a b} ha hb := by
    rcases ha with ⟨Ta, hTa⟩
    rcases hb with ⟨Tb, hTb⟩
    use Ta + Tb
    rw [Multiset.map_add, Multiset.sum_add, hTa, hTb]
  -- Then we know that $0 \in I J$, since $0$ is simply the result of an empty sum.
  zero_mem' := by
    use 0
    simp only [Multiset.map_zero, Multiset.sum_zero]
  -- Finally, we prove that $\forall c \in R, a \in I$, we have $c a \in I$. Suppose $a = \displaystyle \sum_{(i, j) \in T_a} i * j$, if we take $T_b = \{(c i, j) | (i, j) \in T_a\}$, then $c a = c (\displaystyle \sum_{(i, j) \in T_a} i * j) = \displaystyle \sum_{(i, j) \in T_a} c * (i * j) = \displaystyle \sum_{(i, j) \in T_a} (c * i) * j = \displaystyle \sum_{(i, j) \in T_b} i * j$, and therefore $c a \in I J$.
  smul_mem' c {a} ha := by
    rcases ha with ⟨Ta, hTa⟩
    use Multiset.map (fun t ↦ (⟨c * t.1.1, I.smul_mem' c t.1.2⟩, t.2)) Ta
    calc
    _ = c * Multiset.sum (Multiset.map (fun (t : I × J) ↦ (t.1 : R) * (t.2 : R)) Ta) := by rw [hTa, smul_eq_mul]
    _ = Multiset.sum (Multiset.map (fun (t : I × J) ↦ c * ((t.1 : R) * (t.2 : R))) Ta) := by exact Multiset.sum_map_mul_left.symm
    _ = Multiset.sum (Multiset.map (fun (t : I × J) ↦ (c * t.1 : R) * (t.2 : R)) Ta) := by
      congr
      ext t
      exact Eq.symm (mul_assoc c t.1.1 t.2.1)
    _ = Multiset.sum (Multiset.map (fun (t : I × J) ↦ (t.1 : R) * (t.2 : R)) (Multiset.map (fun t ↦ (⟨c * t.1.1, I.smul_mem' c t.1.2⟩, t.2)) Ta)) := by
      simp only [Multiset.map_map, Function.comp_apply]
