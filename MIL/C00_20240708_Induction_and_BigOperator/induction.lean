import MIL.common

/--
 -  Inductive types
 -  Intuitively, an inductive type is built up from a specified list of constructors. In Lean, the syntax for specifying such a type is as follows:
 -  inductive Foo where
      | constructor₁ : ... → Foo
      | constructor₂ : ... → Foo
      ...
      | constructorₙ : ... → Foo
--/

-- examples of an inductive type
inductive Bool' where
  | True : Bool'
  | False : Bool'

inductive Nat' where
  | zero : Nat'
  | succ (k : Nat') : Nat'

-- example of recursive functions
-- define factorics for natural numbers
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

-- to prove factorics are always positive with induction
example (n : ℕ) : 0 < fac n := by
  induction n with
  | zero =>
    rw [fac]; linarith
  | succ k hk =>
    rw [fac]
    exact Nat.succ_mul_pos k hk

-- to prove factorics are always positive with induction'
example (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · exact Nat.zero_lt_succ 0
  · rw [fac]
    exact Nat.succ_mul_pos n ih

-- practice induction' with
example (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  induction' n with n ih
  · show 2 ^ (0 - 1) ≤ 1
    norm_num
  · rw [add_tsub_cancel_right]
    cases' n with m
    · show 2 ^ 0 ≤ 1 * 1
      norm_num
    · rw [add_tsub_cancel_right] at ih
      rw [pow_succ']
      show 2 * 2 ^ m ≤ (m + 2) * fac (m + 1)
      exact mul_le_mul (by omega) ih (by exact Nat.zero_le (2 ^ m)) (by exact Nat.zero_le (m + 2))

-- to get a proof of mul_left_cancel
example (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction' b with d hd generalizing c
  · rw [mul_zero] at h
    have := mul_eq_zero.mp h.symm
    tauto
  -- · induction' c with e _
  --   · rw [mul_zero] at h
  --     have := mul_eq_zero.mp h
  --     tauto
  --   · repeat rw [mul_add] at h
  --     rw [mul_one] at h
  --     have g := add_right_cancel h
  --     have := hd e g
  --     rw [this]
  · cases' c with e
    · rw [mul_zero] at h
      have := mul_eq_zero.mp h
      tauto
    · repeat rw [mul_add] at h
      rw [mul_one] at h
      let g := add_right_cancel h
      let h' := hd e g
      rw [h']

-- practice generalizing
noncomputable section
open Classical Set Function
variable {α β : Type*} [Nonempty β] (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

/--
 -  sbAux 0 = A \ g(B)
 -  sbAux 1 = g(f(sbAux 0)) = g(f(A \ g(B)))
 -  sbAux 2 = g(f(sbAux 1)) = g(f(...))
--/

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := sorry

theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        sorry
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    sorry
  push_neg  at xA
  sorry

end

variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

#check Finset.induction

example {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  -- induction s using Finset.induction with
  -- | empty =>
  --     simp
  -- | @insert i s _ hs =>
  --     rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
  --     set K := ⨅ j ∈ s, J j
  --     calc
  --       1 = I + K                  := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
  --       _ = I + K * (I + J i)      := by rw [hf i (Finset.mem_insert_self i s), mul_one]
  --       _ = (1 + K) * I + K * J i  := by ring
  --       _ ≤ I + K ⊓ J i            := by gcongr ; apply mul_le_left ; apply mul_le_inf
  induction' s using Finset.induction with i s _ hs
  · simp
  · rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
    set K := ⨅ j ∈ s, J j
    calc
      1 = I + K                  := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
      _ = I + K * (I + J i)      := by rw [hf i (Finset.mem_insert_self i s), mul_one]
      _ = (1 + K) * I + K * J i  := by ring
      _ ≤ I + K ⊓ J i            := by gcongr ; apply mul_le_left ; apply mul_le_inf


-- practice induction' using with
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases' m with m1
  · exact False.elim (h0 rfl)
  · cases' m1 with m2
    exact False.elim (((add_zero 1) ▸ h1) rfl)
    · rw [add_assoc, ((by norm_num) : 1 + 1 = 2)]
      exact Nat.le_add_left 2 m2

#check Nat.strong_induction_on
example {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  induction' n using Nat.strong_induction_on with n hn
  by_cases h1 : n.Prime
  · exact ⟨n, ⟨h1, dvd_refl n⟩⟩
  · have := Nat.exists_dvd_of_not_prime2 (n:=n) h h1
    obtain ⟨m, ⟨h1, h2, h3⟩⟩ := this
    obtain ⟨p, ⟨hp, h4⟩⟩ := hn m h3 h2
    exact ⟨p, ⟨hp, dvd_trans h4 h1⟩⟩

#check Set
#check Quotient
