import Init.Core
import Mathlib.Init.Quot
import Mathlib.Init.Set
import Mathlib.Data.Finset.Basic

-- Untyped Lambda Calculus

inductive lambda_terms (α : Type) :=
  | Variable (u : α) : lambda_terms α
  | Application (M : lambda_terms α) (N : lambda_terms α) : lambda_terms α
  | Abstraction (u : α) (M : lambda_terms α) : lambda_terms α
deriving DecidableEq
#check instDecidableEqLambda_terms

open lambda_terms

#check Variable.injEq
#check Application.injEq
#check Abstraction.injEq
#check DecidableEq

variable {α : Type} [inst : DecidableEq α]

-- def my_decidable (M1 N1 : lambda_terms α) : Decidable (M1 = N1) :=
--   match M1, N1 with
--   | Variable u, Variable v => if h : u = v then Decidable.isTrue (h ▸ rfl) else Decidable.isFalse (fun x ↦ h (Variable.inj x))
--   | Variable u, Application M N => Decidable.isFalse (by simp only [not_false_eq_true])
--   | Variable u, Abstraction v M => Decidable.isFalse (by simp only [not_false_eq_true])
--   | Application M N, Variable v => Decidable.isFalse (by simp only [not_false_eq_true])
--   | Application M N, Application M' N' =>
--     match my_decidable M M' with
--     | Decidable.isTrue h =>
--       match my_decidable N N' with
--       | Decidable.isTrue h' => Decidable.isTrue (h ▸ h' ▸ rfl)
--       | Decidable.isFalse h' => Decidable.isFalse (fun h1 ↦ h' (Application.inj h1).2)
--     | Decidable.isFalse h => Decidable.isFalse (fun h1 ↦ h (Application.inj h1).1)
--   | Application M N, Abstraction v M' => Decidable.isFalse (by simp only [not_false_eq_true])
--   | Abstraction u M, Variable v => Decidable.isFalse (by simp only [not_false_eq_true])
--   | Abstraction u M, Application M' N' => Decidable.isFalse (by simp only [not_false_eq_true])
--   | Abstraction u M, Abstraction v M' =>
--     match inst u v with
--     | Decidable.isTrue h =>
--       match my_decidable M M' with
--       | Decidable.isTrue h' => Decidable.isTrue (h ▸ h' ▸ rfl)
--       | Decidable.isFalse h' => Decidable.isFalse (fun h1 ↦ h' (Abstraction.inj h1).2)
--     | Decidable.isFalse h => Decidable.isFalse (fun h1 ↦ h (Abstraction.inj h1).1)

-- instance : DecidableEq (lambda_terms α) := fun M N ↦ my_decidable M N

def Free_Variables (M : lambda_terms α) : Finset α :=
  match M with
  | Variable u => {u}
  | Application M N => (Free_Variables M) ∪ (Free_Variables N)
  | Abstraction u M => (Free_Variables M) \ {u}

def Binding_Variables (M : lambda_terms α) : Finset α :=
  match M with
  | Variable _ => ∅
  | Application M N => (Binding_Variables M) ∪ (Binding_Variables N)
  | Abstraction u M => (Binding_Variables M) ∪ {u}

-- Suppose that x is not a binding variable in M
def Renaming (x y : α) (M : lambda_terms α) : lambda_terms α :=
  match M with
  | Variable u => if u = x then Variable y else Variable u
  | Application M N => Application (Renaming x y M) (Renaming x y N)
  | Abstraction u M => Abstraction u (Renaming x y M)

notation:60 M:60 "⟦" x:60 " → " y:60 "⟧" => Renaming x y M
notation:60 "FV" M:60  => Free_Variables M
notation:60 "BV" M:60  => Binding_Variables M

def Replacable (x : α) (M : lambda_terms α) : Prop := (x ∉ FV M)

def alpha_equiv : lambda_terms α → lambda_terms α → Prop := fun M1 ↦ ( fun N1 ↦ (
  match M1, N1 with
  | Variable u, Variable v => u = v
  | Variable _, Application _ _ => False
  | Variable _, Abstraction _ _ => False
  | Application _ _, Variable _ => False
  | Application M N, Application M' N' => (alpha_equiv M M') ∧ (alpha_equiv N N')
  | Application _ _, Abstraction _ _ => False
  | Abstraction _ _, Variable _ => False
  | Abstraction _ _, Application _ _ => False
  | Abstraction u M, Abstraction v M' => if u = v then alpha_equiv M M' else (Replacable v M) ∧ (M' = M⟦u → v⟧)))

notation:50 M:50 "=[α]" N:50 => alpha_equiv M N

instance {M N : lambda_terms α} : Decidable (M =[α] N) := sorry

#check Setoid
#check Equivalence
#check alpha_equiv

def equiv : Equivalence (alpha_equiv (α := α)) where
  refl := sorry
  symm := sorry
  trans := sorry

class FinsetChoosable (α : Type*) where
  choose : Finset α → α
  choose_spec : ∀ (S : Finset α), choose S ∉ S

variable [inst1 : FinsetChoosable α]


def Substitution (x : α) (N : lambda_terms α) (M : lambda_terms α) : lambda_terms α :=
  let inst' : FinsetChoosable α := inferInstance
  match M with
  | Variable u => if u = x then N else Variable u
  | Application P Q => Application (Substitution x N P) (Substitution x N Q)
  | Abstraction u M =>
    let z := inst'.choose ((BV M) ∪ (FV M) ∪ (FV N))
    Abstraction z (Substitution x N M⟦u → z⟧)

notation:50 M:50"⟦"x:50 "→[β]" N:50 "⟧" => Substitution x N M

lemma alpha_invariant_subst (x : α) {M₁ M₂ N₁ N₂ : lambda_terms α} (h₁ : M₁ =[α] M₂) (h₂ : N₁ =[α] N₂) : (M₁⟦x →[β] N₁⟧) = (M₂⟦x →[β] N₂⟧) := sorry
