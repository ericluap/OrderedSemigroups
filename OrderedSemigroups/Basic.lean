import Mathlib.Algebra.Group.PNatPowAssoc
import OrderedSemigroups.Defs

/-!
# Exponentiation Theorems

This file proves basic facts about exponentiation and how it interacts
with the ordering on a semigroup.

-/

universe u

variable {α : Type u}

section Semigroup
variable [Semigroup α] [Pow α ℕ+] [PNatPowAssoc α]

theorem ppow_succ (n : ℕ+) (x : α) : x ^ (n + 1) = x ^ n * x := by
  simp [ppow_add]

theorem ppow_comm (n : ℕ+) (x : α) : x^n * x = x * x^n := by
  induction n with
  | one => simp
  | succ n ih =>
    simp [ppow_succ, ih, mul_assoc]

theorem ppow_succ' (n : ℕ+) (x : α) : x ^ (n + 1) = x * x^n := by
  rw [ppow_succ, ppow_comm]

theorem ppow_two (x : α) : x ^ (2 : ℕ+) = x * x := by
  have : (2 : ℕ+) = 1 + 1 := by decide
  simp [this, ppow_succ]

omit [Semigroup α] [Pow α ℕ+] [PNatPowAssoc α] in
theorem nppow_eq_nppowRec [Monoid α] [Pow α ℕ+] [PNatPowAssoc α]
    (x : α) (n : ℕ+) : Pow.pow x n = npowRec n.val x := by
  induction n with
  | one =>
    change x ^ (1 : ℕ+) = _
    simp [npowRec]
  | succ n ih =>
    change x ^ (n + 1) = _
    change x ^ n = _ at ih
    simp [pow_add, ppow_add, ih, npowRec]

/-
theorem nppow_eq_pow (n : ℕ+) (x : α) : Semigroup'.nppow n x = x ^ n := rfl

@[simp]
theorem ppow_one (x : α) : x ^ (1 : ℕ+) = x := Semigroup'.nppow_one x


theorem ppow_comm (n : ℕ+) (x : α) : x^n * x = x * x^n := by
  induction n with
  | one => simp
  | succ n ih =>
    simp [ppow_succ, ih, mul_assoc]

theorem ppow_succ' (n : ℕ+) (x : α) : x ^ (n + 1) = x * x^n := by
  rw [ppow_succ, ppow_comm]

theorem ppow_add (a : α) (m n : ℕ+) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | one => simp [ppow_succ]
  | succ n ih => rw [ppow_succ, ←mul_assoc, ←ih, ←ppow_succ]; exact rfl


theorem ppow_mul (a : α) (m : ℕ+) : ∀ n, a ^ (m * n) = (a ^ m) ^ n := by
  intro n
  induction n with
  | one => simp
  | succ n ih =>
    calc
      a ^ (m * (n + 1)) = a ^ (m * n + m)     := rfl
      _                 = a ^ (m * n) * a ^ m := ppow_add a (m * n) m
      _                 = (a ^ m) ^ n * a ^ m := congrFun (congrArg HMul.hMul ih) (a ^ m)
      _                 = (a ^ m) ^ (n + 1)   := Eq.symm (ppow_succ n (a ^ m))
-/

theorem split_first_and_last_factor_of_product {a b : α} {n : ℕ+} :
  (a*b)^(n+1) = a*(b*a)^n*b := by
  induction n with
  | one => simp [ppow_succ, mul_assoc]
  | succ n ih =>
    calc
      (a * b)^(n + 1 + 1) = (a*b)^(n+1) * (a*b) := by rw [ppow_succ]
      _                   = a * (b*a)^n * b * (a*b) := by simp [ih]
      _                   = a * ((b*a)^n * (b*a)) * b := by simp [mul_assoc]
      _                   = a * (b*a)^(n+1) * b := by rw [←ppow_succ]

theorem mul_pow_comm_semigroup (is_comm : ∀x y : α, x * y = y * x)
    (a b : α) (n : ℕ+) : (a*b)^n = a^n * b^n := by
  induction n with
  | one => simp
  | succ n ih =>
    simp [ppow_succ, ih]
    calc a ^ n * b ^ n * (a * b)
    _ = a ^ n * (b ^ n * a) * b := by simp [mul_assoc]
    _ = a ^ n * (a * b ^ n) * b := by simp [is_comm]
    _ = a ^ n * a * (b ^ n * b) := by simp [mul_assoc]
end Semigroup

section OrderedSemigroup
variable [Semigroup α] [PartialOrder α] [IsOrderedSemigroup α]
  [Pow α ℕ+] [PNatPowAssoc α]

theorem le_pow {a b : α} (h : a ≤ b) (n : ℕ+) : a^n ≤ b^n := by
  induction n with
  | one =>
    simpa
  | succ n ih =>
    simp [ppow_succ]
    exact mul_le_mul' ih h

omit [Pow α ℕ+] [PNatPowAssoc α] in
theorem middle_swap {a b c d : α} (h : a ≤ b) : c * a * d ≤ c * b * d := by
  have : a * d ≤ b * d := IsRightOrderedSemigroup.mul_le_mul_right a b h d
  have : c * (a * d) ≤ c * (b * d) :=
    IsLeftOrderedSemigroup.mul_le_mul_left (a*d) (b*d) this c
  simp only [mul_assoc]
  trivial

theorem comm_factor_le {a b : α} (h : a*b ≤ b*a) (n : ℕ+) : a^n * b^n ≤ (a*b)^n := by
  induction n with
  | one => simp
  | succ n ih =>
    calc
      a^(n+1) * b^(n+1) = a * (a^n * b^n) * b := by simp [ppow_succ, ppow_comm, mul_assoc]
      _                 ≤ a * (a * b)^n * b := middle_swap ih
      _                 ≤ a * (b * a)^n * b := middle_swap (le_pow h n)
      _                 = (a * b)^(n+1) := by rw [←split_first_and_last_factor_of_product]

theorem comm_swap_le {a b : α} (h : a*b ≤ b*a) (n : ℕ+) : (a*b)^n ≤ (b*a)^n := le_pow h n

theorem comm_dist_le {a b : α} (h : a*b ≤ b*a) (n : ℕ+) : (b*a)^n ≤ b^n * a^n := by
  induction n with
  | one => simp
  | succ n ih =>
    calc
      (b*a)^(n+1) = b * (a*b)^n * a := by rw [split_first_and_last_factor_of_product]
      _           ≤ b * (b*a)^n * a := middle_swap (le_pow h n)
      _           ≤ b * (b^n * a^n) * a := middle_swap ih
      _           = (b * b^n) * (a^n * a) := by simp [mul_assoc]
      _           = b^(n+1) * a^(n+1) := by simp [ppow_succ, ←ppow_succ']

end OrderedSemigroup

section OrderedCancelSemigroup
variable [Semigroup α] [PartialOrder α] [IsOrderedCancelSemigroup α]
  [Pow α ℕ+] [PNatPowAssoc α]

theorem lt_pow {a b : α} (h : a < b) (n : ℕ+) : a^n < b^n := by
  induction n with
  | one => simpa
  | succ n ih =>
    simp [ppow_succ]
    exact Left.mul_lt_mul ih h

theorem comm_swap_lt {a b : α} (h : a*b < b*a) (n : ℕ+) : (a*b)^n < (b*a)^n := lt_pow h n

end OrderedCancelSemigroup
