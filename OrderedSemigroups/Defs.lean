import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.PNat.Basic

/-!
# Ordered Semigroups

This file defines ordered semigroups and provides some basic instances.
It also defines the action of `ℕ+` on a semigroup.

-/

universe u

variable {α : Type u}

/-- The action of ℕ+ on a type with Mul where
  nppowRec n a = a * a ⋯ * a (aka a^n)-/
def nppowRec [Mul α] : ℕ+ → α → α
  | 1, a => a
  | ⟨n+2, hnp⟩, a =>
    have: (⟨n+1, by simp⟩ : ℕ+) < ⟨n+2, hnp⟩ := by simp
    (nppowRec ⟨n+1, by simp⟩ a) * a
termination_by x => x

/-- A semigroup with an action of ℕ+ on it, by default it is exponentiation -/
class Semigroup' (α : Type u) extends Semigroup α where
  nppow : ℕ+ → α → α := nppowRec
  nppow_one : ∀ x, nppow 1 x = x := by intros; rfl
  nppow_succ : ∀ (n : ℕ+) (x), nppow (n+1) x = nppow n x * x

/-- Define the exponentiation notation for the action of ℕ+ on a semigroup' -/
instance [Semigroup' α]: Pow α ℕ+ :=
  ⟨fun x n ↦ Semigroup'.nppow n x⟩

class OrderedSemigroup (α : Type u) extends Semigroup' α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  mul_le_mul_right : ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c

instance [OrderedSemigroup α] : CovariantClass α α (· * ·) (· ≤ ·) where
  elim a b c bc := OrderedSemigroup.mul_le_mul_left b c bc a

instance [OrderedSemigroup α] : CovariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a b c bc := OrderedSemigroup.mul_le_mul_right b c bc a

class OrderedCancelSemigroup (α : Type u) extends OrderedSemigroup α where
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
  le_of_mul_le_mul_right : ∀ a b c : α, b * a ≤ c * a → b ≤ c

instance [OrderedCancelSemigroup α] : ContravariantClass α α (· * ·) (· ≤ ·) where
  elim a b c bc := OrderedCancelSemigroup.le_of_mul_le_mul_left a b c bc

instance [OrderedCancelSemigroup α] : ContravariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a b c bc := OrderedCancelSemigroup.le_of_mul_le_mul_right a b c bc

instance [OrderedCancelSemigroup α] : LeftCancelSemigroup α where
  mul_left_cancel a b c habc := by
    have b_le_c : b ≤ c := OrderedCancelSemigroup.le_of_mul_le_mul_left a b c (le_of_eq habc)
    have c_le_b : c ≤ b := OrderedCancelSemigroup.le_of_mul_le_mul_left a c b (le_of_eq (id (Eq.symm habc)))
    exact (le_antisymm b_le_c c_le_b)

instance [OrderedCancelSemigroup α] : RightCancelSemigroup α where
  mul_right_cancel a b c habc := by
    have a_le_c : a ≤ c := OrderedCancelSemigroup.le_of_mul_le_mul_right b a c (le_of_eq habc)
    have c_le_a : c ≤ a := OrderedCancelSemigroup.le_of_mul_le_mul_right b c a (le_of_eq (id (Eq.symm habc)))
    exact (le_antisymm a_le_c c_le_a)

class LinearOrderedSemigroup (α : Type u) extends OrderedSemigroup α, LinearOrder α

class LinearOrderedCancelSemigroup (α : Type u) extends OrderedCancelSemigroup α, LinearOrder α

instance [LinearOrderedCancelSemigroup α] : LinearOrderedSemigroup α where
  le_total := LinearOrderedCancelSemigroup.le_total
  decidableLE := LinearOrderedCancelSemigroup.decidableLE
  min_def := LinearOrderedCancelSemigroup.min_def
  max_def := LinearOrderedCancelSemigroup.max_def
  compare_eq_compareOfLessAndEq := LinearOrderedCancelSemigroup.compare_eq_compareOfLessAndEq
