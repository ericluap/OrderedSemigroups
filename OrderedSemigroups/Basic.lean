import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.PNat.Defs

universe u

variable {α : Type u}

instance : Add ℕ+ :=
  ⟨fun a b ↦ ⟨a.val + b.val, by
    have a' : 0 < a.val := by simp
    have b' : 0 < b.val := by simp
    omega⟩⟩

instance : HAdd ℕ+ ℕ ℕ+ :=
  ⟨fun a b ↦ ⟨a.val + b, by
    have a' : 0 < a.val := by simp
    omega⟩⟩

def nppowRec [Mul α] : ℕ+ → α → α
  | 1, a => a
  | ⟨n+2, hnp⟩, a =>
    have: (⟨n+1, by simp⟩ : ℕ+) < ⟨n+2, hnp⟩ := by simp
    (nppowRec ⟨n+1, by simp⟩ a) * a
termination_by x => x

class Semigroup' (α : Type u) extends Semigroup α where
  nppow : ℕ+ → α → α := nppowRec
  nppow_one : ∀ x, nppow 1 x = x := by intros; rfl
  nppow_succ : ∀ (n : ℕ+) (x), nppow (n+1) x = nppow n x * x

instance (α : Type u) [Semigroup' α] : Pow α ℕ+ :=
  ⟨fun x n ↦ Semigroup'.nppow n x⟩

theorem nppow_eq_pow [Semigroup' α] (n : ℕ+) (x : α) : Semigroup'.nppow n x = x ^ n := rfl

class OrderedSemigroup (α : Type u) extends Semigroup' α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  mul_le_mul_right : ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c

instance (α : Type u) [OrderedSemigroup α] : CovariantClass α α (· * ·) (· ≤ ·) where
  elim a b c bc := OrderedSemigroup.mul_le_mul_left b c bc a

instance (α : Type u) [OrderedSemigroup α] : CovariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a b c bc := OrderedSemigroup.mul_le_mul_right b c bc a

class OrderedCancelSemigroup (α : Type u) extends OrderedSemigroup α where
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
  le_of_mul_le_mul_right : ∀ a b c : α, b * a ≤ c * a → b ≤ c

instance (α : Type u) [OrderedCancelSemigroup α] : ContravariantClass α α (· * ·) (· ≤ ·) where
  elim a b c bc := OrderedCancelSemigroup.le_of_mul_le_mul_left a b c bc

instance (α : Type u) [OrderedCancelSemigroup α] : ContravariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a b c bc := OrderedCancelSemigroup.le_of_mul_le_mul_right a b c bc

class LinearOrderedSemigroup (α : Type u) extends OrderedSemigroup α, LinearOrder α

section LinearOrderedSemigroup

variable [LinearOrderedSemigroup α]

end LinearOrderedSemigroup
