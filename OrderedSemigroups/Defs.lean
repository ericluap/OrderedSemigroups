import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import OrderedSemigroups.PNat

/-!
# Ordered Semigroups

This file defines ordered semigroups and provides some basic instances.
It also defines the action of `ℕ+` on a semigroup.

-/

variable {α : Type*}

class IsLeftOrderedSemigroup (α : Type*) [Semigroup α] [PartialOrder α] where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

instance [Semigroup α] [PartialOrder α] [IsLeftOrderedSemigroup α] :
    MulLeftMono α where
  elim a b c bc := IsLeftOrderedSemigroup.mul_le_mul_left b c bc a

class IsRightOrderedSemigroup (α : Type*) [Semigroup α] [PartialOrder α] where
  mul_le_mul_right : ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c

instance [Semigroup α] [PartialOrder α] [IsRightOrderedSemigroup α] :
    MulRightMono α where
  elim a b c bc := IsRightOrderedSemigroup.mul_le_mul_right b c bc a

class IsOrderedSemigroup (α : Type*) [Semigroup α] [PartialOrder α] extends
    IsLeftOrderedSemigroup α, IsRightOrderedSemigroup α

class IsLeftOrderedCancelSemigroup (α : Type*) [Semigroup α] [PartialOrder α]
    extends IsLeftOrderedSemigroup α where
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c

instance [Semigroup α] [PartialOrder α] [IsLeftOrderedCancelSemigroup α] :
    MulLeftReflectLE α := ⟨IsLeftOrderedCancelSemigroup.le_of_mul_le_mul_left⟩

instance [Semigroup α] [PartialOrder α] [IsLeftOrderedCancelSemigroup α] :
    MulLeftReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ ContravariantClass.elim

instance [Semigroup α] [PartialOrder α] [IsLeftOrderedCancelSemigroup α] :
    IsLeftCancelMul α where
  mul_left_cancel _ _ _ h :=
    (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge

class IsRightOrderedCancelSemigroup (α : Type*) [Semigroup α] [PartialOrder α]
    extends IsRightOrderedSemigroup α where
  le_of_mul_le_mul_right : ∀ a b c : α, b * a ≤ c * a → b ≤ c

instance [Semigroup α] [PartialOrder α] [IsRightOrderedCancelSemigroup α] :
    MulRightReflectLE α := ⟨IsRightOrderedCancelSemigroup.le_of_mul_le_mul_right⟩

instance [Semigroup α] [PartialOrder α] [IsRightOrderedCancelSemigroup α] :
    MulRightReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ ContravariantClass.elim

instance [Semigroup α] [PartialOrder α] [IsRightOrderedCancelSemigroup α] :
    IsRightCancelMul α where
  mul_right_cancel _ _ _ h :=
    (le_of_mul_le_mul_right' h.le).antisymm <| le_of_mul_le_mul_right' h.ge

class IsOrderedCancelSemigroup (α : Type*) [Semigroup α] [PartialOrder α]
    extends IsLeftOrderedCancelSemigroup α, IsRightOrderedCancelSemigroup α

instance [Semigroup α] [PartialOrder α] [IsOrderedCancelSemigroup α] :
    IsOrderedSemigroup α where
