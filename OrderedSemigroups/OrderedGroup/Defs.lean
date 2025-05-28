import Mathlib.Algebra.Order.Group.Basic
import OrderedSemigroups.Basic

/-!
# Ordered Groups

This file defines ordered groups and provides some basic instances.

-/

universe u

variable {α : Type u}

class IsLeftOrderedMonoid (α : Type*) [Monoid α] [PartialOrder α] where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

instance [Monoid α] [PartialOrder α] [IsLeftOrderedMonoid α] :
    MulLeftMono α where
  elim a b c bc := IsLeftOrderedMonoid.mul_le_mul_left b c bc a

class IsRightOrderedMonoid (α : Type*) [Monoid α] [PartialOrder α] where
  mul_le_mul_right : ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c

instance [Monoid α] [PartialOrder α] [IsRightOrderedMonoid α] :
    MulRightMono α where
  elim a b c bc := IsRightOrderedMonoid.mul_le_mul_right b c bc a

class IsOrderedMonoid' (α : Type*) [Monoid α] [PartialOrder α] extends
    IsLeftOrderedMonoid α, IsRightOrderedMonoid α

class IsLeftOrderedCancelMonoid (α : Type*) [Monoid α] [PartialOrder α] extends
    IsLeftOrderedMonoid α where
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c

instance [Monoid α] [PartialOrder α] [IsLeftOrderedCancelMonoid α] :
    MulLeftReflectLE α := ⟨IsLeftOrderedCancelMonoid.le_of_mul_le_mul_left⟩

instance [Monoid α] [PartialOrder α] [IsLeftOrderedCancelMonoid α] :
    MulLeftReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ ContravariantClass.elim

instance [Monoid α] [PartialOrder α] [IsLeftOrderedCancelMonoid α] :
    IsLeftCancelMul α where
  mul_left_cancel _ _ _ h :=
    (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge

class IsRightOrderedCancelMonoid (α : Type*) [Monoid α] [PartialOrder α] extends
    IsRightOrderedMonoid α where
  le_of_mul_le_mul_right : ∀ a b c : α, b * a ≤ c * a → b ≤ c

instance [Monoid α] [PartialOrder α] [IsRightOrderedCancelMonoid α] :
    MulRightReflectLE α := ⟨IsRightOrderedCancelMonoid.le_of_mul_le_mul_right⟩

instance [Monoid α] [PartialOrder α] [IsRightOrderedCancelMonoid α] :
    MulRightReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ ContravariantClass.elim

instance [Monoid α] [PartialOrder α] [IsRightOrderedCancelMonoid α] :
    IsRightCancelMul α where
  mul_right_cancel _ _ _ h :=
    (le_of_mul_le_mul_right' h.le).antisymm <| le_of_mul_le_mul_right' h.ge
