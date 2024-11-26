import Mathlib.Algebra.Order.Group.Basic
import OrderedSemigroups.Basic

universe u

variable {α : Type u}

class LeftOrderedGroup (α : Type u) extends Group α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

instance leftOrderedCovariant [LeftOrderedGroup α] : CovariantClass α α (· * ·) (· ≤ ·) where
  elim a b c bc := LeftOrderedGroup.mul_le_mul_left b c bc a

instance leftOrderedContravariant [LeftOrderedGroup α] : ContravariantClass α α (· * ·) (· ≤ ·) where
  elim a b c bc := by simpa using mul_le_mul_left' bc a⁻¹

class RightOrderedGroup (α : Type u) extends Group α, PartialOrder α where
  mul_le_mul_right : ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c

instance rightOrderedCovariant [RightOrderedGroup α] : CovariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a b c bc := RightOrderedGroup.mul_le_mul_right b c bc a

instance rightOrderedContravariant [RightOrderedGroup α] : ContravariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a b c bc := by simpa using mul_le_mul_right' bc a⁻¹

class OrderedGroup (α : Type u) extends LeftOrderedGroup α, RightOrderedGroup α

instance [OrderedGroup α] : OrderedSemigroup α where
  mul_le_mul_left := OrderedGroup.toLeftOrderedGroup.mul_le_mul_left
  mul_le_mul_right := OrderedGroup.toRightOrderedGroup.mul_le_mul_right

class LeftLinearOrderedGroup (α : Type u) extends LeftOrderedGroup α, LinearOrder α

class RightLinearOrderedGroup (α : Type u) extends RightOrderedGroup α, LinearOrder α

class LinearOrderedGroup (α : Type u) extends LeftLinearOrderedGroup α, RightLinearOrderedGroup α

instance [LinearOrderedGroup α] : OrderedGroup α where
  mul_le_mul_right := LinearOrderedGroup.toRightLinearOrderedGroup.mul_le_mul_right
