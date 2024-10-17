import Mathlib.Algebra.Order.Group.Basic
import OrderedSemigroups.Sign

universe u
variable {α : Type u}

def with_one (α : Type u) := α ⊕ Unit

section Semigroup
variable [Semigroup α]

instance : Semigroup (with_one α) where
  mul x y :=
    match x, y with
    | .inl x, .inl y => .inl (x * y)
    | .inl x, .inr _ => .inl x
    | .inr _, .inl y => .inl y
    | .inr one, .inr _ => .inr one
  mul_assoc := by
    intro x y z
    rcases x with x | _ <;> rcases y with y | _ <;> rcases z with z | _
    <;> try simp [HMul.hMul]
    · exact congrArg Sum.inl (mul_assoc x y z)

instance : Monoid (with_one α) where
  one := .inr ()
  one_mul := by
    intro x
    cases x
    <;> unfold_projs
    <;> simp
  mul_one := by
    intro x
    cases x
    <;> unfold_projs
    <;> simp

end Semigroup

section CommSemigroup'
variable [CommSemigroup' α]

instance : CommMonoid (with_one α) where
  mul_comm := by
    intro x y
    cases x <;> cases y
    <;> unfold_projs
    <;> simp [mul_comm]
    · apply congrArg
      rename_i x y
      have := mul_comm x y
      unfold_projs at this
      simpa

end CommSemigroup'

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelCommSemigroup α]

instance (not_one : ∀x : α, ¬is_one x): OrderedCommMonoid (with_one α) where
  le := by
    intro x y
    rcases x with x | _
    <;> rcases y with y | _
    · exact x ≤ y
    · exact x*x ≤ x
    · exact y*y ≥ y
    · exact True
  le_refl := by
    intro x
    rcases x with x | _
    <;> simp
  le_trans := by
    intro x y z x_le_y y_le_z
    rcases x with x | one
    <;> rcases y with y | one
    <;> rcases z with z | one
    <;> simp at *
    · exact Preorder.le_trans x y z x_le_y y_le_z
    · rw [←not_pos_iff]
      exact le_not_pos_not_pos (not_pos_iff.mpr y_le_z) x_le_y
    · exact not_pos_le_not_neg (not_pos_iff.mpr x_le_y) (not_neg_iff.mpr y_le_z)
    · trivial
    · rw [←not_neg_iff]
      exact ge_not_neg_not_neg (not_neg_iff.mpr x_le_y) y_le_z
    · trivial
  le_antisymm := by
    intro x y x_le_y y_le_x
    rcases x with x | one
    <;> rcases y with y | one
    <;> simp at *
    · rw [PartialOrder.le_antisymm x y x_le_y y_le_x]
    · exact not_one x (one_right_one_forall (PartialOrder.le_antisymm (x*x) x x_le_y y_le_x))
    · exact not_one y (one_right_one_forall (PartialOrder.le_antisymm (y*y) y y_le_x x_le_y))
  mul_le_mul_left := by
    intro x y x_le_y z
    rcases x with x | one
    <;> rcases y with y | one
    <;> rcases z with z | one
    <;> unfold_projs
    <;> simp at *
    · exact mul_le_mul_left' x_le_y z
    · trivial
    · exact not_pos_right (not_pos_iff.mpr x_le_y) z
    · exact x_le_y
    · exact not_neg_right (not_neg_iff.mpr x_le_y) z
    · trivial



end LinearOrderedCancelSemigroup
