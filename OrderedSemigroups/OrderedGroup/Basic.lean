import OrderedSemigroups.Defs
import OrderedSemigroups.OrderedGroup.Defs
import Mathlib.Data.Set.Basic
import OrderedSemigroups.SemigroupToMonoid
import Mathlib.Algebra.Group.Subsemigroup.Basic


universe u

variable {α : Type u}

section Cones

variable [Group α] [PartialOrder α]

instance PositiveCone (α : Type u) [Group α] [PartialOrder α] : Subsemigroup α where
  carrier := {x : α | 1 < x}
  mul_mem' := sorry

instance NegativeCone (α : Type u) [Group α] [PartialOrder α] : Subsemigroup α where
  carrier := {x : α | x < 1}
  mul_mem' := sorry

theorem pos_neg_disjoint : Disjoint (SetLike.coe (PositiveCone α)) (SetLike.coe (NegativeCone α)) := sorry

end Cones

section LeftOrdered

variable [LeftOrderedGroup α]

def archimedean_group (α : Type u) [LeftOrderedGroup α] :=
    ∀(g h : α), g ≠ 1 → ∃z : ℤ, g^z > h

instance : LeftOrderedSemigroup α where
  mul_le_mul_left _ _ a b :=  mul_le_mul_left' a b

theorem pos_exp_pos_pos {x : α} (pos_x : 1 < x) {z : ℤ} (pos_z : z > 0) :
    1 < x^z := by sorry

theorem pos_exp_neg_neg {x : α} (neg_x : x < 1) {z : ℤ} (pos_z : z > 0) :
    x^z < 1 := by sorry

theorem neg_exp_pos_neg {x : α} (pos_x : 1 < x) {z : ℤ} (neg_z : z < 0) :
    x^z < 1 := by sorry

theorem neg_exp_neg_pos {x : α} (neg_x : x < 1) {z : ℤ} (neg_z : z < 0) :
    1 < x^z := by sorry

theorem pos_arch {x y : α} (pos_x : 1 < x) (pos_y : 1 < y) :
    ∀z : ℤ, x^z > y → z > 0 := sorry

/--
  If x and y are both positive, then by Archimedneaness
  we have a least z such that x^z > y.
-/
theorem pos_min_arch {x y : α} (pos_x : 1 < x) (pos_y : 1 < y) :
  ∃z : ℤ, x^z > y ∧ z > 0 ∧ (∀t : ℤ, x^t > y → z < t) := sorry

/--
  The definition of archimedean for groups and the one for semigroups are equivalent.
-/
theorem arch_group_semigroup : archimedean_group α ↔ is_archimedean (α := α) := by sorry

def normal_semigroup {α : Type u} [Group α] (x : Subsemigroup α) :=
    ∀s : x, ∀g : α, g * s * g⁻¹ ∈ x

/--
  A left ordered group whose positive cone is a normal semigroup is an ordered group.
-/
def pos_normal_ordered (pos_normal : normal_semigroup (PositiveCone α)) : OrderedGroup α := by sorry

/--
  A left ordered group that is Archimedean is an ordered group.
-/
def left_arch_ordered (arch : is_archimedean (α := α)) : OrderedGroup α := by sorry

end LeftOrdered
