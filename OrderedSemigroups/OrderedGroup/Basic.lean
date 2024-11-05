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
