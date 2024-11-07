import OrderedSemigroups.Defs
import OrderedSemigroups.OrderedGroup.Defs
import Mathlib.Data.Set.Basic
import OrderedSemigroups.SemigroupToMonoid
import Mathlib.Algebra.Group.Subsemigroup.Basic


universe u

variable {α : Type u}

section LeftOrdered

variable [LeftOrderedGroup α]

instance : LeftOrderedSemigroup α where
  mul_le_mul_left _ _ a b :=  mul_le_mul_left' a b

instance PositiveCone (α : Type u) [LeftOrderedGroup α] : Subsemigroup α where
  carrier := {x : α | 1 < x}
  mul_mem' := by
    simp
    exact fun {a b} a_1 a_2 ↦ one_lt_mul' a_1 a_2

instance NegativeCone (α : Type u) [LeftOrderedGroup α] : Subsemigroup α where
  carrier := {x : α | x < 1}
  mul_mem' := by
    simp
    exact fun {a b} a_1 a_2 ↦ mul_lt_one a_1 a_2

theorem pos_neg_disjoint :
    Disjoint (SetLike.coe (PositiveCone α)) (SetLike.coe (NegativeCone α)) := by
  simp [Disjoint, PositiveCone, NegativeCone]
  intro S S_subset_pos S_subset_neg
  ext x
  constructor
  · intro x_in_S
    exact (lt_self_iff_false x).mp (gt_trans (S_subset_pos x_in_S) (S_subset_neg x_in_S))
  · intro x_in_empty
    contradiction

def archimedean_group (α : Type u) [LeftOrderedGroup α] :=
    ∀(g h : α), g ≠ 1 → ∃z : ℤ, g^z > h

theorem pos_exp_pos_pos {x : α} (pos_x : 1 < x) {z : ℤ} (pos_z : z > 0) :
    1 < x^z := by
    have h : z = z.natAbs := by omega
    rw [h, zpow_natCast]
    exact one_lt_pow' pos_x (by omega)

theorem pos_exp_neg_neg {x : α} (neg_x : x < 1) {z : ℤ} (pos_z : z > 0) :
    x^z < 1 := by
    have h : z = z.natAbs := by omega
    rw [h, zpow_natCast]
    exact pow_lt_one' neg_x (by omega)

theorem neg_exp_pos_neg {x : α} (pos_x : 1 < x) {z : ℤ} (neg_z : z < 0) :
    x^z < 1 := by
    have h : 1 < x ^ (-z) := pos_exp_pos_pos pos_x (by omega)
    rwa [zpow_neg, Left.one_lt_inv_iff] at h

theorem neg_exp_neg_pos {x : α} (neg_x : x < 1) {z : ℤ} (neg_z : z < 0) :
    1 < x^z := by
    have h : x ^ (-z) < 1 := pos_exp_neg_neg neg_x (by omega)
    rwa [zpow_neg, Left.inv_lt_one_iff] at h

theorem pos_arch {x y : α} (pos_x : 1 < x) (pos_y : 1 < y) :
    ∀z : ℤ, x^z > y → z > 0 := by
    intro z
    by_contra!
    obtain ⟨h, hz⟩ := this -- h : x ^ z > y, hz : z ≤ 0
    obtain hz | hz := Int.le_iff_eq_or_lt.mp hz
    · -- case z = 0
      have : (1 : α) < 1 := by calc
        1 < y := pos_y
        _ < x^z := h
        _ = 1 := by rw [hz, zpow_zero]
      exact (lt_self_iff_false 1).mp this
    · -- case z < 0
      have : x^z < x^z := by calc
        x^z < 1 := neg_exp_pos_neg pos_x hz
        _ < y := pos_y
        _ < x^z := h
      exact (lt_self_iff_false (x ^ z)).mp this

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
