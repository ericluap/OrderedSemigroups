import Mathlib.Algebra.Order.Group.Basic
import OrderedSemigroups.Archimedean

/-!
# Semigroup to Monoid

This file proves that for a suitable semigroup `α` there exists a larger monoid
`WithOne α` that contains it.
In particular, it shows that for every linear ordered cancel commutative semigroup `α`,
`WithOne α` is a linear ordered cancel commutative monoid that contains it.

-/

universe u
variable {α : Type u}

section Semigroup
variable [Semigroup α]

/--
  The subsemigroup of `WithOne α` containing all elements not equal to `1`
  (i.e. only the original elements of `α`).
-/
def without_one (α : Type u) [Semigroup α] : Subsemigroup (WithOne α) where
  carrier := {x : WithOne α | x ≠ 1}
  mul_mem' := by
    simp only [ne_eq, Set.mem_setOf_eq]
    intro x y x_ne_one y_ne_one
    simp only [WithOne.ne_one_iff_exists]
    use (WithOne.unone x_ne_one) * (WithOne.unone y_ne_one)
    simp

/--
  The semigroup `α` is isomorphic to the semigroup `without_one α`
-/
noncomputable def iso_without_one : α ≃* without_one α where
  toFun x := ⟨x, by simp [without_one]⟩
  invFun x := WithOne.unone x.prop
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_mul' := by simp

end Semigroup

section LinearOrderedCancelCommSemigroup
variable [CommSemigroup α] [LinearOrder α] [IsOrderedCancelSemigroup α]
  [not_one : Fact (∀x : α, ¬is_one x)]

instance : PartialOrder (WithOne α) where
  le := by
    intro x y
    induction' x with x
    <;> induction' y with y
    · exact True
    · exact y * y ≥ y
    · exact x * x ≤ x
    · exact x ≤ y
  le_refl := by
    intro x
    induction' x with x
    <;> simp
  le_trans := by
    intro x y z x_le_y y_le_z
    induction' x with x
    <;> induction' y with y
    <;> induction' z with z
    <;> simp only [ge_iff_le, WithOne.recOneCoe_coe, WithOne.recOneCoe_one] at *
    · trivial
    · rw [←not_neg_iff]
      exact ge_not_neg_not_neg (not_neg_iff.mpr x_le_y) y_le_z
    · trivial
    · exact not_pos_le_not_neg (not_pos_iff.mpr x_le_y) (not_neg_iff.mpr y_le_z)
    · rw [←not_pos_iff]
      exact le_not_pos_not_pos (not_pos_iff.mpr y_le_z) x_le_y
    · order
  lt_iff_le_not_le := by simp
  le_antisymm := by
    intro x y x_le_y y_le_x
    induction' x with x
    <;> induction' y with y
    <;> simp at *
    · exact not_one.out y
        (one_right_one_forall (PartialOrder.le_antisymm (y*y) y y_le_x x_le_y))
    · exact not_one.out x
        (one_right_one_forall (PartialOrder.le_antisymm (x*x) x x_le_y y_le_x))
    · order

instance : MulLeftMono (WithOne α) where
  elim := by
    simp only [Covariant]
    intro x y z y_le_z
    induction' x with x
    <;> induction' y with y
    <;> induction' z with z
    <;> try simp
    <;> try simpa
    · exact not_neg_right (not_neg_iff.mpr y_le_z) x
    · exact not_pos_right (not_pos_right_not_pos y_le_z) x
    · exact IsLeftOrderedSemigroup.mul_le_mul_left y z y_le_z x

instance : IsOrderedMonoid (WithOne α) where
  mul_le_mul_left _ _ a b := mul_le_mul_left' a b

noncomputable instance withOne_linearOrder : LinearOrder (WithOne α) where
  le_total := by
    intro x y
    induction' x with x
    <;> induction' y with y
    · exact Or.inr trivial
    · exact LinearOrder.le_total y (y * y)
    · exact LinearOrder.le_total (x * x) x
    · exact LinearOrder.le_total x y
  toDecidableLE := Classical.decRel LE.le

instance withOne_orderedCancelMonoid : IsOrderedCancelMonoid (WithOne α) where
  le_of_mul_le_mul_left := by
    intro x y z xy_le_xz
    induction' x with x
    <;> induction' y with y
    <;> induction' z with z
    <;> first | exact xy_le_xz | try order
    · exact not_neg_iff.1 (not_neg_right_not_neg xy_le_xz)
    · exact not_pos_iff.1 (not_pos_right_not_pos xy_le_xz)
    · exact IsLeftOrderedCancelSemigroup.le_of_mul_le_mul_left x y z xy_le_xz

instance : IsLeftOrderedSemigroup (WithOne α) where
  mul_le_mul_left _ _ a b := mul_le_mul_left' a b

variable [Pow α ℕ+] [PNatPowAssoc α]
  [Pow (WithOne α) ℕ+] [PNatPowAssoc (WithOne α)]

theorem one_pow_eq_one (n : ℕ+) : (1 : WithOne α) ^ n = 1 := by
  induction n with
  | one => simp
  | succ n ih => simp [ppow_succ, ih]

theorem coe_pow_eq_pow_coe (a : α) (n : ℕ+) :
    (a : WithOne α)^n = (a ^ n : α) := by
  induction n with
  | one => simp
  | succ n ih => simp [ppow_succ, ih]

theorem coe_lt_iff_lt (a b : α) : (a : WithOne α) < b ↔ a < b := by
  constructor
  · intro a_lt_b
    exact lt_iff_le_not_le.mpr a_lt_b
  · intro a_lt_b
    unfold_projs
    simp only [ge_iff_le, WithOne.recOneCoe_coe, not_le]
    constructor
    <;> order

theorem coe_le_iff_le (a b : α) : (a : WithOne α) ≤ b ↔ a ≤ b := by rfl

theorem not_anom_semigroup_not_anom_monoid
    (not_anom : ¬has_anomalous_pair (α := α)) :
    ¬has_anomalous_pair (α := WithOne α) := by
  simp only [has_anomalous_pair, not_exists, not_forall,
    gt_iff_lt, not_or, not_and, not_lt] at not_anom ⊢
  intro x y
  induction' x with x
  <;> induction' y with y
  · simp
  · use 1
    simp only [ppow_one, one_pow_eq_one]
    constructor
    <;> order
  · use 1
    simp [ppow_succ]
    constructor
    <;> order
  ·simp [coe_pow_eq_pow_coe, coe_lt_iff_lt, coe_le_iff_le, not_anom x y]

end LinearOrderedCancelCommSemigroup

section LinearOrderedCancelCommSemigroup
variable [CommSemigroup α] [LinearOrder α] [IsOrderedCancelSemigroup α]
    [has_one : Fact (∃one : α, ∀x : α, one * x = x)]

noncomputable instance has_one_commMonoid : CommMonoid α where
  __ := inferInstanceAs (IsOrderedCancelSemigroup α)
  one := has_one.out.choose
  one_mul := has_one.out.choose_spec
  mul_one a := one_right has_one.out.choose_spec a

instance has_one_orderedCancelMonoid : IsOrderedCancelMonoid α where
  mul_le_mul_left := by simp
  le_of_mul_le_mul_left := by simp

end LinearOrderedCancelCommSemigroup
