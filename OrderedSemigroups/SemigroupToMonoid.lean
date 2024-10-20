import Mathlib.Algebra.Order.Group.Basic
import OrderedSemigroups.Archimedean

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

def without_one : Subsemigroup (with_one α) where
  carrier := {x : with_one α | ∃y : α, x = Sum.inl y}
  mul_mem' := by
    intro x' y' hx hy
    obtain ⟨x, hx⟩ := hx
    obtain ⟨y, hy⟩ := hy
    subst_vars
    simp
    use (x*y)
    unfold_projs
    simp

noncomputable def iso_without_one : α ≃* without_one (α := α) where
  toFun x := ⟨Sum.inl x, by use x⟩
  invFun x := by
    obtain ⟨y, hy⟩ := x
    use hy.choose
  left_inv := by
    simp [Function.LeftInverse]
    intro x
    set point : without_one (α := α) := ⟨Sum.inl x, by use x⟩
    have := point.2.choose_spec
    apply Sum.inl.inj
    rw [←this]
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro x hx
    obtain ⟨y, hy⟩ := hx
    simp [hy]
    rw [Sum.inl.injEq]
    set point : without_one (α := α) := ⟨Sum.inl y, by use y⟩
    have := point.2.choose_spec
    apply Sum.inl.inj
    rw [←this]
  map_mul' := by
    intro x y
    unfold_projs
    simp

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

set_option maxHeartbeats 300000
instance to_monoid (not_one : ∀x : α, ¬is_one x) : LinearOrderedCancelCommMonoid (with_one α) where
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
    <;> simp only [le_refl]
  le_trans := by
    intro x y z x_le_y y_le_z
    rcases x with x | one
    <;> rcases y with y | one
    <;> rcases z with z | one
    <;> simp only [ge_iff_le] at *
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
    <;> simp only [ge_iff_le, reduceCtorEq] at *
    · rw [PartialOrder.le_antisymm x y x_le_y y_le_x]
    · exact not_one x (one_right_one_forall (PartialOrder.le_antisymm (x*x) x x_le_y y_le_x))
    · exact not_one y (one_right_one_forall (PartialOrder.le_antisymm (y*y) y y_le_x x_le_y))
  mul_le_mul_left := by
    intro x y x_le_y z
    rcases x with x | one
    <;> rcases y with y | one
    <;> rcases z with z | one
    <;> unfold_projs
    <;> simp only [ge_iff_le, le_refl] at *
    · exact mul_le_mul_left' x_le_y z
    · trivial
    · exact not_pos_right (not_pos_iff.mpr x_le_y) z
    · exact x_le_y
    · exact not_neg_right (not_neg_iff.mpr x_le_y) z
    · trivial
  le_total := by
    intro x y
    rcases x with x | one
    <;> rcases y with y | one
    <;> simp only [ge_iff_le, or_self] at *
    · exact LinearOrder.le_total x y
    · exact LinearOrder.le_total (x * x) x
    · exact LinearOrder.le_total y (y * y)
  decidableLE := by
    simp [DecidableRel]
    intro x y
    rcases x with x | one
    <;> rcases y with y | one
    <;> simp at *
    · exact instDecidableLe_mathlib x y
    · exact instDecidableLe_mathlib (x * x) x
    · exact instDecidableLe_mathlib y (y * y)
    · exact instDecidableTrue
  le_of_mul_le_mul_left := by
    intro x y z xy_le_xz
    rcases x with x | one
    <;> rcases y with y | one
    <;> rcases z with z | one
    <;> unfold_projs at *
    <;> simp only [ge_iff_le] at *
    · exact (mul_le_mul_iff_left x).mp xy_le_xz
    · exact not_pos_iff.1 (not_pos_right_not_pos xy_le_xz)
    · exact not_neg_iff.1 (not_neg_right_not_neg xy_le_xz)
    all_goals exact xy_le_xz

instance {β : Type*} [Semigroup β] : Semigroup' β where

instance {β : Type*} [OrderedCommMonoid β] : OrderedSemigroup β where
  mul_le_mul_left := fun _ _ a_1 c ↦ mul_le_mul_left' a_1 c
  mul_le_mul_right := fun _ _ a_1 c ↦ mul_le_mul_right' a_1 c

instance toOrderedSemigroup {β : Type*} (_ : LinearOrderedCancelCommMonoid β) : OrderedSemigroup β :=
  inferInstance

theorem arch_semigroup_arch_monoid (not_one : ∀x : α, ¬is_one x) (arch : is_archimedean (α := α)) :
    @is_archimedean (with_one α) (toOrderedSemigroup (to_monoid not_one)) := sorry


end LinearOrderedCancelSemigroup
