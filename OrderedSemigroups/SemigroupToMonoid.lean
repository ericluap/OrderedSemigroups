import Mathlib.Algebra.Order.Group.Basic
import OrderedSemigroups.Archimedean

universe u
variable {α : Type u}

def with_one (α : Type u) := α ⊕ Unit

section Semigroup
variable [Semigroup α]

instance {β : Type*} [Semigroup β] : Semigroup' β where

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

theorem pow_without_one {a : α} (n : ℕ+):
    (Semigroup'.nppow n (Sum.inl a : with_one α) : with_one α) = (Sum.inl (a ^ n) : with_one α) := by
  induction n using PNat.recOn with
  | p1 => simp [Semigroup'.nppow_one]
  | hp n ih =>
    simp [Semigroup'.nppow_succ, ih]
    unfold_projs
    simp [nppowRec_succ n a]
    have : Mul.mul (nppowRec n a) a = nppowRec (n+1) a := (nppowRec_succ n a).symm
    rw [this, Sum.inl.injEq]
    apply nppowRec_eq
    simp
    rfl

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
variable [LinearOrderedCancelCommSemigroup α] [not_one : Fact (∀x : α, ¬is_one x)]

instance : OrderedCommMonoid (with_one α) where
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
    · exact not_one.out x (one_right_one_forall (PartialOrder.le_antisymm (x*x) x x_le_y y_le_x))
    · exact not_one.out y (one_right_one_forall (PartialOrder.le_antisymm (y*y) y y_le_x x_le_y))
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

instance to_monoid : LinearOrderedCancelCommMonoid (with_one α) where
  le_total := by
    intro x y
    rcases x with x | one
    <;> rcases y with y | one
    · exact LinearOrder.le_total x y
    · exact LinearOrder.le_total (x * x) x
    · exact LinearOrder.le_total y (y * y)
    · simp
  decidableLE := by
    simp [DecidableRel]
    intro x y
    rcases x with x | one
    <;> rcases y with y | one
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

instance {β : Type*} [OrderedCommMonoid β] : OrderedSemigroup β where
  mul_le_mul_left := fun _ _ a_1 c ↦ mul_le_mul_left' a_1 c
  mul_le_mul_right := fun _ _ a_1 c ↦ mul_le_mul_right' a_1 c

instance toOrderedSemigroup {β : Type*} (_ : LinearOrderedCancelCommMonoid β) : OrderedSemigroup β :=
  inferInstance

theorem inr_is_one : @is_one (with_one α) _ (Sum.inr ()) := by
  simp only [is_one]
  intro x
  rcases x with x | one
  <;> unfold_projs
  <;> simp

theorem pos_without_one {a : α} : @is_positive (with_one α) _ (Sum.inl a) ↔ is_positive a := by
  constructor
  · simp only [is_positive] at *
    intro pos x
    have := pos (Sum.inl x)
    unfold_projs at this
    simp at this
    tauto
  · simp only [is_positive] at *
    intro pos x
    rcases x with x | one
    · have := pos x
      unfold_projs
      simp
      constructor
      exact this.le
      trivial
    · unfold_projs
      simp
      constructor
      exact (pos a).le
      exact pos a

theorem neg_without_one {a : α} : @is_negative (with_one α) _ (Sum.inl a) ↔ is_negative a := by
  constructor
  · simp only [is_negative] at *
    intro neg x
    have := neg (Sum.inl x)
    unfold_projs at this
    simp at this
    tauto
  · simp only [is_negative] at *
    intro neg x
    rcases x with x | one
    · have := neg x
      unfold_projs
      simp
      constructor
      exact this.le
      trivial
    · unfold_projs
      simp
      constructor
      exact (neg a).le
      exact neg a

theorem one_without_one {a : α} : @is_one (with_one α) _ (Sum.inl a) ↔ is_one a := by
  constructor
  · intro one x
    have := one (Sum.inl x)
    simp at this
  · intro one
    exact False.elim (not_one.out a one)

theorem same_sign_without_one {a b : α} : @same_sign (with_one α) _ (Sum.inl a) (Sum.inl b) ↔ same_sign a b := by
  simp [same_sign, neg_without_one, pos_without_one, one_without_one] at *

theorem arch_wrt_without_one {a b : α} : @is_archimedean_wrt (with_one α) _ (Sum.inl a) (Sum.inl b) ↔ is_archimedean_wrt a b := by
  simp [is_archimedean_wrt, pos_without_one, neg_without_one, HPow.hPow, Pow.pow, pow_without_one, nppow_eq_nppowRec]
  unfold_projs
  have {a b : α} : a ≤ b ∧ a < b ↔ a < b := by
    constructor
    · rintro ⟨-, this⟩
      exact this
    · intro h
      exact ⟨h.le, h⟩
  simp [this]

theorem arch_semigroup_arch_monoid (arch : is_archimedean (α := α)) :
    @is_archimedean (with_one α) _ := by
  simp [is_archimedean] at *
  intro x y
  rcases x with x | one
  <;> rcases y with y | one'
  <;> simp [same_sign_without_one, one_without_one, arch_wrt_without_one]
  · exact arch x y
  · right
    left
    exact inr_is_one
  · left
    exact inr_is_one
  · left
    exact inr_is_one

end LinearOrderedCancelSemigroup
