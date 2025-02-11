import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Group.Basic
import OrderedSemigroups.OrderedGroup.ArchimedeanGroup

/-!
# Monoid to Group

This file proves that for a suitable monoid `α` there exists a larger group
`with_division α` that contains it.
In particular, it shows that for every linear ordered cancel commutative monoid `α`,
`with_division α` is a linear ordered commutative group that contains it.

-/

universe u
variable {α : Type u}

section CancelCommMonoid
variable [CancelCommMonoid α]

/--
  Defines an equivalence relation ~ on pairs of elements of `α` such that
  `(x₁, x₂) ~ (y₁, y₂)` if and only if `x₁ * y₂ = x₂ * y₁`
-/
def pair_setoid (α : Type u) [CancelCommMonoid α] : Setoid (α × α) where
  r x y := x.1 * y.2 = x.2 * y.1
  iseqv := {
    refl := by simp [mul_comm]
    symm := by
      intro x y hxy
      simp [mul_comm y.2 x.1, mul_comm y.1 x.2, hxy]
    trans := by
      intro x y z h1 h2
      have : x.1 * z.2 * y.2 = x.2 * z.1 * y.2 := by
        calc x.1 * z.2 * y.2
          _ = x.1 * y.2 * z.2 := by rw [mul_assoc, mul_comm z.2 y.2, mul_assoc]
          _ = x.2 * y.1 * z.2 := by rw [h1]
          _ = x.2 * (y.2 * z.1) := by rw [mul_assoc, h2]
          _ = x.2 * z.1 * y.2 := by rw [mul_comm y.2 z.1, mul_assoc]
      simpa
  }

/--
  The type `with_division α` is the type `α × α` quotiented out by
  the equivalence relation `pair_setoid α`
-/
abbrev with_division (α : Type u) [CancelCommMonoid α] := Quotient (pair_setoid α)

def pair_mul (x y : α × α) := x * y

theorem prod_mul_eq_pair_mul (x y : α × α) : x * y = (x.1 * y.1, x.2 * y.2) := by
  simp [HMul.hMul, Prod.instMul]

def mul_pair (x y : α × α) : with_division α := Quotient.mk _ (x*y)

theorem mul_pair_well_defined : ∀(a₁ b₁ a₂ b₂ : α × α),
    (pair_setoid α).r a₁ a₂ → (pair_setoid α).r b₁ b₂ → mul_pair a₁ b₁ = mul_pair a₂ b₂ := by
  intro a b x y eq1 eq2
  simp [mul_pair]
  simp [pair_setoid] at *
  calc  a.1 * b.1 * (x.2 * y.2)
    _ = a.1 * (x.2 * b.1) * y.2 := by simp [mul_assoc, mul_comm x.2 b.1]
    _ = (a.1 * x.2) * (b.1 * y.2) := by simp [mul_assoc]
    _ = (a.2 * x.1) * (b.2 * y.1) := by simp [eq1, eq2]
    _ = a.2 * (b.2 * x.1) * y.1 := by simp [mul_assoc, mul_comm b.2 x.1]
    _ = (a.2 * b.2) * (x.1 * y.1) := by simp [mul_assoc]

def lift_mul :=
  Quotient.lift₂ (mul_pair (α := α)) mul_pair_well_defined

def lift_mul_comb (x y : α × α) : lift_mul ⟦x⟧ ⟦y⟧ = ⟦x * y⟧ := by
  simp [lift_mul, mul_pair]

def pair_inv (x : α × α) := (x.2, x.1)

def pair_inv_quot (x : α × α) := Quotient.mk (pair_setoid α) (pair_inv x)

theorem pair_inv_well_defined : ∀(a b : α × α), (pair_setoid α).r a b → pair_inv_quot a = pair_inv_quot b := by
  intro a b eq
  simp [pair_inv_quot, instHasEquivOfSetoid, pair_inv]
  exact id (Eq.symm eq)

def lift_inv := Quotient.lift (pair_inv_quot (α := α)) pair_inv_well_defined

/--
  Shows that `with_division α` is a commutative group
-/
instance : CommGroup (with_division α) where
  mul := lift_mul
  mul_assoc := by
    intro a b c
    induction' a using Quot.ind with a
    induction' b using Quot.ind with b
    induction' c using Quot.ind with c
    apply Quot.sound
    simp [prod_mul_eq_pair_mul, mul_assoc]
    exact (Setoid.refl' (pair_setoid α) (a *(b*c)))
  one := Quotient.mk (pair_setoid α) (1, 1)
  one_mul := by
    intro a
    induction' a using Quot.ind with a
    apply Quot.sound
    simp
    exact (Setoid.refl' (pair_setoid α) a)
  mul_one := by
    intro a
    induction' a using Quot.ind with a
    apply Quot.sound
    simp
    exact (Setoid.refl' (pair_setoid α) a)
  inv := lift_inv
  inv_mul_cancel := by
    intro a
    induction' a using Quot.ind with a
    apply Quot.sound
    simp [pair_inv, prod_mul_eq_pair_mul, pair_setoid, mul_comm]
  mul_comm := by
    intro a b
    induction' a using Quot.ind with a
    induction' b using Quot.ind with b
    apply Quot.sound
    simp [pair_setoid, mul_comm]

theorem mul_comb (x y : α × α) : ⟦x⟧ * ⟦y⟧ = (⟦x * y⟧ : with_division α) := rfl

/--
  The set of elements of `with_division α` represented by an element
  of the form `(x, 1)`.
-/
def over_one_subset : Set (with_division α) :=
  {x : (with_division α) | ∃y : α, Quotient.mk (pair_setoid α) (y, 1) = x}

/--
  Shows that `over_one_susbset` is a submonoid of `with_division α`
-/
def over_one_submonoid : Submonoid (with_division α) where
  carrier := over_one_subset
  mul_mem' := by
    intro a' b' ha hb
    simp [over_one_subset] at *
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    use (a * b)
    induction' a' using Quot.ind with a'
    induction' b' using Quot.ind with b'
    rw [←ha, ←hb]
    apply Quot.sound
    simp [pair_setoid]
  one_mem' := by
    simp [over_one_subset]
    use 1
    apply Quot.sound
    simp [pair_setoid]

theorem over_one_in_subset (a : α) : ⟦(a, 1)⟧ ∈ over_one_subset := by
  simp [over_one_submonoid, over_one_subset]
  use a

theorem inj_over_one (a b : α) : ⟦(a, 1)⟧ = (⟦(b, 1)⟧ : with_division α) → a = b := by
  intro eq
  simp at eq
  change (a * 1 = 1 * b) at eq
  simp at eq
  trivial

/--
  The monoid `α` is isomorphic to the submonoid of `with_division α`
  made of elements with representatives of the form `(a, 1)` where `a : α`.
-/
noncomputable def iso_over_one : α ≃* over_one_submonoid (α := α) where
  toFun x := ⟨⟦(x, 1)⟧, over_one_in_subset x⟩
  invFun x := by
    obtain ⟨y, hy⟩ := x
    simp [over_one_submonoid, over_one_subset] at hy
    use hy.choose
  left_inv := by
    simp [Function.LeftInverse]
    intro x
    have := (over_one_in_subset x).choose_spec
    apply inj_over_one at this
    simpa
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro x y
    simp [over_one_submonoid] at y
    simp [over_one_subset] at y
    induction' x using Quot.ind with x
    have := y.choose_spec
    conv_rhs => rw [←this]
  map_mul' := by
    intro x y
    apply Subtype.eq
    simp [mul_comb]

end CancelCommMonoid

section OrderedCancelCommMonoid
variable [OrderedCancelCommMonoid α]

/--
  Define an ordering on `α × α`
-/
def pair_lt (x y : α × α) : Prop :=  (x.1 * y.2 < x.2 * y.1)

/--
  `pair_lt` is transitive
-/
theorem pair_lt_trans {x y z : α × α} (x_lt_y : pair_lt x y) (y_lt_z : pair_lt y z) :
    pair_lt x z := by
  have : x.1 * z.2 * y.2  < x.2 * z.1 * y.2 := by
        calc (x.1 * z.2 * y.2)
        _ = (x.1 * y.2) * z.2 := by simp [mul_assoc, mul_comm y.2 z.2]
        _ < (x.2 * y.1) * z.2 := mul_lt_mul_right' x_lt_y z.2
        _ = x.2 * (y.1 * z.2) := by simp [mul_assoc]
        _ < x.2 * (y.2 * z.1) := mul_lt_mul_left' y_lt_z x.2
        _ = x.2 * z.1 * y.2 := by simp [mul_comm z.1 y.2, mul_assoc]
  simpa

/--
  `pair_lt` is irreflexive
-/
theorem pair_lt_irreflexive {x : α × α} (h : pair_lt x x) : False := by
  simp [pair_lt, mul_comm] at h

/--
  Show that `pair_lt` is well defined with respect to
  the `pair_setoid` relation
-/
def pair_lt_well_defined : ∀(a₁ b₁ a₂ b₂ : α × α),
    (pair_setoid α).r a₁ a₂ → (pair_setoid α).r b₁ b₂ → pair_lt a₁ b₁ = pair_lt a₂ b₂ := by
  intro a₁ b₁ a₂ b₂ ha hb
  simp [pair_lt, pair_setoid] at *
  have swap_left : (b₂.1 * a₂.2) * (a₁.1 * b₁.2) = (b₁.1 * a₁.2) * (a₂.1 * b₂.2) :=
    calc  (b₂.1 * a₂.2) * (a₁.1 * b₁.2)
      _ = (b₂.1 * b₁.2) * (a₂.2 * a₁.1) := by simp [mul_assoc, mul_comm b₁.2 _, mul_assoc]
      _ = (b₁.1 * b₂.2) * (a₁.2 * a₂.1) := by simp [mul_comm, hb, ha]
      _ = (b₁.1 * a₁.2) * (b₂.2 * a₂.1) := by simp [mul_assoc, mul_comm a₁.2]
      _ = (b₁.1 * a₁.2) * (a₂.1 * b₂.2) := by simp [mul_comm]
  have swap_right : (b₂.1 * a₂.2) * (a₁.2 * b₁.1) = (b₁.1 * a₁.2) * (a₂.2 * b₂.1) :=
    calc (b₂.1 * a₂.2) * (a₁.2 * b₁.1)
      _ = (b₁.1 * a₁.2) * (a₂.2 * b₂.1) := by simp [mul_comm]
  constructor
  · intro h
    have := mul_lt_mul_left' h (b₂.1 * a₂.2)
    simpa [swap_left, swap_right]
  · intro h
    have := mul_lt_mul_left' h (b₁.1 * a₁.2)
    simpa [←swap_left, ←swap_right]

/--
  Define the ordering relation on `with_division α` by
  lifting `pair_lt`
-/
def with_division_lt : with_division α → with_division α → Prop :=
  Quotient.lift₂ pair_lt pair_lt_well_defined

/--
  `with_division α` is a partial order
-/
instance : PartialOrder (with_division α) where
  le x y := with_division_lt x y ∨ x = y
  le_refl := by tauto
  le_trans := by
    intro x y z x_le_y y_le_z
    induction' z using Quot.ind with z
    induction' x using Quot.ind with x
    induction' y using Quot.ind with y
    rcases y_le_z with y_lt_z | y_eq_z
    <;> rcases x_le_y with x_lt_y | x_eq_y
    · left
      exact (pair_lt_trans x_lt_y y_lt_z)
    · left
      simpa [x_eq_y]
    · left
      simpa [←y_eq_z]
    · right
      simp [y_eq_z, x_eq_y]
  le_antisymm := by
    intro x y x_le_y y_le_x
    induction' x using Quot.ind with x
    induction' y using Quot.ind with y
    simp [with_division_lt, Quotient.lift₂, pair_lt, Quotient.lift] at *
    rcases x_le_y with x_lt_y | x_eq_y
    <;> rcases y_le_x with y_lt_x | y_eq_x
    · have : x.1 * y.2 < x.1 * y.2 := by
        calc x.1 * y.2
        _ < x.2 * y.1 := x_lt_y
        _ = y.1 * x.2 := by simp [mul_comm]
        _ < y.2 * x.1 := y_lt_x
        _ = x.1 * y.2 := by simp [mul_comm]
      exact False.elim ((lt_self_iff_false (x.1 * y.2)).mp this)
    · exact y_eq_x.symm
    · trivial
    · trivial

/--
  `with_division α` is an ordered commutative group
-/
instance : OrderedCommGroup (with_division α) where
  mul_le_mul_left := by
    intro x y x_le_y z
    induction' x using Quot.ind with x
    induction' y using Quot.ind with y
    induction' z using Quot.ind with z
    rcases x_le_y with x_lt_y | x_eq_y
    · left
      simp [with_division_lt, pair_lt, Quotient.lift₂, Quotient.lift] at *
      have : (z.1 * z.2) * (x.1 * y.2) < (z.1 * z.2) * (x.2 * y.1) :=
        mul_lt_mul_left' x_lt_y (z.1 * z.2)
      have : pair_lt (z * x) (z * y) := by
        simp [pair_lt]
        calc z.1 * x.1 * (z.2 * y.2)
        _ = z.1 * (z.2 * x.1) * y.2 := by simp [mul_assoc, mul_comm z.2 x.1, mul_assoc]
        _ = (z.1 * z.2) * (x.1 * y.2) := by simp [mul_assoc]
        _ < (z.1 * z.2) * (x.2 * y.1) := mul_lt_mul_left' x_lt_y (z.1 * z.2)
        _ = (z.2 * z.1) * (x.2 * y.1) := by simp [mul_comm]
        _ = z.2 * (z.1 * x.2) * y.1 := by simp [mul_assoc]
        _ = z.2 * (x.2 * z.1) * y.1 := by simp [mul_comm]
        _ = z.2 * x.2 * (z.1 * y.1) := by simp [mul_assoc]
      exact this
    · right
      simp [x_eq_y]
/-
def ordiso_over_one : α ≃*o over_one_submonoid (α := α) where
  toFun := iso_over_one
  invFun := iso_over_one.symm
  left_inv := by simp [iso_over_one]
  right_inv := _
  map_mul' := _
  map_le_map_iff' := _
-/
end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid
variable [LinearOrderedCancelCommMonoid α]

/--
  `with_division α` is a linear ordered commutative group
-/
noncomputable instance : LinearOrderedCommGroup (with_division α) where
  le_total := by
    intro x y
    induction' x using Quot.ind with x
    induction' y using Quot.ind with y
    rcases lt_trichotomy (x.1*y.2) (x.2*y.1) with x_lt_y | x_eq_y | y_lt_x
    · left
      left
      simpa [x_lt_y]
    · left
      right
      apply Quot.sound
      simpa [x_eq_y]
    · right
      left
      simp [with_division_lt, pair_lt, Quotient.lift₂, Quotient.lift]
      simp [CommMonoid.mul_comm x.2 y.1, CommMonoid.mul_comm x.1 y.2] at y_lt_x
      simp [y_lt_x]
  decidableLE := Classical.decRel fun x1 x2 ↦ x1 ≤ x2

instance : LeftOrderedSemigroup α where
  __ := inferInstanceAs (LinearOrderedCancelCommMonoid α)

noncomputable instance : LeftOrderedGroup (with_division α) where
  __ := inferInstanceAs (LinearOrderedCommGroup (with_division α))

theorem not_anom_to_arch (not_anom : ¬has_anomalous_pair α) :
    archimedean_group (with_division α) := by
  sorry

end LinearOrderedCancelCommMonoid
