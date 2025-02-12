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

def all_one_div_one (all_one : ∀x : α, x = 1) :
    ∀z : with_division α, z = Quotient.mk (pair_setoid α) (1, 1) := by
  intro z
  induction' z using Quot.ind with z
  apply Quot.sound
  simp [pair_setoid, all_one]

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

noncomputable def ordiso_over_one : α ≃*o over_one_submonoid (α := α) :=
  OrderMonoidIso.mk iso_over_one (by
    simp [iso_over_one]
    unfold_projs
    simp [with_division_lt, pair_lt, pair_setoid]
    have one_mul (a : α) : a * One.one = a := mul_right_eq_self.mpr rfl
    have one_mul' (b : α) : One.one * b = b := mul_left_eq_self.mpr rfl
    simp [one_mul, one_mul', le_iff_lt_or_eq]
    )

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

theorem not_one_div_not_one {x : with_division α}
    (not_one_div : ¬is_one x) : ∃t : α, ¬is_one t := by
  by_contra!
  induction' x using Quot.ind with x
  simp [is_one] at *
  have x1_one : x.1 = 1 := this x.1
  have x2_one : x.2 = 1 := this x.2
  have : ⟦x⟧ = (1 : with_division α) := by
    have : x = (x.1, x.2) := rfl
    rw [this, x1_one, x2_one]
    unfold_projs
    simp
  contradiction

instance : LinearOrderedCancelSemigroup α where
  __ := inferInstanceAs (LinearOrderedCancelCommMonoid α)
  mul_le_mul_right := by simp
  le_of_mul_le_mul_right := by simp

noncomputable instance : LinearOrderedGroup (with_division α) where
  __ := inferInstanceAs (LinearOrderedCommGroup (with_division α))
  mul_le_mul_right := by simp

theorem not_anom_pos_pair (not_anom : ¬has_anomalous_pair α)
    {t : α} (pos_t : is_positive t) :
    ∀z : with_division α, ¬is_one z → ∃x y : α,
    is_positive x ∧ is_positive y ∧ ⟦(x,y)⟧ = z := by
  intro z not_one_z
  induction' z using Quot.ind with z
  obtain ⟨z1', pos_z1', pos_z1_z1'⟩ := pos_large_elements not_anom (by use t) z.1
  obtain ⟨z2', pos_z2', pos_z2_z2'⟩ := pos_large_elements not_anom (by use t) z.2
  have pos_numerator : is_positive (z.1*z1'*z2') := pos_lt_pos pos_z2' (pos_z1_z1' z2')
  have pos_denominator : is_positive (z.2*z1'*z2') := by
    have := not_anomalous_pair_commutative not_anom z1' z2'
    rw [mul_assoc, this, ←mul_assoc]
    exact pos_lt_pos pos_z1' (pos_z2_z2' z1')
  use (z.1 * z1' * z2'), (z.2 * z1' * z2')
  constructor
  · exact pos_numerator
  constructor
  · exact pos_denominator
  apply Quot.sound
  simp [pair_setoid]
  calc z.1 * z1' * z2' * z.2
  _ = z.2 * (z.1 * z1' * z2') := not_anomalous_pair_commutative not_anom _ _
  _ = z.2 * (z.1 * (z1' * z2')) := by simp [mul_assoc]
  _ = z.2 * (z1' * z2' * z.1) := by simp [not_anomalous_pair_commutative not_anom]
  _ = z.2 * z1' * z2' * z.1 := by simp [mul_assoc]

theorem not_anom_neg_pair (not_anom : ¬has_anomalous_pair α)
    {t : α} (neg_t : is_negative t) :
    ∀z : with_division α, ¬is_one z → ∃x y : α,
    is_negative x ∧ is_negative y ∧ ⟦(x,y)⟧ = z := by
  intro z not_one_z
  induction' z using Quot.ind with z
  obtain ⟨z1', neg_z1', neg_z1_z1'⟩ := neg_large_elements not_anom (by use t) z.1
  obtain ⟨z2', neg_z2', neg_z2_z2'⟩ := neg_large_elements not_anom (by use t) z.2
  have neg_numerator : is_negative (z.1*z1'*z2') := lt_neg_neg neg_z2' (neg_z1_z1' z2')
  have neg_denominator : is_negative (z.2*z1'*z2') := by
    have := not_anomalous_pair_commutative not_anom z1' z2'
    rw [mul_assoc, this, ←mul_assoc]
    exact lt_neg_neg neg_z1' (neg_z2_z2' z1')
  use (z.1 * z1' * z2'), (z.2 * z1' * z2')
  constructor
  · exact neg_numerator
  constructor
  · exact neg_denominator
  apply Quot.sound
  simp [pair_setoid]
  calc z.1 * z1' * z2' * z.2
  _ = z.2 * (z.1 * z1' * z2') := not_anomalous_pair_commutative not_anom _ _
  _ = z.2 * (z.1 * (z1' * z2')) := by simp [mul_assoc]
  _ = z.2 * (z1' * z2' * z.1) := by simp [not_anomalous_pair_commutative not_anom]
  _ = z.2 * z1' * z2' * z.1 := by simp [mul_assoc]

theorem exists_pos_neg_all_one :
    (∀t : α, is_one t) ∨ (∃t : α, is_positive t) ∨ (∃t : α, is_negative t) := by
  by_cases h : ∃t : α, is_positive t
  · right; left; trivial
  simp at h
  by_cases h' : ∃t : α, is_negative t
  · right; right; trivial
  simp at h'
  left
  intro t
  obtain pos | neg | one := pos_neg_or_one t
  · exact (h t pos).elim
  · exact (h' t neg).elim
  · exact one

theorem with_div_pos_ineq {x y : α}
    (pos : is_positive (⟦(x,y)⟧ : with_division α)) :
    y < x := by
  simp [is_positive] at *
  unfold_projs at pos
  simp [with_division_lt, pair_lt, pair_setoid] at pos
  tauto

theorem with_div_neg_ineq {x y : α}
    (neg : is_negative (⟦(x,y)⟧ : with_division α)) :
    x < y := by
  simp [is_negative] at *
  unfold_projs at neg
  simp [with_division_lt, pair_lt, pair_setoid] at neg
  tauto

theorem with_div_pow (not_anom : ¬has_anomalous_pair (α := α))
    (n : ℕ) (g1 g2 : α) :
    (⟦(g1, g2)⟧ : with_division α)^n = ⟦(g1^n, g2^n)⟧ := by
  unfold_projs
  unfold npowRecAuto
  induction n with
  | zero =>
    unfold npowRec
    simp
    unfold_projs
    simp
  | succ n ih =>
    simp at ih ⊢
    unfold npowRec
    simp [ih]
    apply Quot.sound
    simp [pow_succ, pair_setoid]
    simp [not_anomalous_pair_commutative not_anom]

theorem monoid_ppow_rec_eq (n : ℕ+) (x : α) : x^(n : ℕ) = x^n := by
  induction n with
  | one => simp
  | succ n ih =>
    simp [pow_succ, ppow_succ, ih]

theorem not_anom_to_arch (not_anom : ¬has_anomalous_pair α) :
    archimedean_group (with_division α) := by
  have arch : is_archimedean (α := α) := not_anomalous_arch not_anom
  obtain all_one | ⟨t, pos_t⟩ | ⟨t, neg_t⟩ :=
    exists_pos_neg_all_one (α := α)
  · simp [archimedean_group]
    intro g _ g_not_one
    have : ¬is_one g := by simp [is_one, g_not_one]
    have all_one : ∀t : α, t = 1 := by
      simp [is_one] at all_one
      exact all_one
    have := all_one_div_one all_one
    exact (g_not_one (this g)).elim
  · apply pos_arch_arch
    intro g h pos_g pos_h
    have pos_g : is_positive g := by simpa [is_positive]
    have pos_h : is_positive h := by simpa [is_positive]
    obtain ⟨g1, g2, pos_g1, pos_g2, eq_g⟩ :=
      not_anom_pos_pair not_anom pos_t g (pos_not_one pos_g)
    obtain ⟨h1, h2, pos_h1, pos_h2, eq_h⟩ :=
      not_anom_pos_pair not_anom pos_t h (pos_not_one pos_h)
    simp [←eq_g, ←eq_h]
    simp [is_archimedean] at arch
    obtain one_g2 | one_h1 | imp := arch g2 h1
    · exact (pos_not_one pos_g2 one_g2).elim
    · exact (pos_not_one pos_h1 one_h1).elim
    have : same_sign g2 h1 := by
      simp [same_sign]
      tauto
    specialize imp this
    simp [is_archimedean_wrt] at imp
    subst_vars
    obtain ⟨N, hN⟩ := imp
    obtain ⟨pos, big⟩ | ⟨neg, small⟩ := hN N (by simp)
    · have : g2 < g1 := with_div_pos_ineq pos_g
      obtain ⟨N1, hN1⟩ := not_anom_big_sep not_anom N this
      use N1
      simp [with_div_pow not_anom]
      unfold_projs
      simp
      simp [with_division_lt, pair_lt, pair_setoid, mul_comm]
      have : h1 * g2 ^ (N1 : ℕ) < h2 * g1 ^ (N1 : ℕ) :=
        calc h1 * g2^ (N1 : ℕ)
        _ < g2^(N : ℕ) * g2^(N1 : ℕ) := by
          simp
          convert big
          exact monoid_ppow_rec_eq N g2
        _ = g2^(N1 + N : ℕ) := by simp [pow_add, mul_comm]
        _ < g1^(N1 : ℕ) := by
          have : g2 ^ ((N1 + N) : ℕ) = g2 ^ (N1 + N) := by
            rw [←monoid_ppow_rec_eq]
            norm_cast
          simp [this, monoid_ppow_rec_eq, hN1]
        _ < h2 * g1^(N1 : ℕ) := pos_h2 (g1 ^ ↑N1)
      constructor
      · left
        exact this
      · constructor
        · exact this.le
        · exact this.ne.symm
    · exact (pos_not_neg pos_h1 neg).elim
  · apply neg_arch_arch
    intro g h neg_g neg_h
    have neg_g : is_negative g := by simpa [is_negative]
    have neg_h : is_negative h := by simpa [is_negative]
    obtain ⟨g1, g2, neg_g1, neg_g2, eq_g⟩ :=
      not_anom_neg_pair not_anom neg_t g (neg_not_one neg_g)
    obtain ⟨h1, h2, neg_h1, neg_h2, eq_h⟩ :=
      not_anom_neg_pair not_anom neg_t h (neg_not_one neg_h)
    simp [←eq_g, ←eq_h]
    simp [is_archimedean] at arch
    obtain one_g2 | one_h1 | imp := arch g2 h1
    · exact (neg_not_one neg_g2 one_g2).elim
    · exact (neg_not_one neg_h1 one_h1).elim
    have : same_sign g2 h1 := by
      simp [same_sign]
      tauto
    specialize imp this
    simp [is_archimedean_wrt] at imp
    subst_vars
    obtain ⟨N, hN⟩ := imp
    obtain ⟨pos, big⟩ | ⟨neg, small⟩ := hN N (by simp)
    · exact (neg_not_pos neg_h1 pos).elim
    · have : g1 < g2 := with_div_neg_ineq neg_g
      obtain ⟨N1, hN1⟩ := not_anom_big_sep' not_anom N this
      use N1
      simp [with_div_pow not_anom]
      unfold_projs
      simp
      simp [with_division_lt, pair_lt, pair_setoid, mul_comm]
      have : h1 * g2 ^ (N1 : ℕ) > h2 * g1 ^ (N1 : ℕ) :=
        calc h1 * g2 ^ (N1 : ℕ)
        _ > g2^(N : ℕ) * g2^(N1 : ℕ) := by
          simp
          convert small
          exact monoid_ppow_rec_eq N g2
        _ = g2^(N1 + N : ℕ) := by simp [pow_add, mul_comm]
        _ > g1^(N1 : ℕ) := by
          have : g2 ^ ((N1 + N) : ℕ) = g2 ^ (N1 + N) := by
            rw [←monoid_ppow_rec_eq]
            norm_cast
          simp [this, monoid_ppow_rec_eq, hN1]
        _ > h2 * g1^(N1 : ℕ) := neg_h2 (g1 ^ ↑N1)
      constructor
      · left
        exact this
      · constructor
        · exact this.le
        · exact this.ne.symm

end LinearOrderedCancelCommMonoid
