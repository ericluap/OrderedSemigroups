import OrderedSemigroups.Defs
import OrderedSemigroups.OrderedGroup.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Subsemigroup.Basic
import OrderedSemigroups.Archimedean

/-!
# Basic ordered group facts

This file proves some basic facts about ordered groups and
positive cones.

-/

universe u

variable {α : Type u}

section Group
variable [Group α]

theorem pnat_pow_eq_nat_pow (x : α) (n : ℕ+) : x^(n.val) = x^n := by
  induction n using PNat.recOn with
  | p1 => simp
  | hp n ih =>
    simp [ppow_succ, pow_succ, ih]

theorem split_first_and_last_factor_of_product_group {a b : α} {n : ℕ} :
  (a*b)^(n+1) = a*(b*a)^n*b := by
  obtain n_eq_0 | n_gt_0 := Nat.eq_zero_or_pos n
  · simp [n_eq_0]
  · set n' : ℕ+ := ⟨n, n_gt_0⟩
    have : (a*b)^(n'+1) = a*(b*a)^n'*b := split_first_and_last_factor_of_product
    simpa [←pnat_pow_eq_nat_pow]

end Group

section LeftOrdered

variable [LeftOrderedGroup α]

theorem pos_exp_pos_pos {x : α} (pos_x : 1 < x) {z : ℤ} (pos_z : z > 0) :
    1 < x^z := by
  have h : z = z.natAbs := by omega
  rw [h, zpow_natCast]
  exact one_lt_pow' pos_x (by omega)

theorem nonneg_exp_pos_nonneg {x : α} (pos_x : 1 < x) {z : ℤ} (pos_z : z ≥ 0) :
    1 ≤ x^z := by
  obtain z_eq_0 | z_gt_0 := pos_z.eq_or_gt
  · simp [z_eq_0]
  · exact (pos_exp_pos_pos pos_x z_gt_0).le

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

theorem pos_lt_exp_lt {f : α} (f_pos : 1 < f) {a b : ℤ} (f_lt : f^a < f^b) : a < b := by
  have swap : (f^a)⁻¹ * f^a < (f^a)⁻¹ * f^b  := mul_lt_mul_left' f_lt (f ^ a)⁻¹
  simp only [inv_mul_cancel] at swap
  have : (f^a)⁻¹ = f^(-a) := by exact Eq.symm (zpow_neg f a)
  have one_lt_prod : 1 < f^(-a) * f^b := lt_of_lt_of_eq swap (congrFun (congrArg HMul.hMul this) (f ^ b))
  simp only [←zpow_add] at one_lt_prod
  have : 0 < -a + b := by
    by_contra h
    simp at h
    obtain b_eq_a | b_lt_a := h.eq_or_lt
    · simp [b_eq_a] at one_lt_prod
    · have : -a + b < 0 := by exact neg_add_neg_iff.mpr b_lt_a
      have : f ^ (-a + b) < 1 := by exact neg_exp_pos_neg f_pos this
      have : f ^ (-a + b) < f^(-a + b) := by exact gt_trans one_lt_prod this
      exact (lt_self_iff_false (f ^ (-a + b))).mp this
  exact lt_neg_add_iff_lt.mp this

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

def normal_semigroup {α : Type u} [Group α] (x : Subsemigroup α) :=
    ∀s : x, ∀g : α, g * s * g⁻¹ ∈ x

/--
  A left ordered group whose positive cone is a normal semigroup is an ordered group.
-/
def pos_normal_ordered (pos_normal : normal_semigroup (PositiveCone α)) :
    ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c := by
  intro a b a_le_b c
  simp [normal_semigroup, PositiveCone] at pos_normal
  have : 1 ≤ a⁻¹ * b := le_inv_mul_iff_le.mpr a_le_b
  rcases this.eq_or_lt with ainv_b_eq_one | ainv_b_pos
  -- Case `a = b`
  · have : a*1 = a*(a⁻¹*b) := congrArg (HMul.hMul a) ainv_b_eq_one
    simp at this
    simp [this]
  -- Case `a < b`
  have := pos_normal (a⁻¹ * b) ainv_b_pos c⁻¹
  simp at this
  have : c * 1 < c * (c⁻¹ * (a⁻¹ * b) * c) := mul_lt_mul_left' this c
  simp [mul_one, ←mul_assoc] at this
  have : a * c < a * (a⁻¹ * b * c) := mul_lt_mul_left' this a
  simp [←mul_assoc] at this
  exact this.le

end LeftOrdered
section LinearOrderedGroup

variable [LinearOrderedGroup α]

theorem comm_factor_le_group {a b : α} (h : a*b ≤ b*a) (n : ℕ) : a^n * b^n ≤ (a*b)^n := by
  obtain n_eq_0 | n_gt_0 := Nat.eq_zero_or_pos n
  · simp [n_eq_0]
  · set n' : ℕ+ := ⟨n, n_gt_0⟩
    have := comm_factor_le h n'
    simpa [←pnat_pow_eq_nat_pow]

theorem comm_swap_le_group {a b : α} (h : a*b ≤ b*a) (n : ℕ) : (a*b)^n ≤ (b*a)^n := pow_le_pow_left' h n

theorem comm_dist_le_group {a b : α} (h : a*b ≤ b*a) (n : ℕ) : (b*a)^n ≤ b^n * a^n := by
  obtain n_eq_0 | n_gt_0 := Nat.eq_zero_or_pos n
  · simp [n_eq_0]
  · set n' : ℕ+ := ⟨n, n_gt_0⟩
    have := comm_dist_le h n'
    simpa [←pnat_pow_eq_nat_pow]

theorem pos_exp_lt_lt {f : α} (f_pos : 1 < f) {a b : ℤ} (a_lt_b : a < b) : f^a < f^b := by
  have : 0 < b - a := Int.sub_pos_of_lt a_lt_b
  have : 1 < f ^ (b - a) := pos_exp_pos_pos f_pos this
  have : 1 < f^(b + (-a)) := this
  rw [zpow_add] at this
  have : 1*f^a < (f^b * f^(-a))*f^a := mul_lt_mul_right' this (f ^ a)
  simpa

theorem pos_exp_le_le {f : α} (f_pos : 1 < f) {a b : ℤ} (a_le_b : a ≤ b) : f^a ≤ f^b := by
  have : 0 ≤ b - a := Int.sub_nonneg_of_le a_le_b
  have : 1 ≤ f ^ (b - a) := nonneg_exp_pos_nonneg f_pos this
  have : 1 ≤ f^(b + (-a)) := this
  rw [zpow_add] at this
  have : 1*f^a ≤ (f^b * f^(-a))*f^a := mul_le_mul_right' this (f ^ a)
  simpa

end LinearOrderedGroup
