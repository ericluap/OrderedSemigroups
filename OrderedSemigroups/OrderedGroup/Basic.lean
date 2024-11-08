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
theorem pos_min_arch {x y : α} (arch : archimedean_group α) (pos_x : 1 < x) (pos_y : 1 < y) :
  ∃z : ℤ, x^z > y ∧ (∀t : ℤ, x^t > y → z ≤ t) := by
  -- Define predicate for numbers satisfying x^n > y
  let P : ℕ → Prop := fun n => x^(n : ℤ) > y

  -- Define the set of natural numbers satisfying P
  let S := {n : ℕ | P n}

  -- Since x > 1 and y > 1, and the group is Archimedean, there exists some positive n such that x^n > y
  have exists_P : ∃ n, P n := by
    obtain ⟨n, hn⟩ := arch x y (ne_of_gt pos_x)
    have n_pos : n > 0 := pos_arch pos_x pos_y n hn
    dsimp [P]
    use n.natAbs
    rwa [Int.cast_natAbs, abs_of_pos n_pos]

  -- P is a decidable predicate
  have : DecidablePred P := Classical.decPred P

  -- By the well-ordering principle, S has a least element z₀
  let z₀ := Nat.find exists_P

  -- z₀ satisfies the required properties
  use z₀
  constructor
  · exact Nat.find_spec exists_P -- x^z₀ > y
  · -- For all t, if x^t > y, then z₀ ≤ t
    intro t ht
    by_contra! h -- t < z₀, but x^t > y, so t ∈ S, contradicting minimality of z₀
    have : t > 0 := pos_arch pos_x pos_y t ht
    have t_abs : t = t.natAbs := by omega
    have t_in_S : (t.natAbs) ∈ S := by rwa [t_abs] at ht
    exact Nat.find_min exists_P (by omega) t_in_S

/--
  The definition of archimedean for groups and the one for semigroups are equivalent.
-/
theorem arch_group_semigroup : archimedean_group α ↔ is_archimedean (α := α) := by sorry

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

section LeftLinearOrderedGroup

variable [LeftLinearOrderedGroup α]

theorem neg_case_left_arch_false {g h : α} (arch : is_archimedean (α := α)) (pos_g : 1 < g) (neg_h : h < 1)
    (conj_lt_one : h * g * h⁻¹ < 1) : False := by
  simp [←arch_group_semigroup] at arch
  have pos_hinv : 1 < h⁻¹ := one_lt_inv_of_inv neg_h
  obtain ⟨z, gz_gt_hinv, z_maximum⟩ := pos_min_arch arch pos_g pos_hinv
  have hinv_lt : h⁻¹ < g⁻¹ * h⁻¹ := by
    have : h⁻¹ * (h * g * h⁻¹) < h⁻¹ * 1 := mul_lt_mul_left' conj_lt_one (h⁻¹)
    simp [mul_assoc] at this
    have : g⁻¹ * (g * h⁻¹) < g⁻¹ * h⁻¹ := mul_lt_mul_left' this g⁻¹
    simpa [mul_assoc]
  have : g⁻¹ * h⁻¹ < g⁻¹ * g^z := mul_lt_mul_left' gz_gt_hinv g⁻¹
  have hinv_lt : h⁻¹ < g⁻¹ * g^z := by exact gt_trans this hinv_lt
  have : g^z = g * g^((-1) + z) := by
    have : g^z = g^(1 + ((-1) + z)) := by simp
    have : g^(1 + ((-1) + z)) = g^(1 : ℤ) * g^((-1) + z) := by
      simp only [zpow_add g 1 (-1 + z)]
    simpa
  simp [this] at hinv_lt
  have := z_maximum (-1 + z) hinv_lt
  omega

theorem neg_case_conj_pos {g h : α} (arch : is_archimedean (α := α)) (pos_g : 1 < g) (neg_h : h < 1)
    : 1 < h * g * h⁻¹ := by
  by_contra not_pos_conj
  simp at not_pos_conj
  rcases not_pos_conj.eq_or_lt with conj_eq_one | conj_lt_one
  · have : g = 1 := by exact conj_eq_one_iff.mp conj_eq_one
    rw [this] at pos_g
    exact (lt_self_iff_false 1).mp pos_g
  exact False.elim (neg_case_left_arch_false arch pos_g neg_h conj_lt_one)

/--
  A left ordered group that is Archimedean is right ordered.
-/
theorem left_arch_ordered (arch : is_archimedean (α := α)) :
    ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c := by
  apply pos_normal_ordered
  simp [normal_semigroup, PositiveCone]
  intro g pos_g h
  -- Assume that `h * g * h⁻¹` is negative for contradiction
  by_contra not_pos_conj
  simp at not_pos_conj
  rcases not_pos_conj.eq_or_lt with conj_eq_one | conj_lt_one
  · have : g = 1 := by exact conj_eq_one_iff.mp conj_eq_one
    rw [this] at pos_g
    exact (lt_self_iff_false 1).mp pos_g
  by_cases pos_h : 1 < h
  case neg =>
    simp at pos_h
    rcases pos_h.eq_or_lt with h_eq_one | neg_h
    -- The case where `h = 1`
    · simp [h_eq_one] at *
      exact (lt_self_iff_false 1).mp (lt_imp_lt_of_le_imp_le (fun _ ↦ not_pos_conj) pos_g)
    -- The case where `h` is in the negative cone
    · exact False.elim (neg_case_left_arch_false arch pos_g neg_h conj_lt_one)
  case pos =>
    -- The case where `h` is in the positive cone
    have conjinv_pos : 1 < (h * g * h⁻¹)⁻¹ := one_lt_inv_of_inv conj_lt_one
    simp at conjinv_pos
    have hinv_neg : h⁻¹ < 1 := Left.inv_lt_one_iff.mpr pos_h
    have := neg_case_conj_pos arch conjinv_pos hinv_neg
    simp at this
    exact (lt_self_iff_false g).mp (gt_trans pos_g this)

end LeftLinearOrderedGroup
