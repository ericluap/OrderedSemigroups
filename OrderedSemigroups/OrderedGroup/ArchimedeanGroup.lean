import OrderedSemigroups.OrderedGroup.Basic
import OrderedSemigroups.Defs
import OrderedSemigroups.OrderedGroup.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Tactic

/-!
# Archimedean Groups

This file defines and proves things about Archimedean groups.

-/

universe u

variable {α : Type u}

section LeftOrdered

variable [LeftOrderedGroup α]

def archimedean_group (α : Type u) [LeftOrderedGroup α] :=
    ∀(g h : α), g ≠ 1 → ∃z : ℤ, g^z > h

theorem gt_exp (arch : archimedean_group α) (f g : α) (f_ne_one : f ≠ 1) : ∃z : ℤ, g < f^z := by
  obtain ⟨z, hz⟩ := arch f g f_ne_one
  simp at hz
  use z

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

theorem neg_case_left_arch_false {g h : α} (arch : archimedean_group α) (pos_g : 1 < g) (neg_h : h < 1)
    (conj_lt_one : h * g * h⁻¹ < 1) : False := by
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

end LeftOrdered
section LeftLinearOrderedGroup

variable [LeftLinearOrderedGroup α]

theorem neg_case_conj_pos {g h : α} (arch : archimedean_group α) (pos_g : 1 < g) (neg_h : h < 1)
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
theorem left_arch_ordered (arch : archimedean_group α) :
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

def left_arch_ordered_group (arch : archimedean_group α) : LinearOrderedGroup α where
  mul_le_mul_right := by exact fun a b a_1 c ↦ left_arch_ordered arch a b a_1 c

end LeftLinearOrderedGroup

section LinearOrderedGroup

variable [LinearOrderedGroup α]

theorem lt_exp (arch : archimedean_group α) (f g : α) (f_ne_one : f ≠ 1) : ∃z : ℤ, f^z < g := by
  obtain f_le_g | g_lt_f := le_or_lt f g
  · obtain f_lt_one | one_lt_f := lt_or_gt_of_ne f_ne_one
    · have : f*f < f := (mul_lt_iff_lt_one_right' f).mpr f_lt_one
      use 2
      simp [zpow_two f]
      exact mul_lt_of_le_of_lt_one f_le_g f_lt_one
    · have : f⁻¹ < f := by exact Right.inv_lt_self one_lt_f
      use -1
      simp
      exact gt_of_ge_of_gt f_le_g this
  · have : f⁻¹ < g⁻¹ := inv_lt_inv_iff.mpr g_lt_f
    have finv_ne_one : f⁻¹ ≠ 1 := inv_ne_one.mpr f_ne_one
    obtain ⟨z, hz⟩ := arch f⁻¹ g⁻¹ finv_ne_one
    simp at hz
    use z

end LinearOrderedGroup
