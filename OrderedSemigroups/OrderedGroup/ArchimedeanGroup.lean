import OrderedSemigroups.Defs
import OrderedSemigroups.OrderedGroup.Defs
import Mathlib.Data.Set.Basic
import OrderedSemigroups.SemigroupToMonoid
import Mathlib.Algebra.Group.Subsemigroup.Basic

universe u

variable {α : Type u}

section LeftOrdered

variable [LeftOrderedGroup α]

def archimedean_group (α : Type u) [LeftOrderedGroup α] :=
    ∀(g h : α), g ≠ 1 → ∃z : ℤ, g^z > h

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
