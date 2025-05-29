import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Group.Basic
import OrderedSemigroups.OrderedGroup.ArchimedeanGroup
import Mathlib.GroupTheory.MonoidLocalization.Order

/-!
# Monoid to Group

Thie files proves that if a suitable monoid does not have anomalous pairs,
then the smallest group containing it is Archimedean.

-/

universe u
variable {α : Type u}

section LinearOrderedCancelCommMonoid
variable [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α]
  [Pow α ℕ+] [PNatPowAssoc α]

abbrev with_division (α : Type*) [CommMonoid α] := Localization (⊤ : Submonoid α)

def with_division.mk (m s : α) : with_division α := Localization.mk m ⟨s, by simp⟩

abbrev over_one (α : Type*) [CommMonoid α] :=
  MonoidHom.mrange ((Localization.monoidOf (⊤ : Submonoid α)).toMap)

abbrev over_one_map (α : Type*) [CommMonoid α] : α →* over_one α
  := (Localization.monoidOf (⊤ : Submonoid α)).mrangeRestrict

theorem over_one_map_inj : Function.Injective (over_one_map α) := by
  simp [Function.Injective]
  intro a b hab
  simp [over_one_map, MonoidHom.mrangeRestrict,
    ←Localization.mk_one_eq_monoidOf_mk] at hab
  simp [Localization.mk_eq_mk_iff'] at hab
  trivial

noncomputable def iso_over_one : α ≃*o (over_one α) where
  toFun := (Localization.monoidOf (⊤ : Submonoid α)).mrangeRestrict
  invFun x := x.prop.choose
  left_inv := by
    simp [Function.LeftInverse]
    intro x
    apply over_one_map_inj
    simp [over_one_map]
    simp [←Subtype.val_inj]
    exact (over_one_map α x).prop.choose_spec
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro x y hyx
    set t : over_one α := ⟨x, by use y⟩
    simp [MonoidHom.mrangeRestrict, t.prop.choose_spec, t]
  map_mul' := by simp
  map_le_map_iff' := by
    simp [MonoidHom.mrangeRestrict, ←Localization.mk_one_eq_monoidOf_mk,
      Localization.mk_le_mk]

instance : CommGroup (with_division α) where
  __ := inferInstanceAs (CommMonoid (with_division α))
  inv x := Localization.liftOn x
          (fun m s => Localization.mk s ⟨m, by simp⟩)
          (by
            intro a c b d h
            simp [Localization.mk_eq_mk_iff',
              Localization.r_iff_exists] at h ⊢
            simp [mul_comm c, mul_comm a, h])
  inv_mul_cancel := by
    intro x
    unfold with_division at x
    induction x with
    | H y =>
      simp [Localization.liftOn_mk, Localization.mk_mul,
        ←Localization.mk_one, Localization.mk_eq_mk_iff', mul_comm]

instance monoid_to_semigroup : IsOrderedCancelSemigroup α where
  __ := inferInstanceAs (IsOrderedCancelMonoid α)
  mul_le_mul_right := by simp
  le_of_mul_le_mul_right := by simp

instance : IsOrderedSemigroup (with_division α) where
  mul_le_mul_left := by simp
  mul_le_mul_right := by simp

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

theorem not_anom_pos_pair (not_anom : ¬has_anomalous_pair α)
    {t : α} (pos_t : is_positive t) :
    ∀z : with_division α, ¬is_one z → ∃x y : α,
    is_positive x ∧ is_positive y ∧ with_division.mk x y = z := by
  intro z not_one_z
  unfold with_division at *
  induction' z with z
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
  simp [with_division.mk, Localization.mk_eq_mk_iff']
  calc z.2 * (z.1 * z1' * z2')
  _ = z.2 * (z1' * z.1 * z2') := by simp [mul_comm]
  _ = z.2 * (z1' * (z.1 * z2')) := by simp [mul_assoc]
  _ = z.2 * z1' * z2' * z.1 := by simp [mul_comm z2', mul_assoc]

theorem not_anom_neg_pair (not_anom : ¬has_anomalous_pair α)
    {t : α} (neg_t : is_negative t) :
    ∀z : with_division α, ¬is_one z → ∃x y : α,
    is_negative x ∧ is_negative y ∧ with_division.mk x y = z := by
  intro z not_one_z
  unfold with_division at *
  induction' z with z
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
  simp [with_division.mk, Localization.mk_eq_mk_iff']
  calc z.2 * (z.1 * z1' * z2')
  _ = z.2 * (z1' * z.1 * z2') := by simp [mul_comm]
  _ = z.2 * (z1' * (z.1 * z2')) := by simp [mul_assoc]
  _ = z.2 * z1' * z2' * z.1 := by simp [mul_comm z2', mul_assoc]

theorem all_one_div_one (all_one : ∀x : α, x = 1) :
    ∀z : with_division α, z = 1 := by
  intro z
  unfold with_division at *
  induction' z with z
  simp [←Localization.mk_one, Localization.mk_eq_mk_iff', all_one]

theorem with_div_pos_ineq {x y : α}
    (pos : is_positive (with_division.mk x y)) :
    y < x := by
  rw [is_positive] at pos
  simp [with_division.mk, Localization.liftOn₂_mk] at pos
  rw [←Localization.mk_one] at pos
  simp [Localization.mk_lt_mk] at pos
  trivial

theorem with_div_neg_ineq {x y : α}
    (neg : is_negative (with_division.mk x y)) :
    x < y := by
  rw [is_negative] at neg
  simp [with_division.mk, Localization.liftOn₂_mk] at neg
  rw [←Localization.mk_one] at neg
  simp [Localization.mk_lt_mk] at neg
  trivial

theorem with_div_pow (n : ℕ) (g1 g2 : α) :
    (with_division.mk g1 g2)^n = with_division.mk (g1^n) (g2^n) := by
  simp [with_division.mk]
  induction n with
  | zero =>
    simp [←Localization.mk_one, Localization.mk_eq_mk_iff']
  | succ n ih =>
    simp [pow_succ, ih, Localization.mk_mul]

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
      intro t
      simp only [is_one] at all_one
      exact mul_eq_left.mp (all_one t t)
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
    simp only [← eq_g, ← eq_h, gt_iff_lt]
    simp only [is_archimedean] at arch
    obtain one_g2 | one_h1 | imp := arch g2 h1
    · exact (pos_not_one pos_g2 one_g2).elim
    · exact (pos_not_one pos_h1 one_h1).elim
    have : same_sign g2 h1 := by
      simp only [same_sign]
      tauto
    specialize imp this
    simp only [is_archimedean_wrt, ge_iff_le] at imp
    subst_vars
    obtain ⟨N, hN⟩ := imp
    obtain ⟨pos, big⟩ | ⟨neg, small⟩ := hN N (by simp only [le_refl])
    · have : g2 < g1 := with_div_pos_ineq pos_g
      obtain ⟨N1, hN1⟩ := not_anom_big_sep not_anom N this
      use N1
      simp only [with_div_pow]
      simp only [with_division.mk, Localization.mk_lt_mk]
      calc g2^ (N1 : ℕ) * h1
      _ = h1 * g2 ^ (N1 : ℕ) := by simp [mul_comm]
      _ < g2^(N : ℕ) * g2^(N1 : ℕ) := by
        simp only [mul_lt_mul_iff_right]
        convert big
        exact monoid_ppow_rec_eq N g2
      _ = g2^(N1 + N : ℕ) := by simp [pow_add, mul_comm]
      _ < g1^(N1 : ℕ) := by
        have : g2 ^ ((N1 + N) : ℕ) = g2 ^ (N1 + N) := by
          rw [←monoid_ppow_rec_eq]
          norm_cast
        simp [this, monoid_ppow_rec_eq, hN1]
      _ < h2 * g1^(N1 : ℕ) := pos_h2 (g1 ^ ↑N1)
    · exact (pos_not_neg pos_h1 neg).elim
  · apply neg_arch_arch
    intro g h neg_g neg_h
    have neg_g : is_negative g := by simpa [is_negative]
    have neg_h : is_negative h := by simpa [is_negative]
    obtain ⟨g1, g2, neg_g1, neg_g2, eq_g⟩ :=
      not_anom_neg_pair not_anom neg_t g (neg_not_one neg_g)
    obtain ⟨h1, h2, neg_h1, neg_h2, eq_h⟩ :=
      not_anom_neg_pair not_anom neg_t h (neg_not_one neg_h)
    simp only [← eq_g, ← eq_h]
    simp only [is_archimedean] at arch
    obtain one_g2 | one_h1 | imp := arch g2 h1
    · exact (neg_not_one neg_g2 one_g2).elim
    · exact (neg_not_one neg_h1 one_h1).elim
    have : same_sign g2 h1 := by
      simp only [same_sign]
      tauto
    specialize imp this
    simp only [is_archimedean_wrt, ge_iff_le] at imp
    subst_vars
    obtain ⟨N, hN⟩ := imp
    obtain ⟨pos, big⟩ | ⟨neg, small⟩ := hN N (by simp)
    · exact (neg_not_pos neg_h1 pos).elim
    · have : g1 < g2 := with_div_neg_ineq neg_g
      obtain ⟨N1, hN1⟩ := not_anom_big_sep' not_anom N this
      use N1
      simp only [with_div_pow]
      simp only [with_division.mk, Localization.mk_lt_mk]
      calc g2 ^ (N1 : ℕ) * h1
        _ = h1 * g2 ^ (N1 : ℕ) := by simp [mul_comm]
        _ > g2^(N : ℕ) * g2^(N1 : ℕ) := by
          simp only [gt_iff_lt, mul_lt_mul_iff_right]
          convert small
          exact monoid_ppow_rec_eq N g2
        _ = g2^(N1 + N : ℕ) := by simp [pow_add, mul_comm]
        _ > g1^(N1 : ℕ) := by
          have : g2 ^ ((N1 + N) : ℕ) = g2 ^ (N1 + N) := by
            rw [←monoid_ppow_rec_eq]
            norm_cast
          simp [this, monoid_ppow_rec_eq, hN1]
        _ > h2 * g1^(N1 : ℕ) := neg_h2 (g1 ^ ↑N1)

end LinearOrderedCancelCommMonoid
