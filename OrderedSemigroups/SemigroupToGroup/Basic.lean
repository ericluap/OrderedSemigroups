import OrderedSemigroups.SemigroupToGroup.SemigroupToMonoid
import OrderedSemigroups.SemigroupToGroup.MonoidToGroup
import OrderedSemigroups.OrderedGroup.ArchimedeanGroup
import OrderedSemigroups.OrderedGroup.Holder
import OrderedSemigroups.Sign

/-!
# Archimedean semigroups and groups

This file proves the equivalence of the definition of Archimedean semigroup
and of Archimedean group.

-/

universe u
variable {α : Type u}

section LinearOrderedCommGroup
variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

instance : IsLeftOrderedMonoid α where
    __ := inferInstanceAs (IsOrderedMonoid α)

theorem is_one_iff_one (a : α) : is_one a ↔ a = 1 := by
  simp [is_one]

theorem is_pos_iff_gt_one (a : α) : is_positive a ↔ 1 < a := by
  simp [is_positive]

theorem is_neg_iff_lt_one (a : α) : is_negative a ↔ a < 1 := by
  simp [is_negative]

theorem pnat_eq_nat_pow (g : α) {p : ℕ+} {n : ℕ} (eq : p = n) :
    g ^ p = g ^ n := by
  induction n generalizing p with
  | zero => simp at eq
  | succ n ih =>
    cases h : n
    · simp [h] at eq
      simp [eq]
    · rename_i m
      simp [h] at eq
      set pm : ℕ+ := ⟨m+1, by simp⟩
      have : p = pm + 1 := PNat.eq eq
      rw [this]
      rw [ppow_succ, pow_succ]
      simp
      have : pm = n := h.symm
      have := ih this
      simp [this, h]

theorem pnat_eq_z_pow (g : α) {p : ℕ+} {z : ℤ} (eq : p = z) :
    g ^ p = g ^ z := by
  simp [←eq]
  exact pnat_eq_nat_pow g rfl

theorem pos_pnat_le_pnat_pow {g : α} {a b : ℕ+} (pos : 1 < g) (a_le_b : a ≤ b) :
    g ^ a ≤ g ^ b := by
  have : is_positive g := (is_pos_iff_gt_one g).mpr pos
  exact pos_ppow_le_ppow a b this a_le_b

theorem neg_pnat_le_pnat_pow {g : α} {a b : ℕ+} (neg : g < 1) (a_le_b : a ≤ b) :
    g ^ b ≤ g ^ a := by
  have : is_negative g := (is_neg_iff_lt_one g).mpr neg
  exact neg_ppow_le_ppow a b this a_le_b

theorem arch_semigroup_to_arch_group :
    is_archimedean (α := α) → archimedean_group α := by
  simp [is_archimedean, archimedean_group, is_one]
  intro is_arch g h g_ne_one
  obtain one_lt_g | one_eq_g | g_lt_one := lt_trichotomy 1 g
  <;> obtain one_lt_h | one_eq_h | h_lt_one := lt_trichotomy 1 h
  <;> try (have := one_eq_g.symm; contradiction)
  -- Both `g` and `h` are positive
  · specialize is_arch g h
    obtain g_eq_one | h_eq_one | same_sign_arch := is_arch
    · order
    · rw [h_eq_one] at one_lt_h
      order
    · have : same_sign g h := by
        simp [same_sign, is_positive]
        tauto
      specialize same_sign_arch this
      simp [is_archimedean_wrt, is_positive, is_negative] at same_sign_arch
      obtain ⟨N, hN⟩ := same_sign_arch
      use N
      obtain ⟨_, h_lt_gN⟩ | ⟨h_lt_one, _⟩ := hN N (by simp)
      · convert h_lt_gN
        norm_cast
        exact pnat_pow_eq_nat_pow g N
      · order
  · use 1
    simpa [←one_eq_h]
  · use 1
    simp
    order
  -- `g` is negative and `h` is positive
  · specialize is_arch g⁻¹ h
    obtain g_eq_one | h_eq_one | same_sign_arch := is_arch
    · simp at g_eq_one
      contradiction
    · rw [h_eq_one] at one_lt_h
      order
    · have : same_sign g⁻¹ h := by
        simp [same_sign, is_positive]
        tauto
      specialize same_sign_arch this
      simp [is_archimedean_wrt, is_positive, is_negative] at same_sign_arch
      obtain ⟨N, hN⟩ := same_sign_arch
      use -N
      have : g ^ (-(N : ℤ)) = (g⁻¹)^(N : ℤ) := by simp
      rw [this]
      obtain ⟨_, h_lt_gN⟩ | ⟨h_lt_one, _⟩ := hN N (by simp)
      · convert h_lt_gN
        norm_cast
        exact pnat_pow_eq_nat_pow g⁻¹ N
      · order
  · use -1
    simpa [←one_eq_h]
  · use -1
    have : 1 < g⁻¹ := Right.one_lt_inv_iff.mpr g_lt_one
    simp
    order

theorem pos_pos_arch_group_to_arch_semigroup (arch : archimedean_group α)
    {g : α} (one_lt_g : 1 < g) (one_lt_h : 1 < h) :
    same_sign g h → is_archimedean_wrt g h := by
  obtain ⟨z, hz⟩ := arch g h (ne_of_gt one_lt_g)
  intro same_sign_gh
  simp [is_archimedean_wrt]
  have z_gt_zero : z > 0 := pos_arch one_lt_g one_lt_h z hz
  obtain ⟨N, hN⟩ := (CanLift.prf z z_gt_zero.le : ∃N : ℕ, N = z)
  have N_gt_zero : N > 0 := by
    zify
    simp [hN, z_gt_zero]
  use ⟨N, N_gt_zero⟩
  intro n N_le_n
  left
  simp [is_positive]
  constructor
  · trivial
  · set N' : ℕ+ := ⟨N, N_gt_zero⟩
    calc h
    _ < g ^ z := hz
    _ = g ^ N := by simp [←hN]
    _ = g ^ N' := Eq.symm (pnat_eq_nat_pow g rfl)
    _ ≤ g ^ n := pos_pnat_le_pnat_pow one_lt_g N_le_n

theorem neg_neg_arch_group_to_arch_semigroup (arch : archimedean_group α)
    {g : α} (g_lt_one : g < 1) (h_lt_one : h < 1) :
    same_sign g h → is_archimedean_wrt g h := by
  have one_lt_ginv : 1 < g⁻¹ := Right.one_lt_inv_iff.mpr g_lt_one
  have one_lt_hinv : 1 < h⁻¹ := Right.one_lt_inv_iff.mpr h_lt_one

  obtain ⟨z, hz⟩ := arch g⁻¹ h⁻¹ (ne_of_gt one_lt_ginv)
  intro same_sign_gh
  simp [is_archimedean_wrt]
  have z_gt_zero : z > 0 := pos_arch one_lt_ginv one_lt_hinv z hz
  obtain ⟨N, hN⟩ := (CanLift.prf z z_gt_zero.le : ∃N : ℕ, N = z)
  have N_gt_zero : N > 0 := by
    zify
    simp [hN, z_gt_zero]
  use ⟨N, N_gt_zero⟩
  intro n N_le_n
  right
  simp [is_negative]
  constructor
  · trivial
  · set N' : ℕ+ := ⟨N, N_gt_zero⟩
    simp at hz
    calc g ^ n
    _ ≤ g ^ N' := neg_pnat_le_pnat_pow g_lt_one N_le_n
    _ = g ^ N := pnat_eq_nat_pow g rfl
    _ = g ^ z := by simp [←hN]
    _ < h := hz

theorem arch_group_to_arch_semigroup :
    archimedean_group α → is_archimedean (α := α) := by
  simp [is_archimedean, archimedean_group, is_one]
  intro arch g h
  obtain one_lt_g | one_eq_g | g_lt_one := lt_trichotomy 1 g
  <;> obtain one_lt_h | one_eq_h | h_lt_one := lt_trichotomy 1 h
  <;> try (right; left; exact one_eq_h.symm)
  all_goals try (left; exact one_eq_g.symm)
  · right; right
    exact pos_pos_arch_group_to_arch_semigroup arch one_lt_g one_lt_h
  · right; right;
    intro same_sign_gh
    simp [same_sign, is_positive, is_negative, is_one] at same_sign_gh
    obtain ⟨_, h_pos⟩ | ⟨g_neg, _⟩ | ⟨g_one, _⟩ := same_sign_gh
    · order
    · order
    · rw [g_one] at one_lt_g
      order
  · right; right;
    intro same_sign_gh
    simp [same_sign, is_positive, is_negative, is_one] at same_sign_gh
    obtain ⟨g_neg, _⟩ | ⟨_, h_neg⟩ | ⟨g_one, _⟩ := same_sign_gh
    <;> order
  · right; right
    exact neg_neg_arch_group_to_arch_semigroup arch g_lt_one h_lt_one

theorem arch_iff_arch : is_archimedean (α := α) ↔ archimedean_group α :=
  ⟨arch_semigroup_to_arch_group, arch_group_to_arch_semigroup⟩
