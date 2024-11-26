import OrderedSemigroups.OrderedGroup.Basic
import OrderedSemigroups.Convergence
import OrderedSemigroups.Basic

/--
  Every nonempty set of integers that is bounded above has a maximum element.
-/
theorem bounded_above_max {S : Set ℤ} (nonempty : Nonempty S) (upper_bounded : BddAbove S) : ∃max ∈ S, max ∈ upperBounds S := by
  simp [BddAbove, upperBounds] at *
  -- `s` is an element in `S`
  obtain ⟨s, hs⟩ := nonempty
  -- `m` is an upper bound of `S`
  obtain ⟨m, hm⟩ := upper_bounded
  simp at hm

  -- `subset` is the set `[s,m]`
  set subset := Set.Icc s m
  -- `subset` is clearly finite
  have : subset.Finite := by exact Set.finite_Icc s m
  -- `S_subset` is all elements of `S` that are larger than `s`
  set S_subset := {x : ℤ | x ∈ S ∧ s ≤ x}
  have each_subset : S_subset ⊆ subset := by
    simp [S_subset, subset, Set.Icc]
    intro x x_in_S s_le_x
    constructor
    · trivial
    · exact hm x_in_S
  -- `S_subset` is finite and nonempty
  have S_subset_finite : S_subset.Finite := by exact Set.Finite.subset this each_subset
  have S_subset_nonempty : S_subset.Nonempty := by
    use s
    trivial

  -- a finite and nonempty set has a maximum element and that's what we want
  obtain ⟨a, a_in_S_subset, a_max⟩ := Set.Finite.exists_maximal_wrt (fun x : ℤ => x) S_subset S_subset_finite S_subset_nonempty
  use a
  constructor
  · exact Set.mem_of_mem_inter_left a_in_S_subset
  · intro t t_in_S
    obtain t_lt_s | s_le_t := Int.lt_or_le t s
    obtain ⟨_, s_le_a⟩ := a_in_S_subset
    · transitivity s
      exact t_lt_s.le
      trivial
    · have : t ∈ S_subset := by exact Set.mem_sep t_in_S s_le_t
      by_contra a_lt_t
      simp at a_lt_t
      exact a_lt_t.ne (a_max t this a_lt_t.le)

universe u

variable {α : Type u} [LeftLinearOrderedGroup α] {f : α} (f_pos : 1 < f)
  [arch : Fact (archimedean_group α)]

instance : LinearOrderedGroup α where
  mul_le_mul_right := by exact fun a b a_1 c ↦ left_arch_ordered arch.elim a b a_1 c

include f_pos in
theorem approximate (g : α) (p : ℕ):
  ∃(q : ℤ), f^q ≤ g^p ∧ g^p < f^(q+1) := by
  obtain ⟨l, hl⟩ := lt_exp arch.out f (g^p) (f_pos.ne.symm)
  obtain ⟨u, hu⟩ := gt_exp arch.out f (g^p) (f_pos.ne.symm)
  set small_exp := {z : ℤ | f^z ≤ g^p}
  have small_exp_nonempty : Nonempty small_exp := by
    use l
    simp [small_exp]
    exact hl.le
  have small_exp_bddabove : BddAbove small_exp := by
    simp [BddAbove]
    use u
    intro a ha
    simp [small_exp] at ha
    have : f^a < f^u := by exact lt_of_le_of_lt ha hu
    exact (pos_lt_exp_lt f_pos this).le
  obtain ⟨z, z_small, z_max⟩ := bounded_above_max small_exp_nonempty small_exp_bddabove
  use z
  simp [small_exp, upperBounds] at z_small z_max
  constructor
  · trivial
  · specialize @z_max (z+1)
    rw [←not_imp_not] at z_max
    simp at z_max
    trivial

noncomputable def q (g : α) (p : ℕ) : ℤ := (approximate f_pos g p).choose

theorem q_spec (g : α) (p : ℕ) :
  f^(q f_pos g p) ≤ g^p ∧ g^p < f^((q f_pos g p)+1) := by
    have := (approximate f_pos g p).choose_spec
    simp at this
    simp [q]
    tauto

theorem q_max_lt (g : α) (p : ℕ) {t : ℤ} (ht : f^t ≤ g^p) : t ≤ q f_pos g p := by
  have ⟨_, gp_lt_fqp1⟩ := q_spec f_pos g p
  by_contra h
  simp at h
  have : q f_pos g p + 1 ≤ t := h
  have lt_t : f ^ (q f_pos g p + 1) ≤ f^t := pos_exp_le_le f_pos h
  have : f ^ t < f ^ (q f_pos g p + 1) := lt_of_le_of_lt ht gp_lt_fqp1
  have : f ^ t < f ^ t := gt_of_ge_of_gt lt_t this
  exact (lt_self_iff_false (f ^ t)).mp this

theorem qplus1_min_gt (g : α) (p : ℕ) {t : ℤ} (ht : g^p < f^t) : q f_pos g p + 1 ≤ t := by
  have ⟨fqp_lt_gt, _⟩ := q_spec f_pos g p
  by_contra h
  simp at h
  have : t ≤ q f_pos g p := (Int.add_le_add_iff_right 1).mp h
  have : f^t ≤ f^(q f_pos g p) := pos_exp_le_le f_pos this
  have : g^p < f^(q f_pos g p) := gt_of_ge_of_gt this ht
  have : g^p < g^p := gt_of_ge_of_gt fqp_lt_gt this
  exact (lt_self_iff_false (g ^ p)).mp this

theorem q_exp_add (g : α) (a b : ℕ) :
    f^((q f_pos g a) + (q f_pos g b)) ≤ g^(a + b) ∧
    g^(a+b) < f^((q f_pos g a) + (q f_pos g b)+2) := by
  have ⟨fqa_le_ga, ga_lt_fa1⟩ := q_spec f_pos g a
  have ⟨fqb_le_gb, gb_lt_fb1⟩ := q_spec f_pos g b
  constructor
  · have : (f ^ q f_pos g a)*(f ^ q f_pos g b) ≤ g^a*g^b :=
      mul_le_mul' fqa_le_ga fqb_le_gb
    simp [←zpow_add, ←pow_add] at this
    trivial
  · have : (g ^ a) * (g ^ b) < (f ^ (q f_pos g a + 1)) * f ^ (q f_pos g b + 1) :=
      Left.mul_lt_mul ga_lt_fa1 gb_lt_fb1
    simp [←zpow_add, ←pow_add] at this
    have exp_add :
        q f_pos g a + 1 + (q f_pos g b + 1) = q f_pos g a + q f_pos g b + 2 := by
      ring
    simp [exp_add] at this
    trivial

theorem q_convergence (g : α) :
  ∃r : ℝ, Filter.Tendsto (fun p ↦ ((q f_pos g p) : ℝ)/(p : ℝ)) Filter.atTop (nhds r) := by
  apply sequence_convergence (C := 1)
  intro m n
  obtain ⟨fab_le_gab, gab_lt_abplus2⟩ := q_exp_add f_pos g m n
  have qmplusqn_le_qmplusn:= q_max_lt f_pos g (m+n) fab_le_gab
  have qmplusn_le_qmplusqnplus2 := qplus1_min_gt f_pos g (m+n) gab_lt_abplus2
  have := Int.sub_le_sub_right qmplusn_le_qmplusqnplus2 1
  simp at this
  ring_nf at this
  have diff_le_1: q f_pos g (m+n) - q f_pos g m - q f_pos g n ≤ 1 := by
    simp
    rw [add_assoc, add_comm (q f_pos g n), ←add_assoc]
    trivial
  have diff_ge_0 : 0 ≤ q f_pos g (m+n) - q f_pos g m - q f_pos g n := by
    simp
    have := Int.sub_le_sub_right qmplusqn_le_qmplusn (q f_pos g m)
    simpa
  norm_cast
  have := abs_of_nonneg diff_ge_0
  rw [this]
  exact diff_le_1

noncomputable def φ' : α → ℝ :=
  fun g ↦ (q_convergence f_pos g).choose

theorem φ'_spec (g : α) : Filter.Tendsto (fun p ↦ ((q f_pos g p) : ℝ)/(p : ℝ)) Filter.atTop (nhds (φ' f_pos g)) := by
  exact (q_convergence f_pos g).choose_spec

theorem φ'_def (g : α) {s : ℝ} (s_lim : Filter.Tendsto (fun p ↦ ((q f_pos g p) : ℝ)/(p : ℝ)) Filter.atTop (nhds s)) :
    φ' f_pos g = s := by
  have := φ'_spec f_pos g
  exact tendsto_nhds_unique this s_lim

theorem φ'_hom_case (a b : α) :
    ∀p : ℕ, q f_pos a p + q f_pos b p ≤ q f_pos (a*b) p ∧
      q f_pos (a*b) p ≤ q f_pos a p + q f_pos b p + 1 := by
  intro p
  obtain ⟨a_spec1, a_spec2⟩ := q_spec f_pos a p
  obtain ⟨b_spec1, b_spec2⟩ := q_spec f_pos b p
  obtain ab_le_ba | ba_le_ab := LinearOrder.le_total (a * b) (b * a)
  · constructor
    · have factor_le : a^p*b^p ≤ (a*b)^p := comm_factor_le_group ab_le_ba p
      have : f^(q f_pos a p) * f^(q f_pos b p) ≤ a^p * b^p := mul_le_mul' a_spec1 b_spec1
      have : f^(q f_pos a p) * f^(q f_pos b p) ≤ (a*b)^p := Preorder.le_trans _ _ _ this factor_le
      simp [←zpow_add] at this
      exact q_max_lt f_pos (a * b) p this
    · have dist_le : (b*a)^p ≤ b^p*a^p := by exact comm_dist_le_group ab_le_ba p
      have : (a*b)^p ≤ (b*a)^p := by exact comm_swap_le_group ab_le_ba p
      have prod_le : (a*b)^p ≤ b^p*a^p := by exact Preorder.le_trans _ _ _ this dist_le
      have : b^p*a^p < f ^ (q f_pos b p + 1) * f ^ (q f_pos a p + 1) :=
        Left.mul_lt_mul b_spec2 a_spec2
      simp [←zpow_add] at this
      have exp_rw : (q f_pos b p + 1) + (q f_pos a p + 1) = q f_pos a p + q f_pos b p + 2 := by
        ring
      simp [exp_rw] at this
      have : (a * b)^p < f^(q f_pos a p + q f_pos b p + 2) := lt_of_le_of_lt prod_le this
      have : q f_pos (a*b) p + 1 ≤ q f_pos a p + q f_pos b p + 2 :=
        qplus1_min_gt f_pos (a * b) p this
      have : q f_pos (a*b) p + 1 - 1 ≤ q f_pos a p + q f_pos b p + 2 - 1 :=
        Int.sub_le_sub_right this 1
      ring_nf at this
      ring_nf
      trivial
  · constructor
    · have factor_le : b^p*a^p ≤ (b*a)^p := comm_factor_le_group ba_le_ab p
      have : (b*a)^p ≤ (a*b)^p := by exact comm_swap_le_group ba_le_ab p
      have factor_le' : b^p*a^p ≤ (a*b)^p := Preorder.le_trans _ _ _ factor_le this
      have : f^(q f_pos b p) * f^(q f_pos a p) ≤ b^p * a^p := mul_le_mul' b_spec1 a_spec1
      have : f^(q f_pos b p) * f^(q f_pos a p) ≤ (a*b)^p := Preorder.le_trans _ _ _ this factor_le'
      simp [←zpow_add] at this
      have := q_max_lt f_pos (a * b) p this
      rw [←add_comm]
      trivial
    · have : a^p*b^p < f ^ (q f_pos a p + 1)*f ^ (q f_pos b p + 1) := Left.mul_lt_mul a_spec2 b_spec2
      have dist_le : (a*b)^p ≤ a^p*b^p := comm_dist_le_group ba_le_ab p
      have : (a*b)^p < f ^ (q f_pos a p + 1)*f ^ (q f_pos b p + 1) := lt_of_le_of_lt dist_le this
      simp [←zpow_add] at this
      have := qplus1_min_gt f_pos (a*b) p this
      have exp_rw : (q f_pos a p + 1) + (q f_pos b p + 1) = q f_pos a p + q f_pos b p + 2 := by
        ring
      rw [exp_rw] at this
      have : q f_pos (a*b) p + 1 - 1 ≤ q f_pos a p + q f_pos b p + 2 - 1 := Int.sub_le_sub_right this 1
      ring_nf at this
      ring_nf
      trivial

theorem φ'_hom (a b : α) : φ' f_pos (a * b) = φ' f_pos a + φ' f_pos b := by
  have sequence_le := φ'_hom_case f_pos a b
  have a_spec := φ'_spec f_pos a
  have b_spec := φ'_spec f_pos b
  have ab_spec := φ'_spec f_pos (a*b)
  have sequence_sum : Filter.Tendsto (fun p ↦ (q f_pos a p : ℝ) / (p : ℝ) + (q f_pos b p : ℝ) / p) Filter.atTop (nhds (φ' f_pos a + φ' f_pos b)) := by
    exact Filter.Tendsto.add a_spec b_spec
  have : (fun p ↦ (q f_pos a p : ℝ) / (p : ℝ) + (q f_pos b p : ℝ) / p) = (fun p ↦ ((q f_pos a p : ℝ) + (q f_pos b p : ℝ) : ℝ) / (p : ℝ)) := by
    ext z
    ring
  rw [this] at sequence_sum
  have : ∀p : ℕ, ((q f_pos a p : ℝ) + (q f_pos b p : ℝ) : ℝ) ≤ (q f_pos (a*b) p : ℝ) := by
    intro p
    norm_cast
    obtain ⟨le, _⟩ := sequence_le p
    exact le
  have (p : ℕ) (p_pos : 0 < p) : ((q f_pos a p : ℝ) + (q f_pos b p : ℝ) : ℝ) / (p : ℝ) ≤ (q f_pos (a*b) p : ℝ) / (p : ℝ) := by
    have rp_pos : (p : ℝ) > 0 := Nat.cast_pos'.mpr p_pos
    exact (div_le_div_iff_of_pos_right rp_pos).mpr (this p)
  have h1 : φ' f_pos a + φ' f_pos b ≤ φ' f_pos (a*b) := by sorry
  have h2 : φ' f_pos (a*b) ≤ φ' f_pos a + φ' f_pos b := by sorry
  have := PartialOrder.le_antisymm (a := φ' f_pos a + φ' f_pos b) (b := φ' f_pos (a*b)) h1 h2
  exact this.symm

noncomputable def φ : α →* ℝ where
  toFun := φ' f_pos
  map_one' := sorry
  map_mul' := sorry
