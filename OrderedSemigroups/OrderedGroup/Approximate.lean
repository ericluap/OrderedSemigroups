import OrderedSemigroups.OrderedGroup.Basic

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

variable {α : Type u} [LeftLinearOrderedGroup α] (arch : archimedean_group α) (f : α) (f_pos : 1 < f)

include f_pos arch in
theorem approximate (g : α) (p : ℕ):
  ∃(q : ℤ), f^q ≤ g^p ∧ g^p < f^(q+1) := by
  obtain ⟨l, hl⟩ := @lt_exp α (left_arch_ordered_group arch) arch f (g^p) (f_pos.ne.symm)
  obtain ⟨u, hu⟩ := gt_exp arch f (g^p) (f_pos.ne.symm)
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

noncomputable def q (g : α) (p : ℕ): ℤ := (approximate arch f f_pos g p).choose

theorem q_spec (g : α) (p : ℕ):
  f^(q arch f f_pos g p) ≤ g^p ∧ g^p < f^((q arch f f_pos g p)+1) := by
    have := (approximate arch f f_pos g p).choose_spec
    simp at this
    simp [q]
    tauto

theorem q_convergence (g : α) :
  ∃r : ℝ, Filter.Tendsto (fun p ↦ ((q arch f f_pos g p) : ℝ)/(p : ℝ)) Filter.atTop (nhds r) := by sorry

noncomputable def φ : α → ℝ :=
  fun g ↦ (q_convergence arch f f_pos g).choose
