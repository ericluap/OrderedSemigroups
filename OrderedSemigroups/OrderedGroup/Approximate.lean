import OrderedSemigroups.OrderedGroup.Basic

universe u

variable {α : Type u}
  [LeftLinearOrderedGroup α]

theorem approximate (arch : archimedean_group α) (f g : α) (p : ℕ):
  ∃!(q : ℤ), f^q ≤ g^p ∧ g^p < f^(q+1) := sorry

noncomputable def q (arch : archimedean_group α) (f g : α) (p : ℕ): ℤ := (approximate arch f g p).choose

theorem q_spec (arch : archimedean_group α) (f g : α) (p : ℕ):
  f^(q arch f g p) ≤ g^p ∧ g^p < f^((q arch f g p)+1) := by
    have := (approximate arch f g p).choose_spec
    simp at this
    simp [q]
    tauto

theorem q_convergence (arch : archimedean_group α) (f g : α) :
  ∃r : ℝ, Filter.Tendsto (fun p ↦ ((q arch f g p) : ℝ)/(p : ℝ)) Filter.atTop (nhds r) := by sorry

noncomputable def φ (arch : archimedean_group α) (f : α) : α → ℝ :=
  fun g ↦ (q_convergence arch f g).choose
