import OrderedSemigroups.SemigroupToGroup.SemigroupToGroup

universe u
variable {α : Type u}

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelSemigroup α]

instance {G : Type*} [LinearOrderedCommGroup G] : Group G := inferInstance

theorem holder_not_anom (not_anom : ¬has_anomalous_pair (α := α)) :
    ∃G : Subsemigroup (Multiplicative ℝ), Nonempty (α ≃*o G) := by
  obtain ⟨G, _, arch, subH, ⟨iso⟩⟩ := to_arch_group not_anom
  obtain ⟨subR, ⟨subR_iso⟩⟩ := holders_theorem arch
  obtain ⟨sub, x⟩ :=
    compose_subsemigroup' (G := (Multiplicative ℝ)) (M := G)
      (G' := subR) subR_iso iso
  use sub
  sorry
  --exact x
