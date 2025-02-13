import OrderedSemigroups.SemigroupToGroup.SemigroupToGroup

/-!
# Holder's Theorem for Semigroups

This file containes the proof of Holder's theorem for semigroups and
some variants of it.

-/

universe u
variable {α : Type u}

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelSemigroup α]

/--
  If `α` is a linear ordered cancel semigroup that does not have anomalous pairs,
  then `α` is monoid order isomorphic to a subsemigroup of `ℝ`.
-/
theorem holder_not_anom (not_anom : ¬has_anomalous_pair (α := α)) :
    ∃G : Subsemigroup (Multiplicative ℝ), Nonempty (α ≃*o G) := by
  obtain ⟨G, _, arch, subH, ⟨iso⟩⟩ := to_arch_group not_anom
  obtain ⟨subR, ⟨subR_iso⟩⟩ := holders_theorem arch
  obtain ⟨sub, x⟩ :=
    compose_subsemigroup' (G := (Multiplicative ℝ)) (M := G)
      (G' := subR) subR_iso iso
  use sub

/--
    If `α` is a linear ordered cancel semigroup that has large differences,
  then `α` is monoid order isomorphic to a subsemigroup of `ℝ`.
-/
theorem holder_large_differences (has_large_diff : has_large_differences (α := α)) :
    ∃G : Subsemigroup (Multiplicative ℝ), Nonempty (α ≃*o G) := by
  apply holder_not_anom
  exact not_anomalous_iff_large_difference.mpr has_large_diff

/--
  If `α` is a linear ordered cancel semigroup where all elements are
  nonnegative or all are nonpositive, `α` is archimedean, and it has differences
  (i.e. if `x < y` then there exists `z` such that `x*z = y`), then
  `α` is monoid order isomoprhic to a subsemigroup of `ℝ`.
-/
theorem holder_sign_arch_differences
    (sign : ∀x y : α, is_one x ∨ is_one y ∨ same_sign x y)
    (arch : is_archimedean (α := α))
    (differences : ∀x y : α, x < y → ∃z : α, x * z = y) :
    ∃G : Subsemigroup (Multiplicative ℝ), Nonempty (α ≃*o G) := by
  apply holder_large_differences
  exact same_sign_differences_and_arch_to_large_difference sign arch differences
