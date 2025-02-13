import OrderedSemigroups.OrderedGroup.Approximate

/-!
# Holder's Theorem for Groups

This file contains the proof of Holder's theorem for groups.

-/

universe u
variable {α : Type u}

/--
  Every left linear ordered group that is Archimedean
  is monoid order isomorphic to a subgroup of `ℝ`.
-/
theorem holders_theorem [LeftLinearOrderedGroup α] (arch : archimedean_group α) :
    ∃G : Subgroup (Multiplicative ℝ), Nonempty (α ≃*o G) := by
  by_cases h : ∃f : α, 1 < f
  -- We have an element `f` to approximate with
  · obtain ⟨f, f_pos⟩ := h
    -- Define `φ` to be the map from `α` to `ℝ` by approximating each element with `f`
    set φ := @φ _ _ f (Fact.mk arch) (Fact.mk f_pos) with φ_def
    use (MonoidHom.range φ)
    rw [←exists_true_iff_nonempty]
    -- `φ'` is the restriction of `φ` to its range
    set φ' : α → (MonoidHom.range φ) := fun a ↦ ⟨φ a, by simp⟩
    -- `φ'` is surjective (because we restricted to its range)
    have φ'_surj : Function.Surjective φ' := by
      simp [Function.Surjective]
      intro a x h
      use x
      simp [φ', h]
    -- `φ'` is injective
    have φ'_inj : Function.Injective φ' := by
      simp [φ', Function.Injective]
      intro a b hab
      have : Function.Injective φ := @injective_φ _ _ f (Fact.mk arch) (Fact.mk f_pos)
      exact this hab
    -- Thus, `φ'` witnesses the monoid order isomorphism to a subgroup of `ℝ`
    use {
      toFun := φ'
      invFun := φ'.invFun
      left_inv := by exact Function.leftInverse_invFun φ'_inj
      right_inv := Function.rightInverse_invFun φ'_surj
      map_mul' := by simp [φ']
      map_le_map_iff' := by
        simp [φ']
        exact fun {a b} ↦ (@strict_order_preserving_φ _ _ f (Fact.mk arch) (Fact.mk f_pos) a b).symm
    }
  -- If there is no positive element to approximate with, the group `α` is trivial.
  · simp at h
    by_cases not_one : ∃a : α, a ≠ 1
    -- If `α` is not trivial then we have a contradiction
    · obtain ⟨a, ha⟩ := not_one
      simp at ha
      obtain a_lt_one | a_eq_one | one_lt_a := lt_trichotomy a 1
      · have : 1 < a⁻¹ := by exact one_lt_inv_of_inv a_lt_one
        have : 1 < 1 := by exact lt_imp_lt_of_le_imp_le (fun a_1 ↦ h a⁻¹) this
        exact False.elim ((lt_self_iff_false 1).mp this)
      · contradiction
      · have : 1 < 1 := by exact lt_imp_lt_of_le_imp_le (fun a_1 ↦ h a) one_lt_a
        exact False.elim ((lt_self_iff_false 1).mp this)
    -- So `α` is trivial
    · simp at not_one
      use ⊥
      rw [←exists_true_iff_nonempty]
      -- The isomorphism showing that a trivial group is monoid order isomorphic to a subgroup of `ℝ`
      use {
        toFun := fun a ↦ 1
        invFun := fun a ↦ 1
        left_inv := by simp [Function.LeftInverse, not_one]
        right_inv := by
          simp [Function.RightInverse, Function.LeftInverse]
          intro a ha
          simp [ha]
          rfl
        map_mul' := by simp
        map_le_map_iff' := by simp [not_one]
      }
