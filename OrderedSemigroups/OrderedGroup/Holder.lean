import OrderedSemigroups.OrderedGroup.Approximate

universe u
variable {α : Type u}

/--
  Every left linear ordered group that is Archimedean
  is monoid order isomorphic to a subgroup of `ℝ`.
-/
theorem holders_theorem [LeftLinearOrderedGroup α] (arch : archimedean_group α) :
    ∃G : Subgroup (Multiplicative ℝ), Nonempty (α ≃*o G) := by
  by_cases h : ∃f : α, 1 < f
  · obtain ⟨f, f_pos⟩ := h
    set φ := @φ _ _ f (Fact.mk arch) (Fact.mk f_pos) with φ_def
    use (MonoidHom.range φ)
    rw [←exists_true_iff_nonempty]
    set φ' : α → (MonoidHom.range φ) := fun a ↦ ⟨φ a, by simp⟩
    have φ'_surj : Function.Surjective φ' := by
      simp [Function.Surjective]
      intro a x h
      use x
      simp [φ', h]
    have φ'_inj : Function.Injective φ' := by
      simp [φ', Function.Injective]
      intro a b hab
      have : Function.Injective φ := @injective_φ _ _ f (Fact.mk arch) (Fact.mk f_pos)
      exact this hab
    use {
      toFun := φ'
      invFun := φ'.invFun
      left_inv := by exact Function.leftInverse_invFun φ'_inj
      right_inv := Function.rightInverse_invFun φ'_surj
      map_mul' := by simp [φ']
      map_le_map_iff' := by
        simp [φ']
        exact fun {a b} ↦ Iff.symm (@strict_order_preserving_φ _ _ f (Fact.mk arch) (Fact.mk f_pos) a b)
    }
  · simp at h
    by_cases not_one : ∃a : α, a ≠ 1
    · obtain ⟨a, ha⟩ := not_one
      simp at ha
      obtain a_lt_one | a_eq_one | one_lt_a := lt_trichotomy a 1
      · have : 1 < a⁻¹ := by exact one_lt_inv_of_inv a_lt_one
        have : 1 < 1 := by exact lt_imp_lt_of_le_imp_le (fun a_1 ↦ h a⁻¹) this
        exact False.elim ((lt_self_iff_false 1).mp this)
      · contradiction
      · have : 1 < 1 := by exact lt_imp_lt_of_le_imp_le (fun a_1 ↦ h a) one_lt_a
        exact False.elim ((lt_self_iff_false 1).mp this)
    · simp at not_one
      use ⊥
      rw [←exists_true_iff_nonempty]
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
