import OrderedSemigroups.SemigroupToGroup.SemigroupToMonoid
import OrderedSemigroups.SemigroupToGroup.MonoidToGroup
import OrderedSemigroups.OrderedGroup.ArchimedeanGroup
import OrderedSemigroups.OrderedGroup.Holder
import OrderedSemigroups.SemigroupToGroup.Basic

universe u v
variable {α : Type u}

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelSemigroup α]

def not_anom_to_comm (not_anomalous : ¬has_anomalous_pair (α := α)) :
    LinearOrderedCancelCommSemigroup α where
  mul_comm a b := not_anomalous_pair_commutative not_anomalous a b

theorem to_not_anom_monoid (not_anomalous : ¬has_anomalous_pair (α := α)) :
    ∃M : Type u, ∃m : LinearOrderedCancelCommMonoid M, ¬has_anomalous_pair (α := M) ∧
      ∃H : Subsemigroup M, Nonempty (α ≃* H) := by
  have := not_anom_to_comm not_anomalous
  by_cases not_one : ∀a : α, ¬(∀x : α, a*x = x)
  ·
    have := @to_monoid α this (Fact.mk not_one)
    use (with_one α), this
    constructor
    /-· exact @not_anom_semigroup_not_anom_monoid α _ (Fact.mk not_one)
        (by
          simp_all
          intro x y
          obtain ⟨z, ⟨l, r⟩⟩ := not_anomalous x y
          use z
          constructor
          · intro t
            unfold_projs
            simp
            unfold LT.lt
            unfold_projs
            simp


        )-/
    sorry
    sorry
  sorry

theorem to_arch_group (not_anomalous : ¬has_anomalous_pair (α := α)) :
    ∃G : Type v, ∃g : LinearOrderedCommGroup G, archimedean_group G ∧
      ∃H : Subgroup G, Nonempty (α ≃* H) := by
  have : is_archimedean (α := α) := not_anomalous_arch not_anomalous
  --have := @holders_theorem α _ (arch_iff_arch.mp this)
  sorry

end LinearOrderedCancelSemigroup
