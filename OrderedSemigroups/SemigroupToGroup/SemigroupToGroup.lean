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

--set_option pp.all true in
theorem to_not_anom_monoid (not_anomalous : ¬has_anomalous_pair (α := α)) :
    ∃M : Type u, ∃m : LinearOrderedCancelCommMonoid M, ¬has_anomalous_pair (α := M) ∧
      ∃H : Subsemigroup M, Nonempty (α ≃* H) := by
  set not_anom := not_anom_to_comm not_anomalous
    with not_anom_def
  have not_anom2 : ¬@has_anomalous_pair α
      (@OrderedSemigroup.toLeftOrderedSemigroup α
        (@LinearOrderedSemigroup.toOrderedSemigroup α
          (@instLinearOrderedSemigroupOfLinearOrderedCancelSemigroup α
            instLinearOrderedCancelSemigroupOfLinearOrderedCancelCommSemigroup)))
      := by
    simp at not_anomalous ⊢
    tauto
  by_cases not_one : ∀a : α, ¬(∀x : α, a*x = x)
  ·
    have := @to_monoid α not_anom (Fact.mk not_one)
    use (with_one α), this
    constructor
    ·
      have := not_anom_semigroup_not_anom_monoid (α := α) (not_one := Fact.mk not_one) not_anom2
      convert this
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
