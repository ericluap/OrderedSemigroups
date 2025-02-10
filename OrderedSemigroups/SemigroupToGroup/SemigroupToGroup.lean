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
    ∃M : Type u, ∃_ : LinearOrderedCancelCommMonoid M, ¬has_anomalous_pair (α := M) ∧
      ∃H : Subsemigroup M, Nonempty (α ≃* H) := by
  set not_anom := not_anom_to_comm not_anomalous
    with not_anom_def
  by_cases not_one : ∀a : α, ¬(∀x : α, a*x = x)
  · set not_anom_monoid := @to_monoid α not_anom (Fact.mk not_one)
      with not_anom_monoid_def
    use (with_one α), not_anom_monoid
    constructor
    · exact not_anom_semigroup_not_anom_monoid (α := α) (not_one := Fact.mk not_one) not_anomalous
    · use without_one, iso_without_one (α := α)
      simp
  · simp at not_one
    obtain ⟨one, hone⟩ := not_one
    set not_anom_monoid := has_one_to_monoid one hone
      with not_anom_monoid_def
    use α, not_anom_monoid
    constructor
    · exact has_one_not_anom_not_anom one hone not_anomalous
    · set whole : Subsemigroup α := {
        carrier := Set.univ
        mul_mem' := by simp
      } with whole_def
      use whole
      constructor
      exact {
        toFun := fun x => ⟨x, by simp [whole_def]⟩
        invFun := fun x => x
        left_inv := by simp [Function.LeftInverse]
        right_inv := by simp [Function.RightInverse, Function.LeftInverse]
        map_mul' := by simp
      }

theorem to_arch_group (not_anomalous : ¬has_anomalous_pair (α := α)) :
    ∃G : Type v, ∃g : LinearOrderedCommGroup G, archimedean_group G ∧
      ∃H : Subgroup G, Nonempty (α ≃* H) := by
  have : is_archimedean (α := α) := not_anomalous_arch not_anomalous
  --have := @holders_theorem α _ (arch_iff_arch.mp this)
  sorry

end LinearOrderedCancelSemigroup
