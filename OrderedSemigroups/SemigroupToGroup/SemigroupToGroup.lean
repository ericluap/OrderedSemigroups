import OrderedSemigroups.SemigroupToGroup.SemigroupToMonoid
import OrderedSemigroups.SemigroupToGroup.MonoidToGroup
import OrderedSemigroups.OrderedGroup.ArchimedeanGroup
import OrderedSemigroups.OrderedGroup.Holder
import OrderedSemigroups.SemigroupToGroup.Basic

/-!
# Semigroup to Group

This file proves that for a suitable semigroup `α`,
there exists a larger Archimedean group containing `α`.

-/

universe u
variable {α : Type u}
section LinearOrderedCancelSemigroup
variable [Semigroup α] [LinearOrder α] [IsOrderedCancelSemigroup α]
  [Pow α ℕ+] [PNatPowAssoc α]

def not_anom_to_comm (not_anomalous : ¬has_anomalous_pair (α := α)) :
    CommSemigroup α where
  mul_comm a b := not_anomalous_pair_commutative not_anomalous a b

/--
  If `α` is a linear ordered cancel semigroup that does not have anomalous pairs,
  then there exists a linear ordered cancel commutative monoid `M` that does not
  have anomalous pairs and such that `α` is isomorphic to some subsemigroup of `M`.
-/
theorem to_not_anom_monoid (not_anomalous : ¬has_anomalous_pair (α := α)) :
    ∃M : Type u, ∃(_ : CommMonoid M) (_ : LinearOrder M)
    (_ : IsOrderedCancelMonoid M), ¬has_anomalous_pair (α := M) ∧
      ∃H : Subsemigroup M, Nonempty (α ≃*o H) := by
  set not_anom := not_anom_to_comm not_anomalous
    with not_anom_def
  by_cases not_one : ∀a : α, ¬(∀x : α, a*x = x)
  · use (WithOne α), inferInstance
    use @withOne_linearOrder _ not_anom _ _ ⟨not_one⟩
    use @withOne_orderedCancelMonoid _ not_anom _ _ ⟨not_one⟩
    constructor
    · exact not_anom_semigroup_not_anom_monoid
        (not_one := Fact.mk not_one) not_anomalous
    · use without_one α, iso_without_one (α := α)
      intro a b
      rfl
  · simp at not_one
    set commMonoid := @has_one_commMonoid _ _ _ _ ⟨not_one⟩
    use α, commMonoid, inferInstance, inferInstance
    constructor
    · simp only [not_exists, not_forall, gt_iff_lt,
        not_or, not_and, not_lt] at not_anomalous ⊢
      unfold_projs at not_anomalous ⊢
      simp only [monoid_pnat_pow_eq_pnat_pow, Nat.zero_eq, Nat.lt_eq,
        Nat.add_eq, PNat.mk_coe] at not_anomalous
      exact not_anomalous
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
        map_le_map_iff' := by simp
      }

omit [IsOrderedCancelSemigroup α] [Pow α ℕ+] [PNatPowAssoc α] in
/--
  If `α` is isomorphic to a subsemigroup of `M` and
  `M` is isomorphic to a submonoid of `G`, then
  `α` is isomorphic to a subsemigroup of `G`.
-/
theorem compose_subsemigroup {G M : Type u} [Monoid G] [Monoid M]
    [Preorder G] [Preorder M]
    {G' : Submonoid G} {M' : Subsemigroup M} (f : M ≃*o G') (g : α ≃*o M') :
    ∃H : Subsemigroup G, Nonempty (α ≃*o H) := by
  set α_to_group : α →ₙ* G := {
    toFun x := f (g x).val
    map_mul' := by simp
  } with α_to_group_def
  use α_to_group.srange
  constructor
  exact {
    toFun := fun x => ⟨α_to_group x, by use x⟩
    invFun := fun x => (Subtype.coe_prop x).choose
    left_inv := by
      simp [Function.LeftInverse]
      intro x
      set img : α_to_group.srange := ⟨α_to_group x, by simp⟩
      have inv := (Subtype.coe_prop img).choose_spec
      simp only [α_to_group, img, MulHom.coe_mk, Subtype.val_inj] at inv
      apply MulEquiv.injective at inv
      simp only [Subtype.val_inj] at inv
      apply MulEquiv.injective at inv
      convert inv
      simp [α_to_group]
    right_inv := by
      simp [Function.RightInverse, Function.LeftInverse]
      intro x y hyx
      set img : α_to_group.srange := ⟨α_to_group y, by simp⟩
      have inv := (Subtype.coe_prop img).choose_spec
      convert inv
      <;> simp [img, hyx]
    map_mul' := by
      simp [α_to_group]
    map_le_map_iff' := by simp [α_to_group]
  }

omit [IsOrderedCancelSemigroup α] [Pow α ℕ+] [PNatPowAssoc α] in
/--
  If `α` is isomorphic to a subsemigroup of `M` and
  `M` is isomorphic to a subgroup of `G`, then
  `α` is isomorphic to a subsemigroup of `G`.
-/
theorem compose_subsemigroup' {G : Type*} {M : Type*} [Group G] [Group M]
    [Preorder G] [Preorder M]
    {G' : Subgroup G} {M' : Subsemigroup M} (f : M ≃*o G') (g : α ≃*o M') :
    ∃H : Subsemigroup G, Nonempty (α ≃*o H) := by
  set α_to_group : α →ₙ* G := {
    toFun x := f (g x).val
    map_mul' := by simp
  } with α_to_group_def
  use α_to_group.srange
  constructor
  exact {
    toFun := fun x => ⟨α_to_group x, by use x⟩
    invFun := fun x => (Subtype.coe_prop x).choose
    left_inv := by
      simp [Function.LeftInverse]
      intro x
      set img : α_to_group.srange := ⟨α_to_group x, by simp⟩
      have inv := (Subtype.coe_prop img).choose_spec
      simp only [α_to_group, img, MulHom.coe_mk, Subtype.val_inj] at inv
      apply MulEquiv.injective at inv
      simp only [Subtype.val_inj] at inv
      apply MulEquiv.injective at inv
      convert inv
      simp [α_to_group]
    right_inv := by
      simp [Function.RightInverse, Function.LeftInverse]
      intro x y hyx
      set img : α_to_group.srange := ⟨α_to_group y, by simp⟩
      have inv := (Subtype.coe_prop img).choose_spec
      convert inv
      <;> simp [img, hyx]
    map_mul' := by
      simp [α_to_group]
    map_le_map_iff' := by simp [α_to_group]
  }

/--
  If `α` is a linear ordered cancel semigroup that does not have anomalous pairs,
  then there exists a linear ordered commutative group `G` that is Archimedean
  and such that `α` is isomorphic to some subsemigroup of `G`.
-/
theorem to_arch_group (not_anomalous : ¬has_anomalous_pair (α := α)) :
    ∃G : Type u, ∃(_ : CommGroup G) (_ : LinearOrder G) (_ : IsOrderedMonoid G),
      archimedean_group G ∧ ∃H : Subsemigroup G, Nonempty (α ≃*o H) := by
  obtain ⟨M, _, _, _, not_anomalous, ⟨subsemi_H, ⟨iso⟩⟩⟩ :=
    to_not_anom_monoid not_anomalous
  use (with_division M), inferInstance, inferInstance, inferInstance
  constructor
  · exact not_anom_to_arch not_anomalous
  · exact compose_subsemigroup iso_over_one iso

end LinearOrderedCancelSemigroup
