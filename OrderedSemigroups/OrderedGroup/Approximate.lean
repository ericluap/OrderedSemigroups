import OrderedSemigroups.OrderedGroup.ArchimedeanGroup
import OrderedSemigroups.OrderedGroup.Convergence
import OrderedSemigroups.Basic

/-!
# Approximate

This file defines the homomorphsim from a left linear ordered group
to the real numbers by fixing an element `f` of the group
and approximating all the others with respect to it.
Most of the content of Holder's theorem is proved here.

-/


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

variable {α : Type u} [LeftLinearOrderedGroup α] (f : α)
  [arch : Fact (archimedean_group α)] [f_pos : Fact (1 < f)]

instance : LinearOrderedGroup α where
  mul_le_mul_right := by exact fun a b a_1 c ↦ left_arch_ordered arch.elim a b a_1 c

theorem approximate (g : α) (p : ℕ):
  ∃(q : ℤ), f^q ≤ g^p ∧ g^p < f^(q+1) := by
  obtain ⟨l, hl⟩ := lt_exp arch.out f (g^p) (f_pos.out.ne.symm)
  obtain ⟨u, hu⟩ := gt_exp arch.out f (g^p) (f_pos.out.ne.symm)
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
    exact (pos_lt_exp_lt f_pos.out this).le
  obtain ⟨z, z_small, z_max⟩ := bounded_above_max small_exp_nonempty small_exp_bddabove
  use z
  simp [small_exp, upperBounds] at z_small z_max
  constructor
  · trivial
  · specialize @z_max (z+1)
    rw [←not_imp_not] at z_max
    simp at z_max
    trivial

noncomputable def q (g : α) (p : ℕ) : ℤ := (approximate f g p).choose

theorem q_spec (g : α) (p : ℕ) :
  f^(q f g p) ≤ g^p ∧ g^p < f^((q f g p)+1) := by
    have := (approximate f g p).choose_spec
    simp at this
    simp [q]
    tauto

theorem q_max_lt (g : α) (p : ℕ) {t : ℤ} (ht : f^t ≤ g^p) : t ≤ q f g p := by
  have ⟨_, gp_lt_fqp1⟩ := q_spec f g p
  by_contra h
  simp at h
  have : q f g p + 1 ≤ t := h
  have lt_t : f ^ (q f g p + 1) ≤ f^t := pos_exp_le_le f_pos.out h
  have : f ^ t < f ^ (q f g p + 1) := lt_of_le_of_lt ht gp_lt_fqp1
  have : f ^ t < f ^ t := gt_of_ge_of_gt lt_t this
  order

theorem qplus1_min_gt (g : α) (p : ℕ) {t : ℤ} (ht : g^p < f^t) : q f g p + 1 ≤ t := by
  have ⟨fqp_lt_gt, _⟩ := q_spec f g p
  by_contra h
  simp at h
  have : t ≤ q f g p := (Int.add_le_add_iff_right 1).mp h
  have : f^t ≤ f^(q f g p) := pos_exp_le_le f_pos.out this
  have : g^p < f^(q f g p) := gt_of_ge_of_gt this ht
  have : g^p < g^p := gt_of_ge_of_gt fqp_lt_gt this
  order

theorem q_exp_add (g : α) (a b : ℕ) :
    f^((q f g a) + (q f g b)) ≤ g^(a + b) ∧
    g^(a+b) < f^((q f g a) + (q f g b)+2) := by
  have ⟨fqa_le_ga, ga_lt_fa1⟩ := q_spec f g a
  have ⟨fqb_le_gb, gb_lt_fb1⟩ := q_spec f g b
  constructor
  · have : (f ^ q f g a)*(f ^ q f g b) ≤ g^a*g^b :=
      mul_le_mul' fqa_le_ga fqb_le_gb
    simp [←zpow_add, ←pow_add] at this
    trivial
  · have : (g ^ a) * (g ^ b) < (f ^ (q f g a + 1)) * f ^ (q f g b + 1) :=
      Left.mul_lt_mul ga_lt_fa1 gb_lt_fb1
    simp [←zpow_add, ←pow_add] at this
    have exp_add :
        q f g a + 1 + (q f g b + 1) = q f g a + q f g b + 2 := by
      ring
    simp [exp_add] at this
    trivial

theorem q_convergence (g : α) :
  ∃r : ℝ, Filter.Tendsto (fun p ↦ ((q f g p) : ℝ)/(p : ℝ)) Filter.atTop (nhds r) := by
  apply sequence_convergence (C := 1)
  intro m n
  obtain ⟨fab_le_gab, gab_lt_abplus2⟩ := q_exp_add f g m n
  have qmplusqn_le_qmplusn:= q_max_lt f g (m+n) fab_le_gab
  have qmplusn_le_qmplusqnplus2 := qplus1_min_gt f g (m+n) gab_lt_abplus2
  have := Int.sub_le_sub_right qmplusn_le_qmplusqnplus2 1
  simp at this
  ring_nf at this
  have diff_le_1: q f g (m+n) - q f g m - q f g n ≤ 1 := by
    simp
    rw [add_assoc, add_comm (q f g n), ←add_assoc]
    trivial
  have diff_ge_0 : 0 ≤ q f g (m+n) - q f g m - q f g n := by
    simp
    have := Int.sub_le_sub_right qmplusqn_le_qmplusn (q f g m)
    simpa
  norm_cast
  have := abs_of_nonneg diff_ge_0
  rw [this]
  exact diff_le_1

noncomputable def φ' : α → ℝ :=
  fun g ↦ (q_convergence f g).choose

theorem φ'_spec (g : α) : Filter.Tendsto (fun p ↦ ((q f g p) : ℝ)/(p : ℝ)) Filter.atTop (nhds (φ' f g)) := by
  exact (q_convergence f g).choose_spec

theorem φ'_def (g : α) {s : ℝ} (s_lim : Filter.Tendsto (fun p ↦ ((q f g p) : ℝ)/(p : ℝ)) Filter.atTop (nhds s)) :
    φ' f g = s := by
  have := φ'_spec f g
  exact tendsto_nhds_unique this s_lim

theorem φ'_hom_case (a b : α) :
    ∀p : ℕ, q f a p + q f b p ≤ q f (a*b) p ∧
      q f (a*b) p ≤ q f a p + q f b p + 1 := by
  intro p
  obtain ⟨a_spec1, a_spec2⟩ := q_spec f a p
  obtain ⟨b_spec1, b_spec2⟩ := q_spec f b p
  obtain ab_le_ba | ba_le_ab := LinearOrder.le_total (a * b) (b * a)
  · constructor
    · have factor_le : a^p*b^p ≤ (a*b)^p := comm_factor_le_group ab_le_ba p
      have : f^(q f a p) * f^(q f b p) ≤ a^p * b^p := mul_le_mul' a_spec1 b_spec1
      have : f^(q f a p) * f^(q f b p) ≤ (a*b)^p := Preorder.le_trans _ _ _ this factor_le
      simp [←zpow_add] at this
      exact q_max_lt f (a * b) p this
    · have dist_le : (b*a)^p ≤ b^p*a^p := by exact comm_dist_le_group ab_le_ba p
      have : (a*b)^p ≤ (b*a)^p := by exact comm_swap_le_group ab_le_ba p
      have prod_le : (a*b)^p ≤ b^p*a^p := by exact Preorder.le_trans _ _ _ this dist_le
      have : b^p*a^p < f ^ (q f b p + 1) * f ^ (q f a p + 1) :=
        Left.mul_lt_mul b_spec2 a_spec2
      simp [←zpow_add] at this
      have exp_rw : (q f b p + 1) + (q f a p + 1) = q f a p + q f b p + 2 := by
        ring
      simp [exp_rw] at this
      have : (a * b)^p < f^(q f a p + q f b p + 2) := lt_of_le_of_lt prod_le this
      have : q f (a*b) p + 1 ≤ q f a p + q f b p + 2 :=
        qplus1_min_gt f (a * b) p this
      have : q f (a*b) p + 1 - 1 ≤ q f a p + q f b p + 2 - 1 :=
        Int.sub_le_sub_right this 1
      ring_nf at this
      ring_nf
      trivial
  · constructor
    · have factor_le : b^p*a^p ≤ (b*a)^p := comm_factor_le_group ba_le_ab p
      have : (b*a)^p ≤ (a*b)^p := by exact comm_swap_le_group ba_le_ab p
      have factor_le' : b^p*a^p ≤ (a*b)^p := Preorder.le_trans _ _ _ factor_le this
      have : f^(q f b p) * f^(q f a p) ≤ b^p * a^p := mul_le_mul' b_spec1 a_spec1
      have : f^(q f b p) * f^(q f a p) ≤ (a*b)^p := Preorder.le_trans _ _ _ this factor_le'
      simp [←zpow_add] at this
      have := q_max_lt f (a * b) p this
      rw [←add_comm]
      trivial
    · have : a^p*b^p < f ^ (q f a p + 1)*f ^ (q f b p + 1) := Left.mul_lt_mul a_spec2 b_spec2
      have dist_le : (a*b)^p ≤ a^p*b^p := comm_dist_le_group ba_le_ab p
      have : (a*b)^p < f ^ (q f a p + 1)*f ^ (q f b p + 1) := lt_of_le_of_lt dist_le this
      simp [←zpow_add] at this
      have := qplus1_min_gt f (a*b) p this
      have exp_rw : (q f a p + 1) + (q f b p + 1) = q f a p + q f b p + 2 := by
        ring
      rw [exp_rw] at this
      have : q f (a*b) p + 1 - 1 ≤ q f a p + q f b p + 2 - 1 := Int.sub_le_sub_right this 1
      ring_nf at this
      ring_nf
      trivial

theorem φ'_hom (a b : α) : φ' f (a * b) = φ' f a + φ' f b := by
  have sequence_le := φ'_hom_case f a b
  have a_spec := φ'_spec f a
  have b_spec := φ'_spec f b
  have ab_spec := φ'_spec f (a*b)

  have sequence_sum : Filter.Tendsto (fun p ↦ (q f a p : ℝ) / (p : ℝ) + (q f b p : ℝ) / p) Filter.atTop (nhds (φ' f a + φ' f b)) := by
    exact Filter.Tendsto.add a_spec b_spec
  have : (fun p ↦ (q f a p : ℝ) / (p : ℝ) + (q f b p : ℝ) / p) = (fun p ↦ ((q f a p : ℝ) + (q f b p : ℝ) : ℝ) / (p : ℝ)) := by
    ext z
    ring
  rw [this] at sequence_sum

  have : ∀p : ℕ, ((q f a p : ℝ) + (q f b p : ℝ) : ℝ) ≤ (q f (a*b) p : ℝ) := by
    intro p
    norm_cast
    obtain ⟨le, _⟩ := sequence_le p
    exact le
  have (p : ℕ) (p_pos : 0 < p) : ((q f a p : ℝ) + (q f b p : ℝ) : ℝ) / (p : ℝ) ≤ (q f (a*b) p : ℝ) / (p : ℝ) := by
    have rp_pos : (p : ℝ) > 0 := Nat.cast_pos'.mpr p_pos
    exact (div_le_div_iff_of_pos_right rp_pos).mpr (this p)
  have : ∀ᶠ p in Filter.atTop, ((q f a p : ℝ) + (q f b p : ℝ) : ℝ) / (p : ℝ) ≤ (q f (a*b) p : ℝ) / (p : ℝ) := by
    simp
    use 1
    exact fun b a ↦ this b a

  have h1 := le_of_tendsto_of_tendsto sequence_sum ab_spec this

  have h2 : φ' f (a*b) ≤ φ' f a + φ' f b := by
    have : Filter.Tendsto (fun x : ℕ => 1 / (x : ℝ)) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inverse_atTop_nhds_zero_nat
    have convergence : Filter.Tendsto (fun p ↦ ((q f a p) + (q f b p)) / (p : ℝ) + 1 / (p : ℝ)) Filter.atTop (nhds (φ' f a + φ' f b + 0)) := by
        apply Filter.Tendsto.add
        <;> trivial
    have : (fun p ↦ ((q f a p) + (q f b p)) / (p : ℝ) + 1 / (p : ℝ)) = (fun p ↦ ((q f a p) + (q f b p) + 1) / (p : ℝ)) := by
      field_simp
    rw [this] at convergence
    simp at convergence

    have : ∀p : ℕ, (q f (a*b) p : ℝ) ≤ q f a p + q f b p + 1 := by
      intro p
      norm_cast
      obtain ⟨_, le⟩ := sequence_le p
      exact le
    have (p : ℕ) (p_pos : 0 < p) : (q f (a*b) p : ℝ) / (p : ℝ) ≤ (q f a p + q f b p + 1) / (p : ℝ) := by
      have rp_pos : (p : ℝ) > 0 := Nat.cast_pos'.mpr p_pos
      exact (div_le_div_iff_of_pos_right rp_pos).mpr (this p)
    have : ∀ᶠ p in Filter.atTop, (q f (a*b) p : ℝ) / (p : ℝ) ≤ (q f a p + q f b p + 1) / (p : ℝ) := by
      simp
      use 1
      exact fun b a ↦ this b a
    exact le_of_tendsto_of_tendsto ab_spec convergence this
  have := PartialOrder.le_antisymm (a := φ' f a + φ' f b) (b := φ' f (a*b)) h1 h2
  exact this.symm

noncomputable def φ : α →* (Multiplicative ℝ) := MonoidHom.mk' (φ' f) (φ'_hom f)

theorem order_preserving_φ {a b : α} (a_le_b : a ≤ b) : (φ f a) ≤ (φ f b) := by
  have (p : ℕ) : (q f a p : ℝ) ≤ q f b p := by
    norm_cast
    apply q_max_lt
    obtain ⟨le, _⟩ := q_spec f a p
    have : a^p ≤ b^p := pow_le_pow_left' a_le_b p
    order
  have (p : ℕ) (p_pos : 0 < p) : (q f a p)/(p : ℝ) ≤ (q f b p)/(p : ℝ) := by
    have rp_pos : 0 < (p : ℝ) := Nat.cast_pos'.mpr p_pos
    exact (div_le_div_iff_of_pos_right rp_pos).mpr (this p)
  have : ∀ᶠ p in Filter.atTop, (q f a p)/(p : ℝ) ≤ (q f b p)/(p : ℝ) := by
    simp
    use 1
    intro b one_le_b
    exact this b one_le_b
  have a_spec := φ'_spec f a
  have b_spec := φ'_spec f b
  have := le_of_tendsto_of_tendsto a_spec b_spec this
  exact this

theorem f_maps_one_φ : (φ f) f = (1 : ℝ) := by
  have p_le (p : ℕ) : (p : ℤ) ≤ q f f p := q_max_lt f f p (t := p) (by simp)
  have p_ge (p : ℕ) : q f f p ≤ (p : ℤ) := by
    have one_lt_f := f_pos.out
    have lt : 1*f^p < f*f^p := mul_lt_mul_right' one_lt_f (f ^ p)
    simp only [one_mul] at lt
    have : f * f^p = f^(p+1) := (pow_succ' f p).symm
    rw [this] at lt
    have := qplus1_min_gt f f p (t := p+1) (by norm_cast)
    simp at this
    trivial
  have (p : ℕ) : q f f p = p := (Int.le_antisymm (p_le p) (p_ge p)).symm
  have : ∀ᶠ p in Filter.atTop, (q f f p)/(p : ℝ) = 1 := by
    simp
    use 1
    intro b one_le_b
    simp [this]
    field_simp
  have eventually_one : (fun p ↦ ((q f f p) : ℝ)/(p : ℝ)) =ᶠ[Filter.atTop] 1 := this
  have : Filter.Tendsto (fun p ↦ ((q f f p) : ℝ)/(p : ℝ)) Filter.atTop (nhds 1) := by
    apply Filter.Tendsto.congr' (f₁ := 1)
    exact eventually_one.symm
    exact tendsto_const_nhds
  exact φ'_def f f this

theorem injective_φ : Function.Injective (φ f) := by
  rw [injective_iff_map_eq_one]
  intro a a_image_one
  by_contra h
  obtain ⟨n, hn⟩ := arch.out a f h
  have zero_le_one : (0 : ℝ) ≥ 1 := by
    calc (0 : ℝ)
    _ = (φ f) a := a_image_one.symm
    _ = ((φ f) a)^n := by
      simp [a_image_one]
    _ = (φ f) (a ^ n) := (MonoidHom.map_zpow (φ f) a n).symm
    _ ≥ (φ f) f := order_preserving_φ f hn.le
    _ = (1 : ℝ) := f_maps_one_φ f
  have zero_lt_one : (0 : ℝ) < 1 := Real.zero_lt_one
  order

theorem strict_order_preserving_φ {a b : α}: a ≤ b ↔ (φ f a) ≤ (φ f b) := by
  constructor
  · exact fun a_1 ↦ order_preserving_φ f a_1
  · intro φa_le_φb
    by_contra h
    simp at h
    have := order_preserving_φ f h.le
    have : (φ f) a = (φ f) b := PartialOrder.le_antisymm _ _ φa_le_φb this
    have := injective_φ f this
    order
