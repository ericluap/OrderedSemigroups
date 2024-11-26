import OrderedSemigroups.OrderedGroup.ArchimedeanGroup

universe u

variable {α : Type u}

section Group
variable [Group α]

theorem pnat_pow_eq_nat_pow (x : α) (n : ℕ+) : x^(n.val) = x^n := by
  induction n using PNat.recOn with
  | p1 => simp
  | hp n ih =>
    simp [ppow_succ, pow_succ, ih]

theorem split_first_and_last_factor_of_product_group {a b : α} {n : ℕ} :
  (a*b)^(n+1) = a*(b*a)^n*b := by
  obtain n_eq_0 | n_gt_0 := Nat.eq_zero_or_pos n
  · simp [n_eq_0]
  · set n' : ℕ+ := ⟨n, n_gt_0⟩
    have : (a*b)^(n'+1) = a*(b*a)^n'*b := split_first_and_last_factor_of_product
    simpa [←pnat_pow_eq_nat_pow]

end Group

section LeftOrdered

variable [LeftOrderedGroup α]

theorem pos_lt_exp_lt {f : α} (f_pos : 1 < f) {a b : ℤ} (f_lt : f^a < f^b) : a < b := by
  have swap : (f^a)⁻¹ * f^a < (f^a)⁻¹ * f^b  := mul_lt_mul_left' f_lt (f ^ a)⁻¹
  simp only [inv_mul_cancel] at swap
  have : (f^a)⁻¹ = f^(-a) := by exact Eq.symm (zpow_neg f a)
  have one_lt_prod : 1 < f^(-a) * f^b := lt_of_lt_of_eq swap (congrFun (congrArg HMul.hMul this) (f ^ b))
  simp only [←zpow_add] at one_lt_prod
  have : 0 < -a + b := by
    by_contra h
    simp at h
    obtain b_eq_a | b_lt_a := h.eq_or_lt
    · simp [b_eq_a] at one_lt_prod
    · have : -a + b < 0 := by exact neg_add_neg_iff.mpr b_lt_a
      have : f ^ (-a + b) < 1 := by exact neg_exp_pos_neg f_pos this
      have : f ^ (-a + b) < f^(-a + b) := by exact gt_trans one_lt_prod this
      exact (lt_self_iff_false (f ^ (-a + b))).mp this
  exact lt_neg_add_iff_lt.mp this

theorem gt_exp (arch : archimedean_group α) (f g : α) (f_ne_one : f ≠ 1) : ∃z : ℤ, g < f^z := by
  obtain ⟨z, hz⟩ := arch f g f_ne_one
  simp at hz
  use z

instance : LeftOrderedSemigroup α where
  mul_le_mul_left _ _ a b :=  mul_le_mul_left' a b

instance PositiveCone (α : Type u) [LeftOrderedGroup α] : Subsemigroup α where
  carrier := {x : α | 1 < x}
  mul_mem' := by
    simp
    exact fun {a b} a_1 a_2 ↦ one_lt_mul' a_1 a_2

instance NegativeCone (α : Type u) [LeftOrderedGroup α] : Subsemigroup α where
  carrier := {x : α | x < 1}
  mul_mem' := by
    simp
    exact fun {a b} a_1 a_2 ↦ mul_lt_one a_1 a_2

theorem pos_neg_disjoint :
    Disjoint (SetLike.coe (PositiveCone α)) (SetLike.coe (NegativeCone α)) := by
  simp [Disjoint, PositiveCone, NegativeCone]
  intro S S_subset_pos S_subset_neg
  ext x
  constructor
  · intro x_in_S
    exact (lt_self_iff_false x).mp (gt_trans (S_subset_pos x_in_S) (S_subset_neg x_in_S))
  · intro x_in_empty
    contradiction

def normal_semigroup {α : Type u} [Group α] (x : Subsemigroup α) :=
    ∀s : x, ∀g : α, g * s * g⁻¹ ∈ x

/--
  A left ordered group whose positive cone is a normal semigroup is an ordered group.
-/
def pos_normal_ordered (pos_normal : normal_semigroup (PositiveCone α)) :
    ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c := by
  intro a b a_le_b c
  simp [normal_semigroup, PositiveCone] at pos_normal
  have : 1 ≤ a⁻¹ * b := le_inv_mul_iff_le.mpr a_le_b
  rcases this.eq_or_lt with ainv_b_eq_one | ainv_b_pos
  -- Case `a = b`
  · have : a*1 = a*(a⁻¹*b) := congrArg (HMul.hMul a) ainv_b_eq_one
    simp at this
    simp [this]
  -- Case `a < b`
  have := pos_normal (a⁻¹ * b) ainv_b_pos c⁻¹
  simp at this
  have : c * 1 < c * (c⁻¹ * (a⁻¹ * b) * c) := mul_lt_mul_left' this c
  simp [mul_one, ←mul_assoc] at this
  have : a * c < a * (a⁻¹ * b * c) := mul_lt_mul_left' this a
  simp [←mul_assoc] at this
  exact this.le

end LeftOrdered

section LeftLinearOrderedGroup

variable [LeftLinearOrderedGroup α]

theorem neg_case_left_arch_false {g h : α} (arch : archimedean_group α) (pos_g : 1 < g) (neg_h : h < 1)
    (conj_lt_one : h * g * h⁻¹ < 1) : False := by
  have pos_hinv : 1 < h⁻¹ := one_lt_inv_of_inv neg_h
  obtain ⟨z, gz_gt_hinv, z_maximum⟩ := pos_min_arch arch pos_g pos_hinv
  have hinv_lt : h⁻¹ < g⁻¹ * h⁻¹ := by
    have : h⁻¹ * (h * g * h⁻¹) < h⁻¹ * 1 := mul_lt_mul_left' conj_lt_one (h⁻¹)
    simp [mul_assoc] at this
    have : g⁻¹ * (g * h⁻¹) < g⁻¹ * h⁻¹ := mul_lt_mul_left' this g⁻¹
    simpa [mul_assoc]
  have : g⁻¹ * h⁻¹ < g⁻¹ * g^z := mul_lt_mul_left' gz_gt_hinv g⁻¹
  have hinv_lt : h⁻¹ < g⁻¹ * g^z := by exact gt_trans this hinv_lt
  have : g^z = g * g^((-1) + z) := by
    have : g^z = g^(1 + ((-1) + z)) := by simp
    have : g^(1 + ((-1) + z)) = g^(1 : ℤ) * g^((-1) + z) := by
      simp only [zpow_add g 1 (-1 + z)]
    simpa
  simp [this] at hinv_lt
  have := z_maximum (-1 + z) hinv_lt
  omega

theorem neg_case_conj_pos {g h : α} (arch : archimedean_group α) (pos_g : 1 < g) (neg_h : h < 1)
    : 1 < h * g * h⁻¹ := by
  by_contra not_pos_conj
  simp at not_pos_conj
  rcases not_pos_conj.eq_or_lt with conj_eq_one | conj_lt_one
  · have : g = 1 := by exact conj_eq_one_iff.mp conj_eq_one
    rw [this] at pos_g
    exact (lt_self_iff_false 1).mp pos_g
  exact False.elim (neg_case_left_arch_false arch pos_g neg_h conj_lt_one)

/--
  A left ordered group that is Archimedean is right ordered.
-/
theorem left_arch_ordered (arch : archimedean_group α) :
    ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c := by
  apply pos_normal_ordered
  simp [normal_semigroup, PositiveCone]
  intro g pos_g h
  -- Assume that `h * g * h⁻¹` is negative for contradiction
  by_contra not_pos_conj
  simp at not_pos_conj
  rcases not_pos_conj.eq_or_lt with conj_eq_one | conj_lt_one
  · have : g = 1 := by exact conj_eq_one_iff.mp conj_eq_one
    rw [this] at pos_g
    exact (lt_self_iff_false 1).mp pos_g
  by_cases pos_h : 1 < h
  case neg =>
    simp at pos_h
    rcases pos_h.eq_or_lt with h_eq_one | neg_h
    -- The case where `h = 1`
    · simp [h_eq_one] at *
      exact (lt_self_iff_false 1).mp (lt_imp_lt_of_le_imp_le (fun _ ↦ not_pos_conj) pos_g)
    -- The case where `h` is in the negative cone
    · exact False.elim (neg_case_left_arch_false arch pos_g neg_h conj_lt_one)
  case pos =>
    -- The case where `h` is in the positive cone
    have conjinv_pos : 1 < (h * g * h⁻¹)⁻¹ := one_lt_inv_of_inv conj_lt_one
    simp at conjinv_pos
    have hinv_neg : h⁻¹ < 1 := Left.inv_lt_one_iff.mpr pos_h
    have := neg_case_conj_pos arch conjinv_pos hinv_neg
    simp at this
    exact (lt_self_iff_false g).mp (gt_trans pos_g this)

def left_arch_ordered_group (arch : archimedean_group α) : LinearOrderedGroup α where
  mul_le_mul_right := by exact fun a b a_1 c ↦ left_arch_ordered arch a b a_1 c

end LeftLinearOrderedGroup

section LinearOrderedGroup

variable [LinearOrderedGroup α]

theorem comm_factor_le_group {a b : α} (h : a*b ≤ b*a) (n : ℕ) : a^n * b^n ≤ (a*b)^n := by
  obtain n_eq_0 | n_gt_0 := Nat.eq_zero_or_pos n
  · simp [n_eq_0]
  · set n' : ℕ+ := ⟨n, n_gt_0⟩
    have := comm_factor_le h n'
    simpa [←pnat_pow_eq_nat_pow]

theorem comm_swap_le_group {a b : α} (h : a*b ≤ b*a) (n : ℕ) : (a*b)^n ≤ (b*a)^n := pow_le_pow_left' h n

theorem comm_dist_le_group {a b : α} (h : a*b ≤ b*a) (n : ℕ) : (b*a)^n ≤ b^n * a^n := by
  obtain n_eq_0 | n_gt_0 := Nat.eq_zero_or_pos n
  · simp [n_eq_0]
  · set n' : ℕ+ := ⟨n, n_gt_0⟩
    have := comm_dist_le h n'
    simpa [←pnat_pow_eq_nat_pow]

theorem pos_exp_lt_lt {f : α} (f_pos : 1 < f) {a b : ℤ} (a_lt_b : a < b) : f^a < f^b := by
  have : 0 < b - a := Int.sub_pos_of_lt a_lt_b
  have : 1 < f ^ (b - a) := pos_exp_pos_pos f_pos this
  have : 1 < f^(b + (-a)) := this
  rw [zpow_add] at this
  have : 1*f^a < (f^b * f^(-a))*f^a := mul_lt_mul_right' this (f ^ a)
  simpa

theorem pos_exp_le_le {f : α} (f_pos : 1 < f) {a b : ℤ} (a_le_b : a ≤ b) : f^a ≤ f^b := by
  have : 0 ≤ b - a := Int.sub_nonneg_of_le a_le_b
  have : 1 ≤ f ^ (b - a) := nonneg_exp_pos_nonneg f_pos this
  have : 1 ≤ f^(b + (-a)) := this
  rw [zpow_add] at this
  have : 1*f^a ≤ (f^b * f^(-a))*f^a := mul_le_mul_right' this (f ^ a)
  simpa

theorem lt_exp (arch : archimedean_group α) (f g : α) (f_ne_one : f ≠ 1) : ∃z : ℤ, f^z < g := by
  obtain f_le_g | g_lt_f := le_or_lt f g
  · obtain f_lt_one | one_lt_f := lt_or_gt_of_ne f_ne_one
    · have : f*f < f := (mul_lt_iff_lt_one_right' f).mpr f_lt_one
      use 2
      simp [zpow_two f]
      exact mul_lt_of_le_of_lt_one f_le_g f_lt_one
    · have : f⁻¹ < f := by exact Right.inv_lt_self one_lt_f
      use -1
      simp
      exact gt_of_ge_of_gt f_le_g this
  · have : f⁻¹ < g⁻¹ := inv_lt_inv_iff.mpr g_lt_f
    have finv_ne_one : f⁻¹ ≠ 1 := inv_ne_one.mpr f_ne_one
    obtain ⟨z, hz⟩ := arch f⁻¹ g⁻¹ finv_ne_one
    simp at hz
    use z

end LinearOrderedGroup
/-
/--
  The definition of archimedean for groups and the one for semigroups are equivalent.
-/
theorem arch_group_semigroup : archimedean_group α ↔ is_archimedean (α := α) := by
  simp [archimedean_group, is_archimedean]
  constructor
  · intro arch_group a b
    rcases pos_neg_or_one a with pos_a | neg_a | one_a
-/
