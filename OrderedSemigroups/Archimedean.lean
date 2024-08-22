import OrderedSemigroups.Sign

/-!
# Archimedean Ordered Semigroups and Anomalous Pairs

This file defines Archimedean ordered semigroups and anomalous pairs
and proves theorems about how they interact.

-/

universe u

variable {α : Type u}

section OrderedSemigroup
variable [OrderedSemigroup α]

/-- `a` is Archimedean with respect to `b` if there exists an `N : ℕ+` such that
for all `n ≥ N`, either `b` is positive and `b < a^n` or `b` is negative and `a^n < b`. -/
abbrev is_archimedean_wrt (a b : α) :=
  ∃N : ℕ+, ∀n : ℕ+, n ≥ N → (is_positive b ∧ b < a^n) ∨ (is_negative b ∧ a^n < b)

/-- A pair of elements `a` and `b` form an anomalous pair if for all `n : ℕ+`,
either `a^n < b^n` and `b^n < a^(n+1)` or `a^n > b^n` and `b^n > a^(n+1)`. -/
abbrev anomalous_pair (a b : α) := ∀n : ℕ+, (a^n < b^n ∧ b^n < a^(n+1)) ∨ (a^n > b^n ∧ b^n > a^(n+1))

/-- An ordered semigroup has an anomalous pair if there exist elements `a` and `b` such that
`a` and `b` form an anomalous pair. -/
abbrev has_anomalous_pair := ∃a b : α, anomalous_pair a b

/-- An ordered semigroup is Archimedean if for all elements `a` and `b` of it, either
`a` is one, `b` is one, or if `a` and `b` have the same sign, then `a` is Archimedean with respect to `b`.-/
def is_archimedean := ∀a b : α, is_one a ∨ is_one b ∨ (same_sign a b → is_archimedean_wrt a b)

end OrderedSemigroup

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelSemigroup α]

/-- If `a` is Archimedean with respect to `b`, then `a` and `b` have the same sign. -/
theorem archimedean_same_sign {a b : α} (arch : is_archimedean_wrt a b) : same_sign a b := by
  obtain ⟨N, arch⟩ := arch
  rcases arch N (by simp) with ⟨pos_b, h⟩ | ⟨neg_b , h⟩
  · left
    constructor
    · exact pos_le_pow_pos pos_b N h.le
    · trivial
  · right
    left
    constructor
    · exact pow_le_neg_neg neg_b N h.le
    · trivial

/-- If `b` is positive and there exists an `n : ℕ+` such that `a^n ≥ b`, then `a` is Archimedean with respect to `b`. -/
theorem pos_ge_once_archimedean {a b : α} (pos : is_positive b) (h : ∃n : ℕ+, a^n ≥ b) : is_archimedean_wrt a b := by
  rcases h with ⟨n, hn⟩
  use n+1
  intro x hx
  left
  constructor
  · trivial
  · exact lt_of_le_of_lt hn (pos_ppow_lt_ppow n x (pos_le_pow_pos pos n hn) hx)

/-- If `b` is negative and there exists an `n : ℕ+` such that `a^n ≤ b`, then `a` is Archimedean with respect to `b`. -/
theorem neg_ge_once_archimedean {a b : α} (neg : is_negative b) (h : ∃n : ℕ+, a^n ≤ b) : is_archimedean_wrt a b := by
  rcases h with ⟨n, hn⟩
  use n+1
  intro x hx
  right
  constructor
  · trivial
  · exact gt_of_ge_of_gt hn (neg_ppow_lt_ppow n x (pow_le_neg_neg neg n hn) hx)

/-- If `b` is positive and `a` is not Archimedean with respect to `b`, then for all `n : ℕ+`, `a^n < b`. -/
theorem pos_not_archimedean_wrt_forall_lt {a b : α} (pos : is_positive b) (h : ¬is_archimedean_wrt a b) :
    ∀n : ℕ+, a^n < b := by
  have := mt (pos_ge_once_archimedean pos) h
  simpa

/-- If `b` is negative and `a` is not Archimedean with respect to `b`, then for all `n : ℕ+`, `b < a^n`. -/
theorem neg_not_archimedean_wrt_forall_gt {a b : α} (neg : is_negative b) (h : ¬is_archimedean_wrt a b) :
    ∀n : ℕ+, b < a^n := by
  have := mt (neg_ge_once_archimedean neg) h
  simpa

/-- If `a` and `b` are positive, `a` is not Archimedean with respect to `b`, and `a*b ≤ b*a`, then `b` and `a*b` form an anomalous pair. -/
theorem pos_not_arch_anomalous_pair {a b : α} (pos_a : is_positive a) (pos_b : is_positive b)
    (not_arch : ¬is_archimedean_wrt a b) (comm : a*b ≤ b*a) : anomalous_pair b (a*b) := by
  intro n
  left
  constructor
  · exact gt_of_ge_of_gt (comm_factor_le comm n) ((pos_pow_pos pos_a n) (b ^ n))
  · calc
      (a * b) ^ n ≤ (b * a) ^ n := le_pow comm n
      _           ≤ b ^ n * a ^ n := comm_dist_le comm n
      _           < b ^ n * b := mul_lt_mul_left' (pos_not_archimedean_wrt_forall_lt pos_b not_arch n) (b ^ n)
      _           = b ^ (n + 1) := Eq.symm (ppow_succ n b)

/-- If `a` and `b` are positive, `a` is not Archimedean with respect to `b`, and `b*a ≤ a*b`, then `b` and `a*b` form an anomalous pair. -/
theorem pos_not_arch_anomalous_pair' {a b : α} (pos_a : is_positive a) (pos_b : is_positive b)
    (not_arch : ¬is_archimedean_wrt a b) (comm : b*a ≤ a*b) : anomalous_pair b (a*b) := by
  intro n
  left
  constructor
  · calc
      b ^ n < b ^ n * a ^ n := pos_right (pos_pow_pos pos_a n) (b ^ n)
      _     ≤ (b * a) ^ n := comm_factor_le comm n
      _     ≤ (a * b) ^ n := comm_swap_le comm n
  · calc
      (a * b) ^ n ≤ a ^ n * b ^ n := comm_dist_le comm n
      _           < b * b ^ n := mul_lt_mul_right' (pos_not_archimedean_wrt_forall_lt pos_b not_arch n) (b ^ n)
      _           = b ^ (n + 1) := Eq.symm (ppow_succ' n b)

/-- If `a` and `b` are negative, `a` is not Archimedean with respect to `b`, and `a*b ≤ b*a`, then `b` and `a*b` form an anomalous pair. -/
theorem neg_not_archimedean_anomalous_pair {a b : α} (neg_a : is_negative a) (neg_b : is_negative b)
    (not_arch : ¬is_archimedean_wrt a b) (comm : a*b ≤ b*a) : anomalous_pair b (a*b) := by
  intro n
  right
  constructor
  · calc
      (a * b) ^ n ≤ (b * a) ^ n := comm_swap_le comm n
      _           ≤ b ^ n * a ^ n := comm_dist_le comm n
      _           < b ^ n := neg_right (neg_pow_neg neg_a n) (b ^ n)
  · calc
      (a * b) ^ n ≥ a ^ n * b ^ n := comm_factor_le comm n
      _           > b * b ^ n := mul_lt_mul_right' (neg_not_archimedean_wrt_forall_gt neg_b not_arch n ) (b ^ n)
      _           = b ^ (n + 1) := Eq.symm (ppow_succ' n b)

/-- If `a` and `b` are negative, `a` is not Archimedean with respect to `b`, and `b*a ≤ a*b`, then `b` and `a*b` form an anomalous pair. -/
theorem neg_not_archimedean_anomalous_pair' {a b : α} (neg_a : is_negative a) (neg_b : is_negative b)
    (not_arch : ¬is_archimedean_wrt a b) (comm : b*a ≤ a*b) : anomalous_pair b (a*b) := by
  intro n
  right
  constructor
  · exact lt_of_le_of_lt (comm_dist_le comm n) ((neg_pow_neg neg_a n) (b ^ n))
  · calc
      (a * b) ^ n ≥ (b * a) ^ n := comm_swap_le comm n
      _           ≥ b ^ n * a ^ n := comm_factor_le comm n
      _           > b ^ n * b := mul_lt_mul_left' (neg_not_archimedean_wrt_forall_gt neg_b not_arch n) (b ^ n)
      _           = b ^ (n + 1) := Eq.symm (ppow_succ n b)

/-- If a linear ordered cancel semigroup is not Archimedean, then it has an anomalous pair. -/
theorem non_archimedean_anomalous_pair (non_arch : ¬is_archimedean (α := α)) : has_anomalous_pair (α := α) := by
  unfold is_archimedean at non_arch
  push_neg at non_arch
  rcases non_arch with ⟨a, b, not_one_a, not_one_b, same_sign_ab, hab⟩
  rcases pos_neg_or_one a with pos_a | neg_a | one_a
  <;> rcases pos_neg_or_one b with pos_b | neg_b | one_b
  <;> try contradiction
  · rcases le_total (a*b) (b*a) with h | h
    <;> use b, (a*b)
    · exact pos_not_arch_anomalous_pair pos_a pos_b hab h
    · exact pos_not_arch_anomalous_pair' pos_a pos_b hab h
  · exact False.elim (pos_neg_same_sign_false pos_a neg_b same_sign_ab)
  · exact False.elim (pos_neg_same_sign_false pos_b neg_a (same_sign_symm same_sign_ab))
  · rcases le_total (a*b) (b*a) with h | h
    <;> use b, (a*b)
    · exact neg_not_archimedean_anomalous_pair neg_a neg_b hab h
    · exact neg_not_archimedean_anomalous_pair' neg_a neg_b hab h

/-- If `a` and `b` are positive and `a * b < b * a`, then `a*b` and `b*a` form an anomalous pair. -/
theorem pos_not_comm_anomalous_pair {a b : α} (pos_a : is_positive a) (pos_b : is_positive b)
    (h : a * b < b * a) : anomalous_pair (a*b) (b*a) := by
  intro n
  have : ∀n : ℕ+, (b*a)^n < (a*b)^(n+1) := by
    intro n
    calc
      (b * a) ^ n < (b * a) ^ n * b := pos_right pos_b ((b * a) ^ n)
      _           < a * (b * a) ^ n * b := mul_lt_mul_right' (pos_a ((b * a) ^ n)) b
      _           = (a * b) ^ (n + 1) := Eq.symm split_first_and_last_factor_of_product
  left
  exact ⟨comm_swap_lt h n, this n⟩

/-- If `a` and `b` are negative and `a * b < b * a`, then `b*a` and `a*b` form an anomalous pair. -/
theorem neg_not_comm_anomalous_pair {a b : α} (neg_a : is_negative a) (neg_b : is_negative b)
    (h : a * b < b * a) : anomalous_pair (b*a) (a*b) := by
  intro n
  have : ∀n : ℕ+, (a*b)^n >(b*a)^(n+1) := by
    intro n
    calc
      (a * b) ^ n > (a * b) ^ n * a := neg_right neg_a ((a * b) ^ n)
      _           > b * (a * b) ^ n * a := mul_lt_mul_right' (neg_b ((a * b) ^ n)) a
      _           = (b * a) ^ (n + 1) := Eq.symm split_first_and_last_factor_of_product
  right
  exact ⟨comm_swap_lt h n, this n⟩

/-- If `a` and `b` are positive and there is no anomalous pair, then `a` and `b` commute. -/
theorem pos_not_anomalous_comm {a b : α} (pos_a : is_positive a) (pos_b : is_positive b)
    (not_anomalous : ¬has_anomalous_pair (α := α)): a * b = b * a := by
  rcases lt_trichotomy (a*b) (b*a) with h | h | h
  · have : has_anomalous_pair (α := α) := by
      use (a*b), (b*a)
      exact pos_not_comm_anomalous_pair pos_a pos_b h
    contradiction
  · trivial
  · have : has_anomalous_pair (α := α) := by
      use (b*a), (a*b)
      exact pos_not_comm_anomalous_pair pos_b pos_a h
    contradiction

/-- If `a` and `b` are negative and there is no anomalous pair, then `a` and `b` commute. -/
theorem neg_not_anomalous_comm {a b : α} (neg_a : is_negative a) (neg_b : is_negative b)
    (not_anomalous : ¬has_anomalous_pair (α := α)): a * b = b * a := by
  rcases lt_trichotomy (a*b) (b*a) with h | h | h
  · have : has_anomalous_pair (α := α) := by
      use (b*a), (a*b)
      exact neg_not_comm_anomalous_pair neg_a neg_b h
    contradiction
  · trivial
  · have : has_anomalous_pair (α := α) := by
      use (a*b), (b*a)
      exact neg_not_comm_anomalous_pair neg_b neg_a h
    contradiction

/-- If `a * b < b * a` and `(b * a)` commutes with `b`, then we have a contradiction and so `a` and `b` commute. -/
theorem not_comm_once_comm {a b : α} (h : a * b < b * a) (comm : (b * a) * b = b * (b * a)) :
  a * b = b * a := by
  have : a * b * a * b > a * b * a * b := calc
    a * b * a * b = a * ((b * a) * b) := by simp [mul_assoc]
    _             = a * (b * (b * a)) := by simp [←comm]
    _             = (a * b) * (b * a) := by simp [mul_assoc]
    _             > (a * b) * (a * b) := by exact mul_lt_mul_left' h (a * b)
    _             = a * b * a * b := by exact Eq.symm (mul_assoc (a * b) a b)
  exact False.elim ((lt_self_iff_false (a * b * a * b)).mp this)

/-- If `b * a < a * b` and `(b * a)` commutes with `b`, then we have a contradiction and so `a` and `b` commute. -/
theorem not_comm_once_comm' {a b : α} (h : b * a < a * b) (comm : (b * a) * b = b * (b * a)) :
  a * b = b * a := by
  have : a * b * a * b > a * b * a * b := calc
    a * b * a * b = a * ((b * a) * b) := by simp [mul_assoc]
    _             = a * (b * (b * a)) := by simp [←comm]
    _             = (a * b) * (b * a) := by simp [mul_assoc]
    _             < (a * b) * (a * b) := by exact mul_lt_mul_left' h (a * b)
    _             = a * b * a * b := by exact Eq.symm (mul_assoc (a * b) a b)
  exact False.elim ((lt_self_iff_false (a * b * a * b)).mp this)

/-- If `a * b < b * a` and `(b * a)` commutes with `a`, then we have a contradiction and so `a` and `b` commute. -/
theorem not_comm_once_comm'' {a b : α} (h : a * b < b * a) (comm : (b * a) * a = a * (b * a)) :
  a * b = b * a := by
  have : a * b * a * b > a * b * a * b := calc
    a * b * a * b = (a * (b * a)) * b := by simp [mul_assoc]
    _             = ((b * a) * a) * b := by simp [←comm]
    _             = (b * a) * (a * b) := by simp [mul_assoc]
    _             > (a * b) * (a * b) := by exact mul_lt_mul_right' h (a * b)
    _             = a * b * a * b := by exact Eq.symm (mul_assoc (a * b) a b)
  exact False.elim ((lt_self_iff_false (a * b * a * b)).mp this)

/-- If `b * a < a * b` and `(b * a)` commutes with `a`, then we have a contradiction and so `a` and `b` commute. -/
theorem not_comm_once_comm''' {a b : α} (h : b * a < a * b) (comm : (b * a) * a = a * (b * a)) :
  a * b = b * a := by
  have : a * b * a * b > a * b * a * b := calc
    a * b * a * b = (a * (b * a)) * b := by simp [mul_assoc]
    _             = ((b * a) * a) * b := by simp [←comm]
    _             = (b * a) * (a * b) := by simp [mul_assoc]
    _             < (a * b) * (a * b) := by exact mul_lt_mul_right' h (a * b)
    _             = a * b * a * b := by exact Eq.symm (mul_assoc (a * b) a b)
  exact False.elim ((lt_self_iff_false (a * b * a * b)).mp this)

/-- If a linear ordered cancel semigroup does not have an anomalous pair, then it is commutative. -/
theorem not_anomalous_pair_commutative (not_anomalous : ¬has_anomalous_pair (α := α)) (a b : α) : a * b = b * a := by
  rcases pos_neg_or_one a with pos_a | neg_a | one_a
  <;> rcases pos_neg_or_one b with pos_b | neg_b | one_b
  all_goals try simp [one_b a, one_right one_b a]
  all_goals try simp [one_a b, one_right one_a b]
  · exact pos_not_anomalous_comm pos_a pos_b not_anomalous
  · rcases pos_neg_or_one (a*b) with pos_ab | neg_ab | one_ab
    have := pos_not_anomalous_comm pos_ab pos_a not_anomalous
    · rcases lt_trichotomy (a*b) (b*a) with h | h | h
      · exact Eq.symm (not_comm_once_comm' h this)
      · trivial
      · exact Eq.symm (not_comm_once_comm h this)
    have := neg_not_anomalous_comm neg_ab neg_b not_anomalous
    · rcases lt_trichotomy (a*b) (b*a) with h | h | h
      · exact Eq.symm (not_comm_once_comm''' h this)
      · trivial
      · exact Eq.symm (not_comm_once_comm'' h this)
    · have : is_one (b * a) := by
        apply one_right_one_forall (b := a)
        rw [Eq.symm (mul_assoc a b a)]
        exact one_ab a
      exact one_unique one_ab this
  · rcases pos_neg_or_one (b*a) with pos_ba | neg_ba | one_ba
    have := pos_not_anomalous_comm pos_ba pos_b not_anomalous
    · rcases lt_trichotomy (a*b) (b*a) with h | h | h
      · exact not_comm_once_comm h this
      · trivial
      · exact not_comm_once_comm' h this
    have := neg_not_anomalous_comm neg_ba neg_a not_anomalous
    · rcases lt_trichotomy (a*b) (b*a) with h | h | h
      · exact not_comm_once_comm'' h this
      · trivial
      · exact not_comm_once_comm''' h this
    · have : is_one (a * b) := by
        apply one_right_one_forall (b := b)
        rw [Eq.symm (mul_assoc b a b)]
        exact one_ba b
      exact one_unique this one_ba
  · exact neg_not_anomalous_comm neg_a neg_b not_anomalous

/-- If a linear ordered cancel semigroup does not have an anomalous pair,
then it is commutative and Archimedean. -/
theorem not_anomalous_comm_and_arch (not_anomalous : ¬has_anomalous_pair (α := α)) :
    (∀a b : α, a * b = b * a) ∧ is_archimedean (α := α) := by
  constructor
  · exact fun a b ↦ not_anomalous_pair_commutative not_anomalous a b
  · have := mt (non_archimedean_anomalous_pair (α := α)) not_anomalous
    simpa

end LinearOrderedCancelSemigroup
