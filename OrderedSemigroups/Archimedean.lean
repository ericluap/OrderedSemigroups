import OrderedSemigroups.Sign
import Mathlib.Tactic

/-!
# Archimedean Ordered Semigroups and Anomalous Pairs

This file defines Archimedean ordered semigroups and anomalous pairs
and proves theorems about how they interact.

-/

universe u

variable {α : Type u}

section OrderedSemigroup
variable [LeftOrderedSemigroup α]

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

abbrev has_large_differences := ∀a b : α, (is_positive a → a < b → ∃(c : α) (n : ℕ+), is_archimedean_wrt c a ∧ a^n*c ≤ b^n) ∧
               (is_negative a → b < a → ∃(c : α) (n : ℕ+), is_archimedean_wrt c a ∧ a^n*c ≥ b^n)

theorem not_anomalous_pair_self (a : α) : ¬anomalous_pair a a := by
  simp

theorem pos_anomalous_lt {a b : α} (anomalous : anomalous_pair a b) (pos : is_positive a) : a < b := by
  rcases anomalous 1 with ⟨a_lt_b, _⟩ | ⟨_, b_gt_ap1⟩
  · simp at a_lt_b
    trivial
  · simp at *
    calc
      a < a * a              := by exact pos a
      _ = a ^ (1 : ℕ+) * a ^ (1 : ℕ+) := by rw [ppow_one]
      _ = a ^ (1 + (1 : ℕ+)) := by exact Eq.symm (ppow_add a 1 1)
      _ < b                  := by exact b_gt_ap1

theorem anomalous_not_one {a b : α} (anomalous : anomalous_pair a b) : ¬is_one a := by
  rcases anomalous 1 with ⟨a_lt_b, b_lt_ap1⟩ | ⟨a_gt_b, b_gt_ap1⟩
  · intro one_a
    simp at a_lt_b
    simp [ppow_succ, one_a a] at b_lt_ap1
    exact (lt_self_iff_false (b)).mp (gt_trans a_lt_b b_lt_ap1)
  · intro one_a
    simp at a_gt_b
    simp [ppow_succ, one_a a] at b_gt_ap1
    exact (lt_self_iff_false (b)).mp (gt_trans b_gt_ap1 a_gt_b)

end OrderedSemigroup

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelSemigroup α]

theorem anomalous_not_one' {a b : α} (anomalous : anomalous_pair a b) : ¬is_one b := by
  rcases anomalous 1 with ⟨a_lt_b, b_lt_ap1⟩ | ⟨a_gt_b, b_gt_ap1⟩
  <;> simp [ppow_succ] at *
  <;> rcases pos_neg_or_one a with pos_a | neg_a | one_a
  <;> intro one_b
  · have : is_positive b := pos_le_pos pos_a a_lt_b.le
    exact False.elim (pos_not_one this one_b)
  · have : is_negative (a * a) := by
      have := neg_pow_neg neg_a 2
      simpa [←ppow_two a]
    have : is_negative b := le_neg_neg this b_lt_ap1.le
    exact False.elim (neg_not_one this one_b)
  · have : is_positive b := gt_one_pos one_a a_lt_b
    exact False.elim (pos_not_one this one_b)
  · exact (lt_self_iff_false b).mp (gt_trans b_gt_ap1 (gt_trans (pos_a a) a_gt_b))
  · exact one_not_neg one_b (le_neg_neg neg_a (a_gt_b.le))
  · exact (lt_self_iff_false b).mp (gt_trans b_gt_ap1 (lt_of_lt_of_eq a_gt_b (id (Eq.symm (one_a a)))))

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


lemma rw_pow_one_plus_one (a : α) : a^(1 + (1 : ℕ+)) = a * a := by
  exact ppow_two a

lemma product_of_neg_neg {a : α} (neg : is_negative a) : is_negative (a * a) := by
  rw [←ppow_two]
  exact neg_pow_neg neg 2

theorem anomalous_pair_same_sign {a b : α} (anomalous : anomalous_pair a b) : same_sign a b := by
  rcases anomalous 1 with ⟨a_lt_b, b_lt_ap1⟩ | ⟨a_gt_b, b_gt_ap1⟩
  <;> simp [rw_pow_one_plus_one] at *
  <;> rcases pos_neg_or_one a with pos_a | neg_a | one_a
  case inl.intro.inr.inl =>
    exact False.elim ((lt_self_iff_false b).mp (gt_trans a_lt_b (gt_trans (neg_a a) b_lt_ap1)))
  case inl.intro.inr.inr =>
    exact False.elim ((lt_self_iff_false b).mp (gt_trans a_lt_b (lt_of_lt_of_eq b_lt_ap1 (one_a a))))
  case inr.intro.inl =>
    exact False.elim ((lt_self_iff_false b).mp (gt_trans b_gt_ap1 (gt_trans (pos_a a) a_gt_b)))
  case inr.intro.inr.inr =>
    exact False.elim ((lt_self_iff_false b).mp (gt_trans b_gt_ap1 (lt_of_lt_of_eq a_gt_b (id (Eq.symm (one_a a))))))
  all_goals rcases pos_neg_or_one b with pos_b | neg_b | one_b
  <;> try tauto
  · exact False.elim (pos_not_neg (pos_le_pos pos_a a_lt_b.le) neg_b)
  · exact False.elim (anomalous_not_one' anomalous one_b)
  · exact False.elim (neg_not_pos (le_neg_neg neg_a a_gt_b.le) pos_b)
  · exact False.elim (neg_not_one (le_neg_neg neg_a a_gt_b.le) one_b)

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

def not_anomalous_comm_semigroup (not_anomalous : ¬has_anomalous_pair (α := α)) :
    LinearOrderedCancelCommSemigroup α where
  mul_comm a b := not_anomalous_pair_commutative not_anomalous a b

theorem lt_not_anomalous_difference {a b : α} (h : a < b) (not_anomalous : ¬has_anomalous_pair (α := α)) :
    ∃n : ℕ+, a^(n+1) ≤ b^n := by
  by_contra hx
  simp at hx
  have : ∀x : ℕ+, a^x < b^x := fun x ↦ lt_pow h x
  have : anomalous_pair a b := by
    intro n
    left
    exact ⟨this n, hx n⟩
  have : has_anomalous_pair (α := α) := by use a, b
  exact not_anomalous this

theorem lt_not_anomalous_difference' {a b : α} (h : a < b) (not_anomalous : ¬has_anomalous_pair (α := α)) :
    ∃n : ℕ+, a^n ≤ b^(n+1) := by
  by_contra hx
  simp at hx
  have : ∀x : ℕ+, a^x < b^x := fun x ↦ lt_pow h x
  have : anomalous_pair b a := by
    intro n
    right
    exact ⟨this n, hx n⟩
  have : has_anomalous_pair (α := α) := by use b, a
  exact not_anomalous this

theorem arch_wrt_self {a : α} (not_one : ¬is_one a) : is_archimedean_wrt a a := by
  use 2
  intro n hn
  rcases pos_neg_or_one a with pos_a | neg_a | one_a
  · left
    constructor
    · trivial
    ·  exact gt_of_ge_of_gt (pos_ppow_le_ppow 2 n pos_a hn) (pos_one_lt_squared pos_a)
  · right
    constructor
    · trivial
    · exact lt_of_le_of_lt (neg_ppow_le_ppow 2 n neg_a hn) (neg_one_lt_squared neg_a)
  · contradiction

theorem not_anomalous_large_difference (not_anomalous : ¬has_anomalous_pair (α := α)) :
    has_large_differences (α := α) := by
  intro a b
  constructor
  · intro pos_a a_lt_b
    obtain ⟨n, hn⟩ := lt_not_anomalous_difference a_lt_b not_anomalous
    have : a^n * a ≤ b^n := by simpa [←ppow_succ]
    use a, n
    constructor
    · exact arch_wrt_self (pos_not_one pos_a)
    · trivial
  · intro neg_a b_lt_a
    obtain ⟨n, hn⟩ := lt_not_anomalous_difference' b_lt_a not_anomalous
    use a, n
    constructor
    · exact arch_wrt_self (neg_not_one neg_a)
    · simpa [←ppow_succ]

theorem large_differences_pos_lt_not_anomalous {a b : α} (differences : has_large_differences (α := α))
    (pos_a : is_positive a) (a_lt_b : a < b) : ¬anomalous_pair a b := by
  intro hab
  rcases differences a b with ⟨pos_diff, _⟩
  obtain ⟨c, m, ⟨N, hN⟩, h⟩ := pos_diff pos_a a_lt_b
  rcases hN N (by exact Preorder.le_refl N) with ⟨_, lt⟩ | ⟨neg, _⟩
  · have : a^(m * N + 1) ≤ b^(m * N) := by
      rcases le_total (a^m*c) (c*a^m) with hamc | hamc
      · calc
          a ^ (m * N + 1) = a ^ (m * N) * a := ppow_succ (m * N) a
          _               ≤ a ^ (m * N) * (c^N) := (mul_lt_mul_left' lt (a ^ (m * N))).le
          _               = (a ^ m) ^ N * c ^ N := by rw [ppow_mul]
          _               ≤ (a ^ m * c) ^ N := comm_factor_le hamc N
          _               ≤ (b ^ m) ^ N := le_pow h N
          _               = b ^ (m * N) := Eq.symm (ppow_mul b m N)
      · calc
          a ^ (m * N + 1) = a * a ^ (m * N) := ppow_succ' (m * N) a
          _               ≤ c ^ N * a ^ (m * N) := (mul_lt_mul_right' lt (a ^ (m * N))).le
          _               = c ^ N * (a ^ m) ^ N := by rw [ppow_mul]
          _               ≤ (c * a ^ m) ^ N := comm_factor_le hamc N
          _               ≤ (a ^ m * c) ^ N := comm_swap_le hamc N
          _               ≤ (b ^ m) ^ N := le_pow h N
          _               = b ^ (m * N) := Eq.symm (ppow_mul b m N)
    rcases hab (m*N) with ⟨_, bmn_lt_amn1⟩ | ⟨amn_gt_bmn, _⟩
    · exact (lt_self_iff_false (a^(m*N+1))).mp (lt_of_le_of_lt this bmn_lt_amn1)
    · have : a ^ (m * N) > a ^ (m * N + 1) := by exact lt_of_le_of_lt this amn_gt_bmn
      simp [ppow_succ] at this
      exact (lt_self_iff_false (a^(m*N))).mp (gt_trans this (pos_right pos_a (a ^ (m * N))))
  · exact False.elim (pos_not_neg pos_a neg)

theorem large_differences_neg_lt_anomalous {a b : α} (differences : has_large_differences (α := α))
    (neg_a : is_negative a) (b_lt_a : b < a) : ¬anomalous_pair a b := by
  intro hab
  rcases differences a b with ⟨_, neg_diff⟩
  obtain ⟨c, m, ⟨N, hN⟩, h⟩ := neg_diff neg_a b_lt_a
  rcases hN N (by exact Preorder.le_refl N) with ⟨pos, _⟩ | ⟨_, lt⟩
  · exact False.elim (pos_not_neg pos neg_a)
  · have : a^(m * N + 1) ≥ b^(m * N) := by
      rcases le_total (a^m*c) (c*a^m) with hamc | hamc
      · calc
          a ^ (m * N + 1) = a * a ^ (m * N) := ppow_succ' (m * N) a
          _               ≥ c ^ N * a ^ (m * N) := (mul_lt_mul_right' lt (a ^ (m * N))).le
          _               = c ^ N * (a ^ m) ^ N := by rw [ppow_mul]
          _               ≥ (c * a ^ m) ^ N := comm_dist_le hamc N
          _               ≥ (a ^ m * c) ^ N := comm_swap_le hamc N
          _               ≥ (b ^ m) ^ N := le_pow h N
          _               = b ^ (m * N) := Eq.symm (ppow_mul b m N)
      · calc
        a ^ (m * N + 1) = a ^ (m * N) * a := ppow_succ (m * N) a
        _               ≥ a ^ (m * N) * (c^N) := (mul_lt_mul_left' lt (a ^ (m * N))).le
        _               = (a ^ m) ^ N * c ^ N := by rw [ppow_mul]
        _               ≥ (a ^ m * c) ^ N := comm_dist_le hamc N
        _               ≥ (b ^ m) ^ N := le_pow h N
        _               = b ^ (m * N) := Eq.symm (ppow_mul b m N)
    rcases hab (m*N) with ⟨left, _⟩ | ⟨_, right⟩
    · have : a^(m*N) < a^(m*N+1) := by exact gt_of_ge_of_gt this left
      simp [ppow_succ] at this
      exact False.elim ((lt_self_iff_false (a ^ (m * N))).mp (gt_trans (neg_right neg_a (a ^ (m * N))) this))
    · exact (lt_self_iff_false (a ^ (m * N + 1))).mp (gt_of_ge_of_gt this right)

theorem large_difference_not_anomalous (differences : has_large_differences (α := α)) :
    ¬has_anomalous_pair (α := α) := by
  intro anomalous
  obtain ⟨a, b, hab⟩ := anomalous
  rcases pos_neg_or_one a with pos_a | neg_a | one_a
  <;> rcases pos_neg_or_one b with pos_b | neg_b | one_b
  <;> rcases lt_trichotomy a b with a_lt_b | a_eq_b | b_lt_a
  <;> try
    rw [a_eq_b] at hab
    have : ¬anomalous_pair b b := not_anomalous_pair_self b
    exact this hab
  all_goals try
    have : ¬is_one a := by exact anomalous_not_one hab
    contradiction
  · exact False.elim (large_differences_pos_lt_not_anomalous differences pos_a a_lt_b hab)
  · exact (lt_self_iff_false (b)).mp (gt_trans (pos_anomalous_lt hab pos_a) b_lt_a)
  all_goals
    have ss_ab : same_sign a b := by exact anomalous_pair_same_sign hab
    try (exact False.elim (pos_neg_same_sign_false pos_a neg_b ss_ab))
    try (exact False.elim (pos_neg_same_sign_false pos_b neg_a (same_sign_symm ss_ab)))
    try (exact False.elim (pos_one_same_sign_false pos_a one_b ss_ab))
    try (exact False.elim (pos_one_same_sign_false pos_b one_a (same_sign_symm ss_ab)))
    try (exact False.elim (neg_one_same_sign_false neg_a one_b ss_ab))
    try (exact False.elim (neg_one_same_sign_false neg_b one_a (same_sign_symm ss_ab)))
  · rcases hab 1 with ⟨a_lt_b, b_lt_ap1⟩ | ⟨a_gt_b, b_gt_ap1⟩
    <;> simp [rw_pow_one_plus_one] at *
    · exact False.elim ((lt_self_iff_false b).mp (gt_trans a_lt_b (gt_trans (neg_a a) b_lt_ap1)))
    · exact False.elim ((lt_self_iff_false b).mp (gt_trans a_lt_b a_gt_b))
  · exact False.elim (large_differences_neg_lt_anomalous differences neg_a b_lt_a hab)

theorem not_anomalous_iff_large_difference : ¬has_anomalous_pair (α := α) ↔ has_large_differences (α := α) := by
  constructor
  · exact fun a ↦ not_anomalous_large_difference a
  · exact fun a ↦ large_difference_not_anomalous a

theorem pos_large_elements (not_anomalous : ¬has_anomalous_pair (α := α)) (pos_elem : ∃a : α, is_positive a) :
    ∀x : α, ∃y : α, is_positive y ∧ is_positive (x*y) := by
  intro x
  obtain ⟨z, hz⟩ := pos_elem
  obtain pos_x | neg_x | one_x := pos_neg_or_one x
  -- If `x` is positive we're immediately done
  · use x
    constructor
    · trivial
    · exact pos_sq_pos pos_x
  -- `x` is negative
  · by_contra! all_pos_small
    have xzn2_negative (n : ℕ+) : is_negative (x * z^(n+2)) := by
      have zn2_lt_zn3 : z^(n+2) < z^(n+3) := by
        calc z^(n+3)
        _ = z^(n+2)*z := ppow_succ (n + 2) z
        _ > z^(n+2) := pos_right hz (z ^ (n + 2))
      have  xzn3_lt_xzn3 : x*z^(n+2) < x*z^(n+3) := mul_lt_mul_left' zn2_lt_zn3 x
      have : is_positive (z^(n+3)) := pos_pow_pos hz (n + 3)
      have zn3_not_pos := all_pos_small (z^(n+3)) this
      rw [not_pos_or] at zn3_not_pos
      obtain zn3_neg | zn3_one := zn3_not_pos
      · exact lt_neg_neg zn3_neg xzn3_lt_xzn3
      · exact lt_one_neg zn3_one xzn3_lt_xzn3
    have : has_anomalous_pair (α := α) := by
      simp [has_anomalous_pair]
      use x*z, x
      simp [anomalous_pair]
      intro n
      right
      obtain ⟨is_comm, _⟩ := not_anomalous_comm_and_arch not_anomalous
      constructor
      · have : (x*z)^n = x^n * z^n := mul_pow_comm_semigroup is_comm x z n
        rw [this]
        have : is_positive (z^n) := pos_pow_pos hz n
        exact pos_right this (x ^ n)
      · have := xzn2_negative n
        calc x^n
        _ > x^n*(x*z^(n+2)) := neg_right (xzn2_negative n) (x ^ n)
        _ = (x^n*x)*(z^(n+2)) := by simp [mul_assoc]
        _ = x^(n+1) * (z^(n+2)) := by simp [ppow_succ]
        _ = x^(n+1) * (z^(n+1) * z) := by
          have : n+2 = (n+1)+1 := rfl
          simp [this, ppow_succ]
        _ = x^(n+1) * z^(n+1) * z := by simp [mul_assoc]
        _ = (x * z)^(n+1) * z := by simp [mul_pow_comm_semigroup is_comm]
        _ > (x * z)^(n+1) := pos_right hz ((x * z) ^ (n + 1))
    contradiction
  -- If `x` is one, we're immediately done
  · use z
    constructor
    · trivial
    · have : x * z = z := one_x z
      simpa [this]

theorem neg_large_elements (not_anomalous : ¬has_anomalous_pair (α := α)) (neg_elem : ∃a : α, is_negative a) :
    ∀x : α, ∃y : α, is_negative y ∧ is_negative (x*y) := by
  intro x
  obtain ⟨z, hz⟩ := neg_elem
  obtain pos_x | neg_x | one_x := pos_neg_or_one x
  -- `x` is positive
  · by_contra! all_neg_small
    have xzn2_positive (n : ℕ+) : is_positive (x * z^(n+2)) := by
      have zn2_gt_zn3 : z^(n+2) > z^(n+3) := by
        calc z^(n+3)
        _ = z^(n+2)*z := ppow_succ (n + 2) z
        _ < z^(n+2) := neg_right hz (z ^ (n + 2))
      have  xzn3_lt_xzn3 : x*z^(n+2) > x*z^(n+3) := mul_lt_mul_left' zn2_gt_zn3 x
      have : is_negative (z^(n+3)) := neg_pow_neg hz (n + 3)
      have zn3_not_neg := all_neg_small (z^(n+3)) this
      rw [not_neg_or] at zn3_not_neg
      obtain zn3_pos | zn3_one := zn3_not_neg
      · exact pos_lt_pos zn3_pos xzn3_lt_xzn3
      · exact gt_one_pos zn3_one xzn3_lt_xzn3
    have : has_anomalous_pair (α := α) := by
      simp [has_anomalous_pair]
      use x*z, x
      simp [anomalous_pair]
      intro n
      left
      obtain ⟨is_comm, _⟩ := not_anomalous_comm_and_arch not_anomalous
      constructor
      · have : (x*z)^n = x^n * z^n := mul_pow_comm_semigroup is_comm x z n
        rw [this]
        have : is_negative (z^n) := neg_pow_neg hz n
        exact neg_right this (x ^ n)
      · have := xzn2_positive n
        calc x^n
        _ < x^n*(x*z^(n+2)) := pos_right (xzn2_positive n) (x ^ n)
        _ = (x^n*x)*(z^(n+2)) := by simp [mul_assoc]
        _ = x^(n+1) * (z^(n+2)) := by simp [ppow_succ]
        _ = x^(n+1) * (z^(n+1) * z) := by
          have : n+2 = (n+1)+1 := rfl
          simp [this, ppow_succ]
        _ = x^(n+1) * z^(n+1) * z := by simp [mul_assoc]
        _ = (x * z)^(n+1) * z := by simp [mul_pow_comm_semigroup is_comm]
        _ < (x * z)^(n+1) := neg_right hz ((x * z) ^ (n + 1))
    contradiction
  -- If `x` is negative, we're immediately done
  · use x
    constructor
    · trivial
    · exact product_of_neg_neg neg_x
  -- If `x` is one, we're immediately done
  · use z
    constructor
    · trivial
    · have : x * z = z := one_x z
      simpa [this]

end LinearOrderedCancelSemigroup
