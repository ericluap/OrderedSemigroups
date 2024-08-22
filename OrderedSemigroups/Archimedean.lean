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

abbrev is_archimedean_wrt (a b : α) :=
  ∃N : ℕ+, ∀n : ℕ+, n ≥ N → (is_positive b ∧ b < a^n) ∨ (is_negative b ∧ a^n < b)

abbrev anomalous_pair (a b : α) := ∀n : ℕ+, (a^n < b^n ∧ b^n < a^(n+1)) ∨ (a^n > b^n ∧ b^n > a^(n+1))

abbrev has_anomalous_pair := ∃a b : α, anomalous_pair a b

def is_archimedean := ∀a b : α, is_one a ∨ is_one b ∨ (same_sign a b → is_archimedean_wrt a b)

class Archimedean (α : Type u) [OrderedSemigroup α] where
  arch : is_archimedean (α := α)

end OrderedSemigroup

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelSemigroup α]

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

theorem pos_ge_once_archimedean {a b : α} (pos : is_positive b) (h : ∃n : ℕ+, a^n ≥ b) : is_archimedean_wrt a b := by
  rcases h with ⟨n, hn⟩
  use n+1
  intro x hx
  left
  constructor
  · trivial
  · exact lt_of_le_of_lt hn (pos_ppow_lt_ppow n x (pos_le_pow_pos pos n hn) hx)

theorem neg_ge_once_archimedean {a b : α} (neg : is_negative b) (h : ∃n : ℕ+, a^n ≤ b) : is_archimedean_wrt a b := by
  rcases h with ⟨n, hn⟩
  use n+1
  intro x hx
  right
  constructor
  · trivial
  · exact gt_of_ge_of_gt hn (neg_ppow_lt_ppow n x (pow_le_neg_neg neg n hn) hx)

theorem pos_not_archimedean_wrt_forall_lt {a b : α} (pos : is_positive b) (h : ¬is_archimedean_wrt a b) :
    ∀n : ℕ+, a^n < b := by
  have := mt (pos_ge_once_archimedean pos) h
  simpa

theorem neg_not_archimedean_wrt_forall_gt {a b : α} (neg : is_negative b) (h : ¬is_archimedean_wrt a b) :
    ∀n : ℕ+, b < a^n := by
  have := mt (neg_ge_once_archimedean neg) h
  simpa

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

theorem not_anomalous_pair_commutative (not_anomalous : ¬has_anomalous_pair (α := α)) (a b : α) : a * b = b * a := by sorry

end LinearOrderedCancelSemigroup
