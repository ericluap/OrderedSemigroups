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

def is_archimedean_wrt (a b : α) :=
  ∃N : ℕ+, ∀n : ℕ+, n ≥ N → (is_positive b ∧ b < a^n) ∨ (is_negative b ∧ a^n < b)

def anomalous_pair (a b : α) := ∀n : ℕ+, (a^n < b^n ∧ b^n < a^(n+1)) ∨ (a^n > b^n ∧ b^n > a^(n+1))

def has_anomalous_pair := ∃a b : α, anomalous_pair a b

def is_archimedean := ∀a b : α, is_one a ∨ is_one b ∨ is_archimedean_wrt a b

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

theorem non_archimedean_anomalous_pair (non_arch : ¬is_archimedean (α := α)) : has_anomalous_pair (α := α) := by
  simp [is_archimedean] at non_arch
  rcases non_arch with ⟨a, not_one_a, b, not_one_b, hab⟩
  rcases pos_neg_or_one a with pos_a | neg_a | one_a
  <;> rcases pos_neg_or_one b with pos_b | neg_b | one_b
  sorry
  /-
  · rcases le_total (a*b) (b*a) with h | h
    ·
  simp [is_archimedean_wrt] at hab
  rcases hab 1 with ⟨x, hx, hab_pos, hab_neg⟩
  -/


end LinearOrderedCancelSemigroup

section Archimedean
variable [Archimedean α]

end Archimedean
