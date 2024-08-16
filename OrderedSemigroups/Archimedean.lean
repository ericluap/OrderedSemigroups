import OrderedSemigroups.Sign

/-!
# Archimedean Ordered Semigroups and Anomalous Pairs

This file defines Archimedean ordered semigroups and anomalous pairs
and proves theorems about how they interact.

-/

universe u

variable {α : Type u} [OrderedSemigroup α]

def is_archimedean_wrt (a b : α) :=
  is_one a ∨ is_one b ∨
  ∃n : ℕ+, (is_positive b ∧ b < a^n) ∨ (is_negative b ∧ a^n < b)

theorem arhimedean_same_sign {a b : α} (h : is_archimedean_wrt a b) : same_sign a b := by
  sorry

def anomalous_pair (a b : α) := ∀n : ℕ+, (a^n < b^n ∧ b^n < a^(n+1)) ∨ (a^n > b^n ∧ b^n > a^(n+1))

def has_anomalous_pair := ∃a b : α, anomalous_pair a b

class Archimedean (α : Type u) [OrderedSemigroup α] where
  arch : ∀a b : α, is_archimedean_wrt a b

section Archimedean
variable [Archimedean α]

end Archimedean
