import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.PNat.Defs

universe u

variable {α : Type u}

/-- Define + notation for the addition of two ℕ+ -/
instance : Add ℕ+ :=
  ⟨fun a b ↦ ⟨a.val + b.val, by
    have a' : 0 < a.val := by simp
    have b' : 0 < b.val := by simp
    omega⟩⟩

/-- Define + notation for the addition of a ℕ+ with a ℕ returning an ℕ+ -/
instance : HAdd ℕ+ ℕ ℕ+ :=
  ⟨fun a b ↦ ⟨a.val + b, by
    have a' : 0 < a.val := by simp
    omega⟩⟩

/-- The action of ℕ+ on a type with Mul where
  nppowRec n a = a * a ⋯ * a (aka a^n)-/
def nppowRec [Mul α] : ℕ+ → α → α
  | 1, a => a
  | ⟨n+2, hnp⟩, a =>
    have: (⟨n+1, by simp⟩ : ℕ+) < ⟨n+2, hnp⟩ := by simp
    (nppowRec ⟨n+1, by simp⟩ a) * a
termination_by x => x

/-- A semigroup with an action of ℕ+ on it, by default it is exponentiation -/
class Semigroup' (α : Type u) extends Semigroup α where
  nppow : ℕ+ → α → α := nppowRec
  nppow_one : ∀ x, nppow 1 x = x := by intros; rfl
  nppow_succ : ∀ (n : ℕ+) (x), nppow (n+1) x = nppow n x * x

/-- Define the exponentiation notation for the action of ℕ+ on a semigroup' -/
instance (α : Type u) [Semigroup' α] : Pow α ℕ+ :=
  ⟨fun x n ↦ Semigroup'.nppow n x⟩

theorem nppow_eq_pow [Semigroup' α] (n : ℕ+) (x : α) : Semigroup'.nppow n x = x ^ n := rfl

class OrderedSemigroup (α : Type u) extends Semigroup' α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  mul_le_mul_right : ∀ a b : α, a ≤ b → ∀ c : α, a * c ≤ b * c

instance (α : Type u) [OrderedSemigroup α] : CovariantClass α α (· * ·) (· ≤ ·) where
  elim a b c bc := OrderedSemigroup.mul_le_mul_left b c bc a

instance (α : Type u) [OrderedSemigroup α] : CovariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a b c bc := OrderedSemigroup.mul_le_mul_right b c bc a

class OrderedCancelSemigroup (α : Type u) extends OrderedSemigroup α where
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
  le_of_mul_le_mul_right : ∀ a b c : α, b * a ≤ c * a → b ≤ c

instance (α : Type u) [OrderedCancelSemigroup α] : ContravariantClass α α (· * ·) (· ≤ ·) where
  elim a b c bc := OrderedCancelSemigroup.le_of_mul_le_mul_left a b c bc

instance (α : Type u) [OrderedCancelSemigroup α] : ContravariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a b c bc := OrderedCancelSemigroup.le_of_mul_le_mul_right a b c bc

instance (α : Type u) [OrderedCancelSemigroup α] : LeftCancelSemigroup α where
  mul_left_cancel a b c habc := by
    have b_le_c : b ≤ c := OrderedCancelSemigroup.le_of_mul_le_mul_left a b c (le_of_eq habc)
    have c_le_b : c ≤ b := OrderedCancelSemigroup.le_of_mul_le_mul_left a c b (le_of_eq (id (Eq.symm habc)))
    exact (le_antisymm b_le_c c_le_b)

instance (α : Type u) [OrderedCancelSemigroup α] : RightCancelSemigroup α where
  mul_right_cancel a b c habc := by
    have a_le_c : a ≤ c := OrderedCancelSemigroup.le_of_mul_le_mul_right b a c (le_of_eq habc)
    have c_le_a : c ≤ a := OrderedCancelSemigroup.le_of_mul_le_mul_right b c a (le_of_eq (id (Eq.symm habc)))
    exact (le_antisymm a_le_c c_le_a)

class LinearOrderedSemigroup (α : Type u) extends OrderedSemigroup α, LinearOrder α

section LinearOrderedSemigroup
variable [LinearOrderedSemigroup α]

def is_positive (a : α) := ∀x : α, a*x > x
def is_negative (a : α) := ∀x : α, a*x < x
def is_zero (a : α) := ∀x : α, a*x = x

end LinearOrderedSemigroup

class LinearOrderedCancelSemigroup (α : Type u) extends OrderedCancelSemigroup α, LinearOrder α

instance (α : Type u) [LinearOrderedCancelSemigroup α] : LinearOrderedSemigroup α where
  le_total := LinearOrderedCancelSemigroup.le_total
  decidableLE := LinearOrderedCancelSemigroup.decidableLE
  min_def := LinearOrderedCancelSemigroup.min_def
  max_def := LinearOrderedCancelSemigroup.max_def
  compare_eq_compareOfLessAndEq := LinearOrderedCancelSemigroup.compare_eq_compareOfLessAndEq

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelSemigroup α]

theorem LinearOrderedCancelSemigroup.mul_lt_mul_left (a b : α) (h : a < b) (c : α) : c * a < c * b := mul_lt_mul_left' h c

lemma pos_right_pos_forall {a b : α} (h : b * a > b) : is_positive a := by
  intro x
  have : b * a * x > b * x := mul_lt_mul_right' h x
  simp [mul_assoc] at this
  trivial

lemma neg_right_neg_forall {a b : α} (h : b * a < b) : is_negative a := by
  intro x
  have : b * a * x < b * x := mul_lt_mul_right' h x
  simp [mul_assoc] at this
  trivial

lemma zero_right_zero_forall {a b : α} (h : b * a = b) : is_zero a := by
  intro x
  have : b * a * x = b * x := congrFun (congrArg HMul.hMul h) x
  simp [mul_assoc] at this
  trivial

/-- Every element of a LinearOrderedCancelSemigroup is either positive, negative, or zero. -/
theorem pos_neg_or_zero : ∀a : α, is_positive a ∨ is_negative a ∨ is_zero a := by
  intro a
  rcases le_total (a*a) a with ha | ha
  <;> rcases LE.le.lt_or_eq ha with ha | ha
  · right; left; exact neg_right_neg_forall ha
  · right; right; exact zero_right_zero_forall ha
  · left; exact pos_right_pos_forall ha
  · right; right; exact zero_right_zero_forall ha.symm


end LinearOrderedCancelSemigroup
