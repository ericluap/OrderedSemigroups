import OrderedSemigroups.Basic

/-!
# Sign of element in Ordered Semigroup

This file defines what it means for an element of an ordered semigroup
to be positive, negative, or one. It also proves some basic facts about signs.
-/

section OrderedSemigroup
variable [OrderedSemigroup α]

def is_positive (a : α) := ∀x : α, a*x > x
def is_negative (a : α) := ∀x : α, a*x < x
def is_one (a : α) := ∀x : α, a*x = x

theorem pos_not_neg {a : α} (is_pos : is_positive a) : ¬is_negative a := by
  intro is_neg
  rw [is_positive, is_negative] at *
  exact (lt_self_iff_false (a * a)).mp (lt_trans (is_neg a) (is_pos a))

theorem pos_not_one {a : α} (is_pos : is_positive a) : ¬is_one a := by
  intro is_zer
  rw [is_positive, is_one] at *
  have is_pos := is_pos a
  simp [is_zer a] at is_pos

theorem neg_not_pos {a : α} (is_neg : is_negative a) : ¬is_positive a := by
  intro is_pos
  rw [is_positive, is_negative] at *
  exact (lt_self_iff_false a).mp (lt_trans (is_pos a) (is_neg a))

theorem neg_not_one {a : α} (is_neg : is_negative a) : ¬is_one a := by
  intro is_zer
  rw [is_negative, is_one] at *
  have is_neg := is_neg a
  simp [is_zer a] at is_neg

theorem one_not_pos {a : α} (is_zer : is_one a) : ¬is_positive a := by
  intro is_pos
  rw [is_positive, is_one] at *
  have is_pos := is_pos a
  rw [is_zer a] at is_pos
  exact (lt_self_iff_false a).mp is_pos

theorem one_not_neg {a : α} (is_zer : is_one a) : ¬is_negative a := by
  intro is_neg
  rw [is_negative, is_one] at *
  have is_neg := is_neg a
  rw [is_zer a] at is_neg
  exact (lt_self_iff_false a).mp is_neg

def same_sign (a b : α) :=
  (is_positive a ∧ is_positive b) ∨
  (is_negative a ∧ is_negative b) ∨
  (is_one a ∧ is_one b)

end OrderedSemigroup

section LinearOrderedCancelSemigroup
variable [LinearOrderedCancelSemigroup α]

lemma pos_right_pos_forall {a b : α} (h : b * a > b) : is_positive a := by
  intro x
  have : b * a * x > b * x := mul_lt_mul_right' h x
  simpa [mul_assoc]

lemma neg_right_neg_forall {a b : α} (h : b * a < b) : is_negative a := by
  intro x
  have : b * a * x < b * x := mul_lt_mul_right' h x
  simpa [mul_assoc]

lemma one_right_one_forall {a b : α} (h : b * a = b) : is_one a := by
  intro x
  have : b * a * x = b * x := congrFun (congrArg HMul.hMul h) x
  simpa [mul_assoc]

/-- Every element of a LinearOrderedCancelSemigroup is either positive, negative, or one. -/
theorem pos_neg_or_one : ∀a : α, is_positive a ∨ is_negative a ∨ is_one a := by
  intro a
  rcases le_total (a*a) a with ha | ha
  <;> rcases LE.le.lt_or_eq ha with ha | ha
  · right; left; exact neg_right_neg_forall ha
  · right; right; exact one_right_one_forall ha
  · left; exact pos_right_pos_forall ha
  · right; right; exact one_right_one_forall ha.symm

end LinearOrderedCancelSemigroup
