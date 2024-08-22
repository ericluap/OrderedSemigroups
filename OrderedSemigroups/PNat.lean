import Mathlib.Data.PNat.Basic

/-!
# Positive Naturals

This file proves some basic lemmas about `PNat` (aka `ℕ+`)
that are used in relation to exponentiation of elements in a semigroup.

-/

lemma add_sub_eq (x y : ℕ+) : x + y - y = x := by
  apply PNat.eq
  simp [PNat.sub_coe, PNat.lt_add_left y x]

lemma gt_one_sub_eq {x : ℕ+} (h : 1 < x) : (x : ℕ) - 1 = ((x - 1) : ℕ+) := by
  simp [PNat.sub_coe, h]

lemma lt_sub {x y : ℕ+} (h : x + 1 < y) : x < y - 1 := by
  rw [←PNat.coe_lt_coe]
  exact Nat.lt_of_lt_of_eq (Nat.lt_sub_of_add_lt h) (gt_one_sub_eq (PNat.one_lt_of_lt h))

lemma le.dest : ∀{n m : ℕ+}, n < m → ∃k : ℕ+, n + k = m := by
  intro n
  induction n using PNat.recOn with
  | p1 =>
    intro m h
    use (m - 1)
    exact PNat.add_sub_of_lt h
  | hp n ih =>
    intro m h
    have : n < m - 1 := lt_sub h
    obtain ⟨k, hk⟩ := ih this
    use k
    have : n + 1 + k = m := by
      simp [add_right_comm, congrFun (congrArg HAdd.hAdd hk) 1,
        AddCommMagma.add_comm (m - 1) 1, PNat.add_sub_of_lt (PNat.one_lt_of_lt h)]
    exact this
