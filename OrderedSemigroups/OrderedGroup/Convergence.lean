import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Convergence of a particular sequence

This file proves that sequences satisfying a particular condition converge.
This is used in the proof of Holder's theorem to show that the
sequence of approximations do converge.

-/

open Filter

lemma arch_nat {e C : ℝ} (C_pos : C > 0) (e_pos : e > 0) : ∃n : ℕ+, 1 / n < e/(2*C) := by
  have eC_pos : e / (2 * C) > 0 := div_pos e_pos (mul_pos zero_lt_two C_pos)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt eC_pos
  use ⟨n + 1, by omega⟩
  simp only [PNat.mk_coe, Nat.cast_add, Nat.cast_one, one_div]
  field_simp
  exact hn

-- Exercise 3.1.5 https://arxiv.org/pdf/1408.5805
-- Formalized with the help of Tomas Ortega
lemma sequence_convergence_unique
  (a : ℕ → ℝ) -- sequence indexed by integers
  (C : ℝ) -- the constant from the bound
  (h_bound : ∀ m n : ℕ, |a (m + n) - a m - a n| ≤ C) :
  ∃! θ : ℝ, -- exists unique θ
  -- conclusion: θ is the limit of a_n/n at +∞
  (Filter.Tendsto (fun n ↦ a n / (n : ℝ)) Filter.atTop (nhds θ)) := by
  -- let I_n be the interval [(a_n - C)/n, (a_n + C)/n]
  let I (n : ℕ) := {x | |(a n) / n - x| ≤ C / n} -- this definition probably needs n > 1
  -- check that I_{m*n} ⊆ I_n for all m, n (we'll do natural, I think it is needed)
  have h (m n : ℕ) (mpos : m > 0): |a (m * n) - m * a n| ≤ (m - 1) * C := by
    -- induction from starting point m = 1
    induction m, mpos using Nat.le_induction with
    | base => rw [Nat.succ_eq_add_one, zero_add, Nat.cast_one, one_mul, one_mul, sub_self, sub_self, abs_zero, zero_mul]
    | succ m hm hI =>
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      calc
        |a ((m + 1) * n) - (m + 1) * a n| = |(a ((m + 1) * n) - a (m * n) - a n) + (a (m * n) - m * a n)| := by ring_nf
        _ ≤ |a ((m + 1) * n) - a (m * n) - a n| + |a (m * n) - m * a n| := abs_add_le _ _
        _ = |a (m * n + n) - a (m * n) - a n| + |a (m * n) - m * a n| := by ring_nf
        _ ≤ C + (m - 1) * C := add_le_add (h_bound (m * n) n) hI
        _ = m * C := by ring_nf

  have h_I (m n : ℕ) (mpos : 0 < m) : I (m * n) ⊆ I n := by
    intro x hx
    have h' : |a (n) - a (m * n) / m| ≤ (m - 1) * C / m := calc
      |a (n) - a (m * n) / m| = 1 / m * |m * a n - a (m * n)| := by
        field_simp; rw [abs_div]
        field_simp; simp only [Nat.abs_cast]; ring
      _ = 1 / ↑m * |a (m * n) - m * a n| := by rw [<-abs_neg]; ring_nf
      _ ≤ 1 / ↑m * ((m - 1) * C) := mul_le_mul_of_nonneg_left (h m n mpos) (by positivity)
      _ ≤ (m - 1) * C / m := by field_simp; simp

    calc
      |a n / ↑n - x| = |(a n / ↑n - a (m * n) / (m * n)) + (a (m * n) / (m * n) - x)| := by simp only [sub_add_sub_cancel]
      _ ≤ |a n / ↑n - a (m * n) / (m * n)| + |a (m * n) / (m * n) - x| := abs_add_le _ _
      _ ≤ |a n / ↑n - a (m * n) / (m * n)| + C / ↑(m * n) := by rw [add_le_add_iff_left, <-Nat.cast_mul]; exact hx
      _ = |a n / n - (a (m * n) / m) / n| + C / ↑(m * n) := by field_simp
      _ = |(a n - a (m * n) / m) / n| + C / ↑(m * n) := by ring_nf
      _ ≤ |a n - a (m * n) / ↑m| / |↑n| + C / ↑(m * n) := by rw [abs_div]
      _ ≤ (m - 1) * C / m / n + C / ↑(m * n) := by rw [Nat.abs_cast, add_le_add_iff_right]; exact div_le_div_of_nonneg_right h' (Nat.cast_nonneg' n)
      _ ≤ ((m - 1) * C + C) / (m * n) := by simp only [Nat.cast_mul]; field_simp; simp
      _ ≤ (m * C) / (m * n) := by exact div_le_div_of_nonneg_right (by linarith) (by simp [mpos])
      _ ≤ C / ↑n := by ring_nf; field_simp; simp

  have : C ≥ 0 := by
    have pos := abs_nonneg (a (2 + 1) - a 2 - a 1)
    have := h 2 1 (by simp)
    exact Preorder.le_trans 0 |a (2 + 1) - a 2 - a 1| C pos (h_bound 2 1)

  -- I n is nonempty
  have h_I_nonempty (n : ℕ) : ∃ x, x ∈ I n := by
    -- n can be zero or positive
    use (a n) / n
    dsimp [I]
    rw [sub_self, abs_zero]
    obtain rfl | npos := Nat.eq_zero_or_pos n
    · simp
    · positivity

  let h_Icc (n : ℕ) := Set.Icc ((a n) / n - C / n) ((a n) / n + C / n)

  have h_I_Icc (n : ℕ) : I n = h_Icc n := by
    ext x
    exact ⟨fun x => Set.mem_Icc_iff_abs_le.mp x, fun x => Set.mem_Icc_iff_abs_le.2 x⟩

  -- let J be the intersection of all I_n for n in N
  let J := ⋂ n ∈ (Set.univ : Set ℕ+), I n
  -- J is nonempty
  have h_J_nonempty : ∃ x, x ∈ J := by
    dsimp only [J]
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · simp only [Directed, Set.mem_univ, Set.iInter_true]
      intro x y
      use (x*y)
      constructor
      · rw [mul_comm x y]
        exact h_I y x (by simp)
      · exact h_I x y (by simp)
    · simp [Set.Nonempty, h_I_nonempty]
    · simp [h_I_Icc]
      exact fun i => isCompact_Icc
    · simp only [Set.mem_univ, h_I_Icc, Set.iInter_true]
      exact fun i => isClosed_Icc
  -- Let x be the element in the intersection of all the I_n
  obtain ⟨x, hx⟩ := h_J_nonempty
  -- then x is what the sequence (a n)/n converges to
  use x
  simp only
  have : (Filter.Tendsto (fun n ↦ a n / (n : ℝ)) Filter.atTop (nhds x)) := by
    by_cases h : C = 0
    -- the case where C = 0 implies that the whole sequence is constant and equal to x
    · subst_vars
      simp_all [h_Icc, J, I]
      have (n : ℕ+) : (a n) / (n : ℝ) = x := by
        have := hx n
        exact this.symm
      rw [Metric.tendsto_atTop]
      intro e pos_e
      use 1
      intro n n_ge_1
      simp only [dist]
      have := this ⟨n, by omega⟩
      simp only [PNat.mk_coe] at this
      simpa [this]
    · have C_pos : C > 0 := lt_of_le_of_ne this fun a => h (id (Eq.symm a))
      rw [Metric.tendsto_atTop]
      intro e he
      simp only [ge_iff_le, dist]
      simp only [Set.mem_univ, Set.iInter_true, Set.mem_iInter, Set.mem_setOf_eq, J, I] at hx
      obtain ⟨N, hN⟩ := arch_nat C_pos he
      use N
      intro n N_le_n
      have zero_lt_n : n > 0 := Nat.lt_of_lt_of_le N.property N_le_n
      have x_in_interval := hx ⟨n, zero_lt_n ⟩
      simp only [PNat.mk_coe] at x_in_interval
      have N_le_n : (N : ℝ) ≤ n := Nat.cast_le.mpr N_le_n
      have zero_lt_N : 0 < (N : ℝ) := Nat.cast_pos'.mpr N.property
      have : 1 / (N : ℝ) ≥ 1 / (n : ℝ) := by
        exact one_div_le_one_div_of_le (α := ℝ) zero_lt_N N_le_n
      calc |(a n) / (n : ℝ) - x|
      _ ≤ C / (n : ℝ)     := x_in_interval
      _ = C * (n : ℝ)⁻¹   := by field_simp
      _ ≤ C * (N : ℝ)⁻¹   := by simp_all
      _ < C * (e / (2*C)) := by simp_all
      _ = e / 2           := by
                              field_simp
      _ < e               := by simp_all
  constructor
  · trivial
  · intro y hy
    exact tendsto_nhds_unique hy this

lemma sequence_convergence
  (a : ℕ → ℝ) -- sequence indexed by integers
  (C : ℝ) -- the constant from the bound
  (h_bound : ∀ m n : ℕ, |a (m + n) - a m - a n| ≤ C) :
  ∃ θ : ℝ, -- exists unique θ
  -- conclusion: θ is the limit of a_n/n at +∞
  (Filter.Tendsto (fun n ↦ a n / (n : ℝ)) Filter.atTop (nhds θ)) := by
  obtain ⟨t, ht, _⟩ := sequence_convergence_unique a C h_bound
  use t
