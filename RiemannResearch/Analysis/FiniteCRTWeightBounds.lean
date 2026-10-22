import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite complete-residue weight bounds

The terms are the literal Pareto residue weights
`1 / ((a + k * L) * (a + k * L + 1))`.
Every nonempty finite prefix retains its physical head term.
These finite statements neither define digamma nor formalize its asymptotic
expansion. They supply the head domination used in that analytic argument.

-/

noncomputable section

open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteCRTWeightBounds

/-- The physical Pareto weight of site `a + k * L`. -/
def residueTerm (a L : ℝ) (k : ℕ) : ℝ :=
  1 / ((a + (k : ℝ) * L) * (a + (k : ℝ) * L + 1))

/-- The first `N` terms, including `k = 0` whenever `N > 0`. -/
def residuePrefix (a L : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, residueTerm a L k

/-- The next `N` terms after the physical head. -/
def residueTail (a L : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, residueTerm a L (k + 1)

@[simp] theorem residueTerm_zero (a L : ℝ) :
    residueTerm a L 0 = 1 / (a * (a + 1)) := by
  simp [residueTerm]

theorem residueTerm_pos (a L : ℝ) (k : ℕ)
    (ha : 0 < a) (hL : 0 ≤ L) :
    0 < residueTerm a L k := by
  have hmul : 0 ≤ (k : ℝ) * L :=
    mul_nonneg (Nat.cast_nonneg k) hL
  have hx : 0 < a + (k : ℝ) * L := by linarith
  have hx1 : 0 < a + (k : ℝ) * L + 1 := by linarith
  exact one_div_pos.mpr (mul_pos hx hx1)

theorem residueTerm_nonneg (a L : ℝ) (k : ℕ)
    (ha : 0 < a) (hL : 0 ≤ L) :
    0 ≤ residueTerm a L k :=
  le_of_lt (residueTerm_pos a L k ha hL)

theorem residueTail_nonneg (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (hL : 0 ≤ L) :
    0 ≤ residueTail a L N := by
  unfold residueTail
  exact Finset.sum_nonneg fun k _ =>
    residueTerm_nonneg a L (k + 1) ha hL

theorem residueTail_succ_pos (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (hL : 0 ≤ L) :
    0 < residueTail a L (N + 1) := by
  have hprev := residueTail_nonneg a L N ha hL
  have hlast := residueTerm_pos a L (N + 1) ha hL
  unfold residueTail at hprev ⊢
  rw [Finset.sum_range_succ]
  linarith

/-- Exact finite decomposition: the actual physical head plus every retained
remaining tail term. No uniform residue law is substituted. -/
theorem residuePrefix_head_tail (a L : ℝ) (N : ℕ) :
    residuePrefix a L (N + 1) =
      1 / (a * (a + 1)) + residueTail a L N := by
  unfold residuePrefix residueTail
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- Every nonempty finite CRT residue prefix dominates its physical head. -/
theorem residuePrefix_head_le (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (hL : 0 ≤ L) :
    1 / (a * (a + 1)) ≤ residuePrefix a L (N + 1) := by
  rw [residuePrefix_head_tail]
  exact le_add_of_nonneg_right (residueTail_nonneg a L N ha hL)

theorem residuePrefix_succ_pos (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (hL : 0 ≤ L) :
    0 < residuePrefix a L (N + 1) := by
  have hhead : 0 < 1 / (a * (a + 1)) := by
    have ha1 : 0 < a + 1 := by linarith
    exact one_div_pos.mpr (mul_pos ha ha1)
  exact lt_of_lt_of_le hhead (residuePrefix_head_le a L N ha hL)

/-- Once a tail term is present, the finite prefix strictly exceeds its head. -/
theorem residuePrefix_head_lt (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (hL : 0 ≤ L) :
    1 / (a * (a + 1)) < residuePrefix a L ((N + 1) + 1) := by
  rw [residuePrefix_head_tail]
  exact lt_add_of_pos_right _ (residueTail_succ_pos a L N ha hL)

/-- Natural-index version in the requested range `a ≥ 1`, `L ≥ 1`. -/
theorem nat_residuePrefix_head_le (a L N : ℕ)
    (ha : 1 ≤ a) (hL : 1 ≤ L) :
    1 / ((a : ℝ) * ((a : ℝ) + 1)) ≤
      residuePrefix (a : ℝ) (L : ℝ) (N + 1) := by
  have haNat : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  have hLNat : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
  have haReal : 0 < (a : ℝ) := by exact_mod_cast haNat
  have hLReal : 0 < (L : ℝ) := by exact_mod_cast hLNat
  exact residuePrefix_head_le (a : ℝ) (L : ℝ) N haReal (le_of_lt hLReal)


/-- Each retained tail term is bounded by the inverse square of its block scale. -/
theorem residueTerm_tail_upper (a L : ℝ) (k : ℕ)
    (ha : 0 < a) (hL : 0 < L) :
    residueTerm a L (k + 1) ≤
      1 / (((k + 1 : ℕ) : ℝ) ^ 2 * L ^ 2) := by
  let b : ℝ := ((k + 1 : ℕ) : ℝ) * L
  have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ k
  have hb : 0 < b := mul_pos hk hL
  have hab : 0 ≤ a * b := mul_nonneg (le_of_lt ha) (le_of_lt hb)
  have hden : b ^ 2 ≤ (a + b) * (a + b + 1) := by
    nlinarith [sq_nonneg a]
  have hbSq : b ^ 2 = ((k + 1 : ℕ) : ℝ) ^ 2 * L ^ 2 := by
    dsimp [b]
    ring
  change 1 / ((a + b) * (a + b + 1)) ≤
    1 / (((k + 1 : ℕ) : ℝ) ^ 2 * L ^ 2)
  rw [← hbSq]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hb) hden

/-- A lower inverse-square bound retains the head-dependent denominator shift. -/
theorem residueTerm_tail_lower (a L : ℝ) (k : ℕ)
    (ha : 0 < a) (hL : 0 < L) :
    1 / (((k + 1 : ℕ) : ℝ) ^ 2 * (L + a + 1) ^ 2) ≤
      residueTerm a L (k + 1) := by
  let t : ℝ := ((k + 1 : ℕ) : ℝ)
  have ht1 : 1 ≤ t := by
    dsimp [t]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have ht : 0 < t := by linarith
  have hx : 0 < a + t * L := by
    have hprod := mul_pos ht hL
    linarith
  have hx1 : 0 < a + t * L + 1 := by linarith
  have hC : 0 < L + a + 1 := by linarith
  have htC : 0 < t * (L + a + 1) := mul_pos ht hC
  have hshift : 0 ≤ (t - 1) * (a + 1) := by
    apply mul_nonneg
    · linarith
    · linarith
  have hx1Bound : a + t * L + 1 ≤ t * (L + a + 1) := by
    nlinarith
  have hxBound : a + t * L ≤ t * (L + a + 1) := by
    linarith
  have hden : (a + t * L) * (a + t * L + 1) ≤
      (t * (L + a + 1)) ^ 2 := by
    have hmul := mul_le_mul hxBound hx1Bound
      (le_of_lt hx1) (le_of_lt htC)
    nlinarith
  have hdenPos : 0 < (a + t * L) * (a + t * L + 1) :=
    mul_pos hx hx1
  have htSq : (t * (L + a + 1)) ^ 2 =
      ((k + 1 : ℕ) : ℝ) ^ 2 * (L + a + 1) ^ 2 := by
    dsimp [t]
    ring
  change 1 / (((k + 1 : ℕ) : ℝ) ^ 2 * (L + a + 1) ^ 2) ≤
    1 / ((a + t * L) * (a + t * L + 1))
  rw [← htSq]
  exact one_div_le_one_div_of_le hdenPos hden

/-- Uniform finite `L⁻²` upper bound for the entire retained tail. -/
theorem residueTail_upper (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (hL : 0 < L) :
    residueTail a L N ≤
      (∑ k ∈ Finset.range N, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) / L ^ 2 := by
  unfold residueTail
  calc
    (∑ k ∈ Finset.range N, residueTerm a L (k + 1)) ≤
        ∑ k ∈ Finset.range N,
          (1 / ((k + 1 : ℕ) : ℝ) ^ 2) / L ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [div_div] using residueTerm_tail_upper a L k ha hL
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]

/-- Finite lower tail bound with the exact head-dependent denominator shift. -/
theorem residueTail_lower (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (hL : 0 < L) :
    (∑ k ∈ Finset.range N, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) /
      (L + a + 1) ^ 2 ≤ residueTail a L N := by
  calc
    (∑ k ∈ Finset.range N, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) /
        (L + a + 1) ^ 2 =
        ∑ k ∈ Finset.range N,
          (1 / ((k + 1 : ℕ) : ℝ) ^ 2) / (L + a + 1) ^ 2 := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ ≤ residueTail a L N := by
      unfold residueTail
      apply Finset.sum_le_sum
      intro k _
      simpa only [div_div] using residueTerm_tail_lower a L k ha hL

/-- A complete finite residue prefix lies between its physical head plus the two
inverse-square tail bounds. No digamma expansion is asserted by this theorem. -/
theorem residuePrefix_two_sided (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (hL : 0 < L) :
    1 / (a * (a + 1)) +
      (∑ k ∈ Finset.range N, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) /
        (L + a + 1) ^ 2 ≤ residuePrefix a L (N + 1) ∧
    residuePrefix a L (N + 1) ≤ 1 / (a * (a + 1)) +
      (∑ k ∈ Finset.range N, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) / L ^ 2 := by
  rw [residuePrefix_head_tail]
  exact ⟨add_le_add (le_refl _) (residueTail_lower a L N ha hL),
    add_le_add (le_refl _) (residueTail_upper a L N ha hL)⟩

end RiemannResearch.Analysis.FiniteCRTWeightBounds
