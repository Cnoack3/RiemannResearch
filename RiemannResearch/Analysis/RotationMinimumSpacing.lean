import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer determinant spacing at a minimum approximation denominator

Source: the user-supplied DyadicRegularizedVerificationContinuation20260910
(1).md, September 10, 2026, off-diagonal Gram/prefix target.

The intended RH consumer is the logarithmic Gram majorant for the rotation
log 3 / log 2. This elementary spacing lemma requires no continued fractions.
It does not itself establish the logarithmic prefix bound or RH.
-/

namespace RiemannResearch.Analysis

/-- If the q-th integer approximation is no worse than the h-th, with h<q,
its nonzero error forces a quantitative lower bound on the earlier error.
The conclusion is division-free and does not require nearest-integer choices. -/
theorem integer_approximation_minimum_spacing_mul
    (α : ℝ) (h q : ℕ) (ph pq : ℤ)
    (hh : 0 < h) (hhq : h < q)
    (hqerr : 0 < |(q : ℝ) * α - (pq : ℝ)|)
    (hminimum : |(q : ℝ) * α - (pq : ℝ)| ≤
      |(h : ℝ) * α - (ph : ℝ)|) :
    1 < 2 * (q : ℝ) * |(h : ℝ) * α - (ph : ℝ)| := by
  let eh : ℝ := (h : ℝ) * α - (ph : ℝ)
  let eq : ℝ := (q : ℝ) * α - (pq : ℝ)
  change 0 < |eq| at hqerr
  change |eq| ≤ |eh| at hminimum
  change 1 < 2 * (q : ℝ) * |eh|
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hqR : (0 : ℝ) < q := lt_trans hhR (by exact_mod_cast hhq)
  have hltR : (h : ℝ) < q := by exact_mod_cast hhq
  have hdet : (q : ℤ) * ph - (h : ℤ) * pq ≠ 0 := by
    intro hz
    have hzR : (q : ℝ) * (ph : ℝ) - (h : ℝ) * (pq : ℝ) = 0 := by
      exact_mod_cast hz
    have hrel : (q : ℝ) * eh = (h : ℝ) * eq := by
      calc
        (q : ℝ) * eh = (h : ℝ) * eq -
            ((q : ℝ) * (ph : ℝ) - (h : ℝ) * (pq : ℝ)) := by
          dsimp [eh, eq]
          ring
        _ = (h : ℝ) * eq := by rw [hzR, sub_zero]
    have hrelabs := congrArg (fun x : ℝ => |x|) hrel
    rw [abs_mul, abs_mul, abs_of_pos hqR, abs_of_pos hhR] at hrelabs
    have hle := mul_le_mul_of_nonneg_left hminimum hqR.le
    have hstrict := mul_lt_mul_of_pos_right hltR hqerr
    linarith
  have hdetpos : (0 : ℤ) < |(q : ℤ) * ph - (h : ℤ) * pq| := abs_pos.mpr hdet
  have hdetone : (1 : ℤ) ≤ |(q : ℤ) * ph - (h : ℤ) * pq| := hdetpos
  have hdetoneR : (1 : ℝ) ≤
      |(q : ℝ) * (ph : ℝ) - (h : ℝ) * (pq : ℝ)| := by
    exact_mod_cast hdetone
  have hdetrewrite : (q : ℝ) * (ph : ℝ) - (h : ℝ) * (pq : ℝ) =
      (h : ℝ) * eq - (q : ℝ) * eh := by
    dsimp [eh, eq]
    ring
  rw [hdetrewrite] at hdetoneR
  have htri := abs_sub_le ((h : ℝ) * eq) 0 ((q : ℝ) * eh)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  rw [abs_mul, abs_mul, abs_of_pos hhR, abs_of_pos hqR] at htri
  have hp : 0 < |eh| := lt_of_lt_of_le hqerr hminimum
  have hle := mul_le_mul_of_nonneg_left hminimum hhR.le
  have hstrict := mul_lt_mul_of_pos_right hltR hp
  nlinarith

/-- The packing form of the integer-determinant spacing bound. -/
theorem integer_approximation_minimum_spacing
    (α : ℝ) (h q : ℕ) (ph pq : ℤ)
    (hh : 0 < h) (hhq : h < q)
    (hqerr : 0 < |(q : ℝ) * α - (pq : ℝ)|)
    (hminimum : |(q : ℝ) * α - (pq : ℝ)| ≤
      |(h : ℝ) * α - (ph : ℝ)|) :
    1 / (2 * (q : ℝ)) < |(h : ℝ) * α - (ph : ℝ)| := by
  have hq : 0 < q := lt_trans hh hhq
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
  have h := integer_approximation_minimum_spacing_mul α h q ph pq hh hhq hqerr hminimum
  nlinarith

end RiemannResearch.Analysis
