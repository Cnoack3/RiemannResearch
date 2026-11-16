import RiemannResearch.RH.MobiusAffineProfile
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import Mathlib.Tactic.Linarith

/-!
# Elementary signed-moment bounds for affine Mobius profiles
Source: the attached exact-head Green memorandum, agenda R5.
The existing elementary reciprocal-Mobius bound proves coefficient compactness
implies bounded signed moments without invoking PNT. The actual uniform
coefficient bound remains open.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.MobiusAffineProfile
open RiemannResearch.RH.Pareto

theorem normalized_mobius_sum_abs_le_one (x : ℕ) :
    |(∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ)) / (x : ℝ)| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have hxR : (0 : ℝ) < x := by exact_mod_cast Nat.pos_of_ne_zero hx
  have hs : |∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ)| ≤ (x : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 x, |(ArithmeticFunction.moebius d : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
      _ = _ := by simp
  rw [abs_div, abs_of_pos hxR]
  exact (div_le_iff₀ hxR).mpr (by simpa using hs)

/-- No PNT, asymptotic counting, or convergence hypothesis is needed. -/
theorem affine_signed_moment_abs_le (x : ℕ) (c0 c1 : ℝ) :
    |signedSum x (fun d => c0 + c1 * ((d : ℝ) / (x : ℝ)))| ≤ |c0| + |c1| := by
  by_cases hx : x = 0
  · simpa [hx, signedSum] using add_nonneg (abs_nonneg c0) (abs_nonneg c1)
  have hxpos := Nat.pos_of_ne_zero hx
  have hrec : |∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)| ≤ 1 :=
    mobiusReciprocalSum_abs_le_one x hxpos
  have hsum := normalized_mobius_sum_abs_le_one x
  rw [affine_signed_moment]
  calc
    _ = |c0 * (∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) +
      c1 * ((∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ)) / (x : ℝ))| := by
        congr 1
        ring
    _ ≤ |c0| * |∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)| +
      |c1| * |(∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ)) / (x : ℝ)| := by
        simpa only [abs_mul] using abs_add_le
          (c0 * (∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)))
          (c1 * ((∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ)) / (x : ℝ)))
    _ ≤ |c0| * 1 + |c1| * 1 := add_le_add
      (mul_le_mul_of_nonneg_left hrec (abs_nonneg c0))
      (mul_le_mul_of_nonneg_left hsum (abs_nonneg c1))
    _ = _ := by ring

theorem affine_signed_moment_le_of_coefficients (x : ℕ) (c0 c1 B : ℝ)
    (hB : |c0| + |c1| ≤ B) :
    signedSum x (fun d => c0 + c1 * ((d : ℝ) / (x : ℝ))) ≤ B :=
  (le_abs_self _).trans ((affine_signed_moment_abs_le x c0 c1).trans hB)

end RiemannResearch.RH.MobiusAffineProfile
