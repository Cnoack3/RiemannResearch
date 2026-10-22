import RiemannResearch.Analysis.ResidualGainProduct
import RiemannResearch.Analysis.FiniteHarmonicBounds
import Mathlib.Analysis.PSeries

/-!
# Harmonic lower bounds for exact relative Schur gains

Source: user-provided argument, `RH_Exact_Signed_Schur_Remainder_2026-09-16.tex`,
the dyadic cumulative-gain sufficient condition. This is a conditional scalar
consumer; it does not establish the required lower bound for arithmetic gains.

The more general finite-product and nonsummability equivalence are already in
`ResidualGainProduct`; this file must not redeclare them.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ResidualGain

/-- An actual pointwise harmonic lower bound implies an explicit finite residual
bound, preserving the exact recurrence before making the estimate. -/
theorem residual_le_exp_neg_harmonic {d r : ℕ → ℝ} {c : ℝ}
    (hd : 0 ≤ d 0) (h1 : ∀ n, r n ≤ 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n))
    (hlower : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ r n) (n : ℕ) :
    d n ≤ d 0 * Real.exp (-c * (harmonic n : ℝ)) := by
  have hsum : c * (harmonic n : ℝ) ≤ ∑ i ∈ Finset.range n, r i := by
    rw [RiemannResearch.Analysis.harmonic_cast_range, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      c * (1 / ((i : ℝ) + 1)) = c / ((i : ℝ) + 1) := by ring
      _ ≤ r i := hlower i
  rw [recurrence_eq_mul_product hrec]
  apply mul_le_mul_of_nonneg_left _ hd
  refine (survivalProduct_le_exp_neg_sum h1 n).trans ?_
  apply Real.exp_le_exp.mpr
  nlinarith

theorem not_summable_of_harmonic_lower {r : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hlower : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ r n) : ¬Summable r := by
  intro hs
  have hsmall : Summable (fun n : ℕ => c / ((n : ℝ) + 1)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hlower hs
  have hinv : Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹) := by
    simpa [div_eq_mul_inv, ← mul_assoc, ne_of_gt hc] using hsmall.mul_left c⁻¹
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hinv
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp hshift)

end RiemannResearch.Analysis.ResidualGain

/-! Source: boundary-observability handoff (16 September 2026), Section 26.
A harmonic relative loss exhausts any nonnegative energy sequence, including
finite termination. This does not supply the arithmetic loss inequality. -/
namespace RiemannResearch.Analysis.ResidualGain
open Filter
open scoped Topology BigOperators

theorem tendsto_zero_of_harmonic_loss {d : ℕ → ℝ} {a : ℝ}
    (hd : ∀ n, 0 ≤ d n) (ha : 0 < a)
    (hgain : ∀ n : ℕ, a/((n:ℝ)+1) * d n ≤ d n-d (n+1)) :
    Tendsto d atTop (𝓝 0) := by
  let q : ℕ → ℝ := fun n => min a 1 / ((n:ℝ)+1)
  have hq0 (n : ℕ) : 0 ≤ q n := by dsimp [q]; positivity
  have hq1 (n : ℕ) : q n ≤ 1 := by
    dsimp [q]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    have h := min_le_right a (1:ℝ)
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hstep (n : ℕ) : d (n+1) ≤ d n*(1-q n) := by
    have hqa : q n ≤ a/((n:ℝ)+1) :=
      div_le_div_of_nonneg_right (min_le_left a 1) (by positivity)
    have hmul := mul_le_mul_of_nonneg_right hqa (hd n)
    have hh := hgain n
    nlinarith
  have hbound (n : ℕ) : d n ≤ d 0*survivalProduct q n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [survivalProduct_succ]
      calc
        d (n+1) ≤ d n*(1-q n) := hstep n
        _ ≤ (d 0*survivalProduct q n)*(1-q n) :=
          mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr (hq1 n))
        _ = _ := by ring
  have hns : ¬ Summable q :=
    not_summable_of_harmonic_lower (lt_min ha zero_lt_one) (fun n => le_rfl)
  have hp := survivalProduct_tendsto_zero_of_not_summable hq0 hq1 hns
  have ht : Tendsto (fun n => d 0*survivalProduct q n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hp :
      Tendsto (fun n => d 0*survivalProduct q n) atTop (𝓝 (d 0*0)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht hd hbound

end RiemannResearch.Analysis.ResidualGain
