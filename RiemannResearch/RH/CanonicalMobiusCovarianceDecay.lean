import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.ParetoSublinearResidualTail
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Fixed-test decay of canonical Möbius residual covariances

Source: independently developed from the repository's exact tail-shift identity,
Cauchy--Schwarz inequality, and established PNT sublinear energy estimate during
the user's investigation of complete signed covariance energy. No mathematical
novelty is claimed.

The complete pairing satisfies
`inner(f, one - F_N)^2 ≤ A²/(N+1) * ‖one - F_N‖²`
when the physical sequence of the fixed test `f` is bounded in absolute value by
`A`. Its limit is zero by the unconditional PNT estimate. In particular, each
fixed canonical residual decorrelates from later residuals, including along
prime cutoffs.

The bound is not uniform as the first test varies. These results do not assert
weak convergence against every Hilbert vector, a bound for a moving covariance
matrix, or uniformly bounded cofinal signed or convex averages. The complete
covariance bound required for squarefree closure remains open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto

/-- Complete residual pairing estimate; the physical bound is on the fixed test. -/
theorem canonicalResidual_inner_sq_le (f : ThresholdHilbert) (N : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n, 0 < n → |hilbertSequence f n| ≤ A) :
    (inner ℝ f (hilbertOne - canonicalMobiusHilbert N)) ^ 2 ≤
      (A ^ 2 / ((N : ℝ) + 1)) * ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 := by
  have he : ∀ n < N, (hilbertOne - canonicalMobiusHilbert N) n = 0 := by
    intro n hn
    have hs := canonicalMobiusHilbert_exact N (n + 1) (by omega) (by omega)
    have hone : hilbertSequence hilbertOne (n + 1) = 1 := by
      rw [hilbertOne_sequence]
      simp [zeroAnchor]
    have hsame : hilbertSequence hilbertOne (n+1) =
        hilbertSequence (canonicalMobiusHilbert N) (n+1) := hone.trans hs.symm
    have hw : Real.sqrt (paretoWeight n) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      unfold paretoWeight
      positivity
    have hc : hilbertOne n = canonicalMobiusHilbert N n := (div_left_inj' hw).mp hsame
    change hilbertOne n - canonicalMobiusHilbert N n = 0
    exact sub_eq_zero.mpr hc
  exact (hilbertTailShift_inner_sq_le f _ N he).trans
    (mul_le_mul_of_nonneg_right (hilbertTailShift_norm_sq_le_of_bounded f N A hA hf)
      (sq_nonneg _))

/-- PNT gives convergence against every fixed bounded physical test sequence.
This does not assert convergence against all Hilbert vectors. -/
theorem canonicalResidual_inner_tendsto_zero_of_bounded (f : ThresholdHilbert)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n, 0 < n → |hilbertSequence f n| ≤ A) :
    Tendsto (fun N => inner ℝ f (hilbertOne - canonicalMobiusHilbert N))
      atTop (𝓝 0) := by
  have hsub := error_energy_div_tendsto_zero_of_energy
    canonicalMobiusHilbert canonicalMobiusHilbert_sublinear
  have hu : Tendsto (fun N => A ^ 2 *
      (‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using hsub.const_mul (A ^ 2)
  have hs : Tendsto (fun N =>
      (inner ℝ f (hilbertOne - canonicalMobiusHilbert N)) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) _ hu
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    calc
      _ ≤ (A ^ 2 / ((N : ℝ) + 1)) *
          ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 :=
        canonicalResidual_inner_sq_le f N A hA hf
      _ ≤ (A ^ 2 / (N : ℝ)) * ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 := by
        gcongr
        linarith
      _ = _ := by ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht

/-- Each fixed canonical residual decorrelates from the later canonical residuals.
The first cutoff is fixed throughout the limit. -/
theorem canonicalResidual_covariance_tendsto_zero (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N => inner ℝ (hilbertOne - canonicalMobiusHilbert K)
      (hilbertOne - canonicalMobiusHilbert N)) atTop (𝓝 0) := by
  apply canonicalResidual_inner_tendsto_zero_of_bounded
    (hilbertOne - canonicalMobiusHilbert K) (1 + 2 * (K : ℝ)) (by positivity)
  intro n hn
  have hseq : hilbertSequence (hilbertOne - canonicalMobiusHilbert K) n =
      1 - canonicalMobiusHead K n := by
    change hilbertSequenceLinear (hilbertOne - canonicalMobiusHilbert K) n = _
    rw [map_sub]
    change hilbertSequence hilbertOne n - hilbertSequence (canonicalMobiusHilbert K) n = _
    rw [hilbertOne_sequence, canonicalMobiusHilbert_sequence]
    simp [zeroAnchor, ne_of_gt hn]
  rw [hseq]
  have hb := abs_le.mp (canonicalMobiusHead_abs_le_two_mul K hK n)
  apply abs_le.mpr
  constructor <;> linarith

end RiemannResearch.RH.Pareto
end
