/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.OrdinateLagPhase
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution

/-!
# Fourier cancellation and the diagonal law of chronological ordinate lags

This file assembles the existing finite phase-lag bound with scalar Fourier
cancellation. The samples are an explicitly supplied monotone real sequence.
No claim that an arbitrary sequence enumerates actual zeta zeros is made.
Actual zeta specialization additionally needs a multiplicity-preserving
chronological enumeration, its height/count control, and a checked provider
of scalar cancellation.

Source: independently derived assembly of one-point equidistribution and
telescoping chronological gaps. The classical analytic motivation is
Ford--Zaharescu, arXiv:math/0405459. No publication-novelty claim is made.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.OrdinateLagEquidistribution

theorem lagPhase_eq_zeroOrdinatePhase (u t : ℝ) :
    OrdinateLagPhase.phase u t = ZeroOrdinate.phase u t := by
  unfold OrdinateLagPhase.phase ZeroOrdinate.phase
  rw [mul_comm]

/-- The zero-lag average is exactly the already formalized one-point
Fourier average. Both normalizers count the same `n+1` samples. -/
theorem diagonalCorrelation_eq_mean (γ : ℕ → ℝ) (u v : ℝ) (n : ℕ) :
    OrdinateLagPhase.correlationMean
      (fun j => OrdinateLagPhase.phase u (γ j))
      (fun j => OrdinateLagPhase.phase v (γ j)) (n+1) 0 =
      ZeroOrdinate.mean n
        (fun j => ZeroOrdinate.phase (u-v) (γ j)) := by
  simp only [OrdinateLagPhase.correlationMean, Nat.add_zero,
    lagPhase_eq_zeroOrdinatePhase, ← ZeroOrdinate.phase_sub,
    ZeroOrdinate.mean, Complex.real_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The same one-point Fourier law controls a moving chronological lag.
The limit is diagonal: equal frequencies have correlation one. -/
theorem phase_correlation_limit_of_fourierCancellation
    (γ : ℕ → ℝ) (hγ : Monotone γ)
    (hcancel : ZeroOrdinate.FourierCancellation γ)
    (u v : ℝ) (lag : ℕ → ℕ)
    (hendpoint : Tendsto
      (fun J => (lag J : ℝ) * (γ (J + lag J) - γ 0) / (J : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun J => OrdinateLagPhase.correlationMean
        (fun j => OrdinateLagPhase.phase u (γ j))
        (fun j => OrdinateLagPhase.phase v (γ j)) J (lag J))
      atTop (𝓝 (if u = v then 1 else 0)) := by
  apply OrdinateLagPhase.phase_correlationMean_tendsto γ hγ u v lag
    (if u = v then 1 else 0) _ hendpoint
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  simp only [diagonalCorrelation_eq_mean]
  simpa only [sub_eq_zero] using
    ZeroOrdinate.phase_average_limit γ hcancel (u-v)

/-- Different frequencies remain asymptotically orthogonal even when the
second phase is sampled at a controlled moving lag. -/
theorem phase_crossCorrelation_tendsto_zero
    (γ : ℕ → ℝ) (hγ : Monotone γ)
    (hcancel : ZeroOrdinate.FourierCancellation γ)
    (u v : ℝ) (huv : u ≠ v) (lag : ℕ → ℕ)
    (hendpoint : Tendsto
      (fun J => (lag J : ℝ) * (γ (J + lag J) - γ 0) / (J : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun J => OrdinateLagPhase.correlationMean
        (fun j => OrdinateLagPhase.phase u (γ j))
        (fun j => OrdinateLagPhase.phase v (γ j)) J (lag J))
      atTop (𝓝 0) := by
  simpa only [if_neg huv] using
    phase_correlation_limit_of_fourierCancellation γ hγ hcancel u v lag hendpoint

end RiemannResearch.Analysis.OrdinateLagEquidistribution
