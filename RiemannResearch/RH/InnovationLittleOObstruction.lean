/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.PrimeGapCurvature

/-!
# A fixed-prefix little-o obstruction

For the bandwidth-two prefix energy from `PrimeGapCurvature`, positivity of
the pivots makes the energy nonnegative and monotone.  Consequently, the
literal asymptotic condition `o(1 / log N)` forces every innovation to
vanish.  This is a formal guardrail against using that fixed-prefix condition
as a nontrivial RH criterion; it does not prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

open Filter Asymptotics

theorem reciprocalLog_tendsto_zero :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (nhds 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

theorem ActualInnovationLittleO.tendsto_zero
    {energy : ℕ → ℝ} (h : ActualInnovationLittleO energy) :
    Tendsto energy atTop (nhds 0) := by
  exact h.trans_tendsto reciprocalLog_tendsto_zero

theorem nonnegative_monotone_tendsto_zero_eq_zero
    (energy : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ energy n)
    (hmono : Monotone energy)
    (hzero : Tendsto energy atTop (nhds 0)) :
    ∀ n, energy n = 0 := by
  intro n
  apply le_antisymm
  · apply ge_of_tendsto hzero
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hmono hm
  · exact hnonneg n

theorem bandwidthTwoEnergy_succ
    (pivot ell second delta : ℕ → ℝ) (N : ℕ) :
    bandwidthTwoEnergy pivot ell second delta (N + 1) =
      bandwidthTwoEnergy pivot ell second delta N +
        (bandwidthTwoInnovation ell second delta N) ^ 2 / pivot N := by
  simp [bandwidthTwoEnergy, Finset.sum_range_succ]

theorem bandwidthTwoEnergy_monotone
    (pivot ell second delta : ℕ → ℝ)
    (hpivot : ∀ i, 0 < pivot i) :
    Monotone (bandwidthTwoEnergy pivot ell second delta) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [bandwidthTwoEnergy_succ]
  exact le_add_of_nonneg_right
    (div_nonneg (sq_nonneg _) (hpivot N).le)

theorem bandwidthTwoInnovation_eq_zero_of_actualLittleO
    (pivot ell second delta : ℕ → ℝ)
    (hpivot : ∀ i, 0 < pivot i)
    (hsmall :
      ActualInnovationLittleO
        (bandwidthTwoEnergy pivot ell second delta)) :
    ∀ i, bandwidthTwoInnovation ell second delta i = 0 := by
  have henergy_zero :
      ∀ N, bandwidthTwoEnergy pivot ell second delta N = 0 :=
    nonnegative_monotone_tendsto_zero_eq_zero
      (bandwidthTwoEnergy pivot ell second delta)
      (fun N => bandwidthTwoEnergy_nonneg pivot ell second delta N
        (fun i _ => hpivot i))
      (bandwidthTwoEnergy_monotone pivot ell second delta hpivot)
      hsmall.tendsto_zero
  intro i
  have hinc := bandwidthTwoEnergy_succ pivot ell second delta i
  have hterm :
      (bandwidthTwoInnovation ell second delta i) ^ 2 / pivot i = 0 := by
    rw [henergy_zero (i + 1), henergy_zero i] at hinc
    simpa using hinc.symm
  rcases (div_eq_zero_iff.mp hterm) with hsq | hpivot_zero
  · exact sq_eq_zero_iff.mp hsq
  · exact (hpivot i).ne' hpivot_zero |>.elim

end RiemannResearch.RH.PrimeGapCurvature
