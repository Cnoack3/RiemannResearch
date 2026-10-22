/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalSourceLimits
import RiemannResearch.RH.ArithmeticCoreRHCriterion

/-!
# Quantitative zeta-zero obstruction for the actual physical charge

The already proved actual Mellin separation inequality is transferred to every
finite legal physical packet synthesis. The complete projection displacement
square and the ordinary-mean signed-source penalty remain in the estimates.
A hypothetical right-hand zeta zero forces a strictly positive limiting
physical error and quantitatively separates the charge limit from `-4 * pi`.

Source: the existing actual Mellin argument in `ThresholdRiemannHypothesis`,
and user-directed continuation of `PhysicalSourceLimits20261008.md`.
No zero-free assertion or RH-to-approximation provider is assumed here.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalZeroObstruction
open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection PhysicalSourceLimits

/-- The positive continuous Mellin evaluation obstruction in `Re(s) > 1/2`. -/
def zeroDefect (ρ : ℂ) : ℝ := (2 * ρ.re - 1) / ‖ρ‖ ^ 2

theorem zeroDefect_pos (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re) :
    0 < zeroDefect ρ := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    norm_num [h] at hρ
  exact div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hρ0) 2)

/-- The complete physical error has the existing quantitative Mellin lower bound.
Every positive physical coordinate is included; no tail cutoff is used. -/
theorem synthesis_zero_floor (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (c : s → ℝ) (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    zeroDefect ρ ≤ paretoError (synthesis s c) := by
  have hA : ∀ a ∈ ({n : ℕ | 0 < n} : Set ℕ), 0 < a := fun _ h => h
  obtain ⟨f, hf, hseq⟩ := legalSeedSpan_exists_hilbert
    {n : ℕ | 0 < n} hA
    (ArithmeticCoreRHCriterion.synthesis_mem_positiveSeedSpan s c hs)
  have hb := legalClosure_distance_sq_lower_bound_of_zeta
    {n : ℕ | 0 < n} hA ρ hρ hρ1 hz
    ((hilbertLegalSubspace {n : ℕ | 0 < n}).le_topologicalClosure hf)
  rw [hilbertOne_sub_norm_sq_eq_paretoError, hseq] at hb
  exact hb

theorem projection_zero_floor (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (ho : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    zeroDefect ρ ≤ 1 - sourceProjectionCharge s := by
  have hb := synthesis_zero_floor s hs (projectionCoefficients s) ρ hρ hρ1 hz
  rwa [projection_error s hs ho] at hb

/-- The full projection displacement square is retained beside the zero floor. -/
theorem complete_projection_zero_obstruction (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (c : s → ℝ) (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    zeroDefect ρ + (c - projectionCoefficients s) ⬝ᵥ
      (ramanujanGramMatrix s *ᵥ (c - projectionCoefficients s)) ≤
        paretoError (synthesis s c) := by
  rw [projection_error_decomposition s hs ho c]
  linarith [projection_zero_floor s hs ho ρ hρ hρ1 hz]

/-- The actual complete signed-source square survives the ordinary-mean bound. -/
theorem meanOne_zero_floor_with_signed_penalty (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    zeroDefect ρ +
      4 * Real.pi * (2 * Real.pi + mixedCharge s) ^ 2 /
        ((-inverseCharge s) * shiftedDeterminant s) ≤
          paretoError (synthesis s (constrainedOptimizer s)) := by
  have hb := synthesis_zero_floor s hs (projectionCoefficients s) ρ hρ hρ1 hz
  have he := meanOne_projection_error_gap s hs ho
  linarith only [hb, he]

/-- A hypothetical right-hand zero bounds the actual limiting projection. -/
theorem primorial_limiting_zero_floor (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf))
    (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    zeroDefect ρ ≤ 1 - 4 * Real.pi / (-Cinf) := by
  have ht : Tendsto (fun n => 1 - sourceProjectionCharge (primorialPackets n))
      atTop (𝓝 (1 - 4 * Real.pi / (-Cinf))) :=
    tendsto_const_nhds.sub (primorial_projectionCharge_tendsto Cinf hCneg hC)
  by_contra h
  have hlt : 1 - 4 * Real.pi / (-Cinf) < zeroDefect ρ := lt_of_not_ge h
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hlt)).exists
  exact (not_lt_of_ge (projection_zero_floor _
    (primorialPackets_legal n) (primorialPackets_odd n) ρ hρ hρ1 hz)) hn

theorem zeroDefect_lt_one_of_primorial_limit (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf))
    (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    zeroDefect ρ < 1 := by
  have hb := primorial_limiting_zero_floor Cinf hCneg hC ρ hρ hρ1 hz
  have hp : 0 < 4 * Real.pi / (-Cinf) := div_pos (by positivity) (neg_pos.mpr hCneg)
  linarith

/-- A right-hand zero quantitatively separates the actual charge endpoint. -/
theorem primorial_charge_limit_le_of_zeta_zero (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf))
    (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    Cinf ≤ -4 * Real.pi / (1 - zeroDefect ρ) := by
  have hb := primorial_limiting_zero_floor Cinf hCneg hC ρ hρ hρ1 hz
  have hδ := zeroDefect_lt_one_of_primorial_limit Cinf hCneg hC ρ hρ hρ1 hz
  have hm : 4 * Real.pi / (-Cinf) ≤ 1 - zeroDefect ρ := by linarith
  have hmul := (div_le_iff₀ (neg_pos.mpr hCneg)).mp hm
  apply (le_div_iff₀ (sub_pos.mpr hδ)).mpr
  nlinarith only [hmul]

theorem primorial_charge_limit_lt_endpoint_of_zeta_zero
    (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf))
    (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    Cinf < -4 * Real.pi := by
  have hb := primorial_charge_limit_le_of_zeta_zero Cinf hCneg hC ρ hρ hρ1 hz
  have hδ := zeroDefect_lt_one_of_primorial_limit Cinf hCneg hC ρ hρ hρ1 hz
  have hδpos := zeroDefect_pos ρ hρ
  have hquot : 4 * Real.pi < 4 * Real.pi / (1 - zeroDefect ρ) :=
    (lt_div_iff₀ (sub_pos.mpr hδ)).mpr (by nlinarith [Real.pi_pos])
  have he : -4 * Real.pi / (1 - zeroDefect ρ) =
      -(4 * Real.pi / (1 - zeroDefect ρ)) := by ring
  rw [he] at hb
  simpa only [neg_mul] using hb.trans_lt (neg_lt_neg hquot)

end RiemannResearch.RH.Pareto.PhysicalZeroObstruction
