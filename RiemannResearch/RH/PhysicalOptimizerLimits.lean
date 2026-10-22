/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalSourceLimits
import RiemannResearch.RH.SquarefreeArithmeticSaturation
import RiemannResearch.RH.ParetoDefectContinuity

/-!
# Actual optimizer agreement and the remaining arithmetic endpoint

The complete Gram displacement between the ordinary mean-one optimizer and
the actual projection is exactly the signed-source penalty. On the primorial
chain this displacement tends to zero, in the physical norm and at each site.
Both actual complete errors tend unconditionally to 1 + 4*pi/Cinf.

Projection charge saturation is exactly the previously isolated centered
squarefree approximation assertion and therefore implies RH. This module
does not supply saturation or the analytic RH-to-squarefree reverse.
Source: user-directed continuation of PhysicalSourceLimits20261008.md;
exact physical projection completion and the established squarefree stage
equivalences. All signed terms and the complete displacement square are kept.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalOptimizerLimits
open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection PhysicalSourceLimits

/-- Exact complete physical norm of the mean-one correction to the actual projection. -/
theorem meanOne_projection_norm_gap (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoInner (synthesis s (constrainedOptimizer s - projectionCoefficients s))
      (synthesis s (constrainedOptimizer s - projectionCoefficients s)) =
        4 * Real.pi * (2 * Real.pi + mixedCharge s) ^ 2 /
          ((-inverseCharge s) * shiftedDeterminant s) := by
  rw [synthesis_gram]
  have hd := projection_error_decomposition s hs ho (constrainedOptimizer s)
  have hg := meanOne_projection_error_gap s hs ho
  rw [projection_error s hs ho] at hg
  linarith only [hd, hg]

theorem meanOne_projection_norm_gap_eq_signedCorrection (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoInner (synthesis s (constrainedOptimizer s - projectionCoefficients s))
      (synthesis s (constrainedOptimizer s - projectionCoefficients s)) =
        signedSourceCorrection s * sourceProjectionCharge s / (-inverseCharge s) := by
  rw [meanOne_projection_norm_gap s hs ho]
  unfold signedSourceCorrection sourceProjectionCharge
  field_simp [ne_of_lt (logarithmicCharge_neg s hs ho),
    ne_of_lt (inverseCharge_neg s hs ho), ne_of_gt (shiftedDeterminant_pos s hs ho)]

theorem primorial_meanOne_error_tendsto (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => paretoError
      (synthesis (primorialPackets n) (constrainedOptimizer (primorialPackets n))))
      atTop (𝓝 (1 + 4 * Real.pi / Cinf)) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 4 * Real.pi)
      atTop (𝓝 (4 * Real.pi))).div hC (ne_of_lt hCneg))
  simpa only [Pi.div_apply,
    constrainedOptimizer_error _ (primorialPackets_legal _) (primorialPackets_odd _)]
    using ht

theorem primorial_projection_error_tendsto (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => paretoError
      (synthesis (primorialPackets n) (projectionCoefficients (primorialPackets n))))
      atTop (𝓝 (1 + 4 * Real.pi / Cinf)) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    (primorial_projectionCharge_tendsto Cinf hCneg hC)
  simpa only [projection_error _ (primorialPackets_legal _) (primorialPackets_odd _),
    div_neg, sub_neg_eq_add] using ht

/-- The actual physical optimizers agree asymptotically, without an RH hypothesis. -/
theorem primorial_optimizer_norm_gap_tendsto_zero (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => paretoInner
      (synthesis (primorialPackets n)
        (constrainedOptimizer (primorialPackets n) - projectionCoefficients (primorialPackets n)))
      (synthesis (primorialPackets n)
        (constrainedOptimizer (primorialPackets n) - projectionCoefficients (primorialPackets n))))
      atTop (𝓝 0) := by
  have ht := (primorial_meanOne_error_tendsto Cinf hCneg hC).sub
    (primorial_projection_error_tendsto Cinf hCneg hC)
  have he (n : ℕ) : paretoError
      (synthesis (primorialPackets n) (constrainedOptimizer (primorialPackets n))) -
      paretoError (synthesis (primorialPackets n) (projectionCoefficients (primorialPackets n))) =
      paretoInner
        (synthesis (primorialPackets n)
          (constrainedOptimizer (primorialPackets n) - projectionCoefficients (primorialPackets n)))
        (synthesis (primorialPackets n)
          (constrainedOptimizer (primorialPackets n) -
            projectionCoefficients (primorialPackets n))) := by
    rw [synthesis_gram, projection_error _ (primorialPackets_legal n) (primorialPackets_odd n)]
    have hd := projection_error_decomposition (primorialPackets n)
      (primorialPackets_legal n) (primorialPackets_odd n)
      (constrainedOptimizer (primorialPackets n))
    linarith only [hd]
  simpa only [he, sub_self] using ht

theorem primorial_projectionCharge_tendsto_one_iff_endpoint (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => sourceProjectionCharge (primorialPackets n)) atTop (𝓝 1) ↔
      Cinf = -4 * Real.pi := by
  constructor
  · intro hQ
    have he := tendsto_nhds_unique (primorial_projectionCharge_tendsto Cinf hCneg hC) hQ
    have hh := (div_eq_iff (neg_ne_zero.mpr (ne_of_lt hCneg))).mp he
    linarith only [hh]
  · intro he
    subst Cinf
    have ht := primorial_projectionCharge_tendsto (-4 * Real.pi) hCneg hC
    have he : 4 * Real.pi / (-(-4 * Real.pi)) = (1 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    simpa only [he] using ht

theorem primorial_projection_error_tendsto_zero_iff_endpoint (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => paretoError
      (synthesis (primorialPackets n) (projectionCoefficients (primorialPackets n))))
      atTop (𝓝 0) ↔ Cinf = -4 * Real.pi := by
  constructor
  · intro h
    have he := tendsto_nhds_unique (primorial_projection_error_tendsto Cinf hCneg hC) h
    have hh : 4 * Real.pi / Cinf = -1 := by linarith only [he]
    have hf := (div_eq_iff (ne_of_lt hCneg)).mp hh
    linarith only [hf]
  · intro he
    subst Cinf
    have ht := primorial_projection_error_tendsto (-4 * Real.pi) hCneg hC
    have he : 1 + 4 * Real.pi / (-4 * Real.pi) = (0 : ℝ) := by
      field_simp [Real.pi_ne_zero]
      ring
    simpa only [he] using ht

theorem primorial_meanOne_error_tendsto_zero_iff_endpoint (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => paretoError
      (synthesis (primorialPackets n) (constrainedOptimizer (primorialPackets n))))
      atTop (𝓝 0) ↔ Cinf = -4 * Real.pi := by
  constructor
  · intro h
    have he := tendsto_nhds_unique (primorial_meanOne_error_tendsto Cinf hCneg hC) h
    have hh : 4 * Real.pi / Cinf = -1 := by linarith only [he]
    have hf := (div_eq_iff (ne_of_lt hCneg)).mp hh
    linarith only [hf]
  · intro he
    subst Cinf
    have ht := primorial_meanOne_error_tendsto (-4 * Real.pi) hCneg hC
    have he : 1 + 4 * Real.pi / (-4 * Real.pi) = (0 : ℝ) := by
      field_simp [Real.pi_ne_zero]
      ring
    simpa only [he] using ht

/-- The complete physical optimizer agreement also holds at every fixed site.
The zero site is anchored by the actual packet definition. -/
theorem primorial_optimizer_pointwise_gap_tendsto_zero (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf))
    (k : ℕ) :
    Tendsto (fun n =>
      synthesis (primorialPackets n) (constrainedOptimizer (primorialPackets n)) k -
        synthesis (primorialPackets n) (projectionCoefficients (primorialPackets n)) k)
      atTop (𝓝 0) := by
  by_cases hk : k = 0
  · subst k
    simp [synthesis, FiniteSchur.combination, ramanujanPacket, residue]
  let g (n : ℕ) : ℕ → ℝ := synthesis (primorialPackets n)
    (constrainedOptimizer (primorialPackets n) - projectionCoefficients (primorialPackets n))
  have hnorm : Tendsto (fun n => paretoInner (g n) (g n)) atTop (𝓝 0) :=
    primorial_optimizer_norm_gap_tendsto_zero Cinf hCneg hC
  have hb : ∀ n, ∃ C : ℝ, ∀ j, |(1 : ℝ) - g n j| ≤ C := by
    intro n
    have hOne : ∀ j : ℕ, |(1 : ℝ)| ≤ 1 := by
      intro j
      norm_num
    exact ⟨_, bounded_sub hOne (synthesis_bounded (primorialPackets n)
      (constrainedOptimizer (primorialPackets n) -
        projectionCoefficients (primorialPackets n)))⟩
  have he : Tendsto (fun n => paretoError (fun j => (1 : ℝ) - g n j))
      atTop (𝓝 0) := by
    have hex (n : ℕ) : paretoError (fun j => (1 : ℝ) - g n j) =
        paretoInner (g n) (g n) := by
      have hres : (fun j => (1 : ℝ) - (1 - g n j)) = g n := by
        funext j
        ring
      simp only [paretoError, hres]
    simpa only [hex] using hnorm
  have hp := paretoError_tendsto_coordinate hb he k (Nat.pos_of_ne_zero hk)
  have hz := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
    atTop (𝓝 1)).sub hp
  have hsub (n : ℕ) : g n k =
      synthesis (primorialPackets n) (constrainedOptimizer (primorialPackets n)) k -
        synthesis (primorialPackets n) (projectionCoefficients (primorialPackets n)) k := by
    simp only [g, synthesis, FiniteSchur.combination, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib]
  have hcancel : (fun n => (1 : ℝ) - (1 - g n k)) = (fun n => g n k) := by
    funext n
    ring
  rw [hcancel, sub_self] at hz
  simpa only [hsub] using hz

/-- The unconditional source limits identify projection saturation with the
same remaining physical charge endpoint. Neither assertion is supplied here. -/
theorem primorial_projectionCharge_saturation_iff_physical_charge :
    Tendsto (fun n => sourceProjectionCharge (primorialPackets n)) atTop (𝓝 1) ↔
      Tendsto (fun n => inverseCharge (primorialPackets n))
        atTop (𝓝 (-4 * Real.pi)) := by
  obtain ⟨Cinf, hbound, hC⟩ := SquarefreeStageExhaustion.exists_primorial_charge_limit
  have hC' : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf) := hC
  have hCneg : Cinf < 0 := hbound.2.trans_lt (by nlinarith [Real.pi_pos])
  have he : Tendsto (fun n => inverseCharge (primorialPackets n))
      atTop (𝓝 (-4 * Real.pi)) ↔ Cinf = -4 * Real.pi := by
    constructor
    · intro h
      exact tendsto_nhds_unique hC' h
    · intro h
      simpa only [h] using hC'
  exact (primorial_projectionCharge_tendsto_one_iff_endpoint Cinf hCneg hC').trans he.symm

/-- Actual inverse-Gram charge saturation is exactly complete centered
squarefree approximation, with no analytic reverse premise. -/
theorem primorial_projectionCharge_saturation_iff_squarefreeCenteredApproximation :
    Tendsto (fun n => sourceProjectionCharge (primorialPackets n)) atTop (𝓝 1) ↔
      SquarefreeTransfer.SquarefreeCenteredApproximation := by
  have heq : (fun n => ArithmeticCoreInertia.arithmeticInverseCharge
      (SquarefreeStageExhaustion.primorialPeriod n)
      (divisorPackets (SquarefreeStageExhaustion.primorialPeriod n))) =
      (fun n => inverseCharge (primorialPackets n)) := by
    funext n
    exact ArithmeticCoreInertia.arithmeticInverseCharge_eq_physical _ _
      (SquarefreeStageExhaustion.primorialPeriod_pos n)
      (divisorPackets_legal _) (divisorPackets_period _)
  have hc := SquarefreeArithmeticSaturation.squarefreeCenteredApproximation_iff_primorial_charge
  rw [heq] at hc
  exact primorial_projectionCharge_saturation_iff_physical_charge.trans hc.symm

/-- Saturation of the actual physical inverse Gram would imply RH. The
saturation premise retains the complete remaining arithmetic obligation. -/
theorem riemannHypothesis_of_primorial_projectionCharge_saturation
    (h : Tendsto (fun n => sourceProjectionCharge (primorialPackets n)) atTop (𝓝 1)) :
    RiemannHypothesis := by
  exact SquarefreeTransfer.riemannHypothesis_of_squarefreeCenteredApproximation
    (primorial_projectionCharge_saturation_iff_squarefreeCenteredApproximation.mp h)

/-- All actual optimizer error limits and optimizer agreement are supplied
unconditionally on the concrete primorial chain. The common limiting error
is identified exactly, while its vanishing remains the arithmetic endpoint. -/
theorem exists_primorial_complete_optimizer_limits :
    ∃ Cinf : ℝ, Cinf ∈ Set.Icc (-8 * Real.sqrt 3) (-4 * Real.pi) ∧
      Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf) ∧
      Tendsto (fun n => paretoError
        (synthesis (primorialPackets n) (constrainedOptimizer (primorialPackets n))))
        atTop (𝓝 (1 + 4 * Real.pi / Cinf)) ∧
      Tendsto (fun n => paretoError
        (synthesis (primorialPackets n) (projectionCoefficients (primorialPackets n))))
        atTop (𝓝 (1 + 4 * Real.pi / Cinf)) ∧
      Tendsto (fun n => paretoInner
        (synthesis (primorialPackets n)
          (constrainedOptimizer (primorialPackets n) - projectionCoefficients (primorialPackets n)))
        (synthesis (primorialPackets n)
          (constrainedOptimizer (primorialPackets n) -
            projectionCoefficients (primorialPackets n))))
        atTop (𝓝 0) ∧
      ∀ k : ℕ, Tendsto (fun n =>
        synthesis (primorialPackets n) (constrainedOptimizer (primorialPackets n)) k -
          synthesis (primorialPackets n) (projectionCoefficients (primorialPackets n)) k)
        atTop (𝓝 0) := by
  obtain ⟨Cinf, hbound, hC⟩ := SquarefreeStageExhaustion.exists_primorial_charge_limit
  have hC' : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf) := hC
  have hCneg : Cinf < 0 := hbound.2.trans_lt (by nlinarith [Real.pi_pos])
  exact ⟨Cinf, hbound, hC', primorial_meanOne_error_tendsto Cinf hCneg hC',
    primorial_projection_error_tendsto Cinf hCneg hC',
    primorial_optimizer_norm_gap_tendsto_zero Cinf hCneg hC',
    primorial_optimizer_pointwise_gap_tendsto_zero Cinf hCneg hC'⟩

end RiemannResearch.RH.Pareto.PhysicalOptimizerLimits
