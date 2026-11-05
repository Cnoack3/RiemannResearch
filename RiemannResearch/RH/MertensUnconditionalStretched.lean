/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QProfileTailEnergy
import RiemannResearch.RH.QSquarefreeStretchedDisplacement
import RiemannResearch.Analysis.StretchedLogProductIncrement

/-!
# Pointwise displacement at the unconditional Mertens scale

The existing stretched displacement-tail theorem already incorporates the
unconditional Mertens estimate, including the legal exact-head and complete
energy arguments. We specialize the physical profile bound directly to its
actual weight. This avoids weakening the available tail exponent.
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QAnnihilatorTailEscape
open ZetaTwoHilbert ZetaTwoProbability QFiniteSupportDualCriterion

/-- An exponentially growing pointwise envelope gives bounded complete weighted
tail energy at its matching exponent. The increment bound is the sole shape
requirement on the arbitrary real sequence `φ`. -/
theorem exponential_profile_weighted_tail_bounded (u : QHilbert) (φ : ℕ → ℝ) (b D : ℝ)
    (hinc : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N < n →
      4 * b * (φ n - φ N) ≤ Real.log (n : ℝ) - Real.log (N : ℝ))
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence u n| ≤ D * Real.exp (b * φ n)) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) * Real.exp (-(2*b) * φ N) * ‖tail N u‖^2 ≤
      2 * D^2 / zetaTwo := by
  let H : ℕ → ℝ := fun n => Real.exp (b*φ n)
  have hshape (n : ℕ) (hn : 0 < (n:ℝ)) : H n ^ 2 / Real.sqrt (n:ℝ) =
      Real.exp (2*b*φ n - Real.log (n:ℝ)/2) := by
    dsimp only [H]
    rw [pow_two, ← Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn, ← Real.exp_sub]
    congr 1 <;> ring
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hd
  filter_upwards [hinc, eventually_ge_atTop (max N₀ 1)] with N hi hN
  have hN1 : 1 ≤ N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hprof (n : ℕ) (hn : N < n) : H n ^ 2 / Real.sqrt (n:ℝ) ≤
      H N ^ 2 / Real.sqrt (N:ℝ) := by
    have hnr : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    rw [hshape _ hnr, hshape _ hNr]
    exact Real.exp_le_exp.mpr (by linarith [hi n hn])
  have ht := profile_tail_energy_le u H D N hN1 hprof (fun n hn => hN₀ n (by omega))
  have he : Real.exp (-(2*b) * φ N) * H N ^ 2 = 1 := by
    dsimp only [H]; rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    rw [show -(2*b)*φ N + (b*φ N+b*φ N) = 0 by ring, Real.exp_zero]
  calc
    _ ≤ ((N:ℝ) * Real.exp (-(2*b)*φ N)) * ((2*D^2/zetaTwo) * H N^2 / (N:ℝ)) :=
      mul_le_mul_of_nonneg_left ht (mul_nonneg hNr.le (Real.exp_pos _).le)
    _ = (2*D^2/zetaTwo) * (Real.exp (-(2*b)*φ N) * H N^2) := by
      field_simp [hNr.ne'] <;> ring
    _ = _ := by rw [he, mul_one]

end RiemannResearch.RH.QAnnihilatorTailEscape

namespace RiemannResearch.RH.QSquarefreeStretchedDisplacement
open RiemannResearch.Analysis RiemannResearch.Analysis.StretchedTailWeights
open RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QAnnihilatorTailEscape QSquarefreeDisplacementRigidity QFiniteSupportDualCriterion

/-- At the unconditional Mertens exponent, a single fixed coefficient `b > 0`
makes pointwise exponential boundedness equivalent to vanishing of the actual
projection residual. The multiplicative constant is arbitrary. -/
theorem exists_residual_zero_iff_stretched_pointwise_displacement :
    ∃ b : ℝ, 0 < b ∧ (limitingResidual = 0 ↔ ∃ D : ℝ, ∀ᶠ n : ℕ in atTop,
      |qSequence displacement n| ≤ D * Real.exp (b *
        logProductPower (1/11) (6 + Real.log (n:ℝ)))) := by
  obtain ⟨a, ha, hfreq⟩ := exists_residual_zero_iff_frequently_bounded_stretched_displacement_tail
  let φ : ℕ → ℝ := fun n => logProductPower (1/11) (6 + Real.log (n:ℝ))
  let b : ℝ := a/2
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨b, hb, ?_⟩
  constructor
  · intro hr
    refine ⟨0, Eventually.of_forall (fun n => ?_)⟩
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    change |qSequenceLinear 0 n| ≤ _
    simp
  · rintro ⟨D, hD⟩
    have hi : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N < n →
        4*b*(φ n - φ N) ≤ Real.log (n:ℝ) - Real.log (N:ℝ) := by
      have hh := (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
          (shifted_logProductPower_eventual_log_increment (1/11) (4*b)
            (by norm_num) (by norm_num) (by positivity))
      filter_upwards [hh] with N hN n hn
      exact hN (n:ℝ) (by exact_mod_cast hn.le)
    have htail := exponential_profile_weighted_tail_bounded displacement φ b D hi hD
    have hab : 2*b = a := by dsimp [b]; ring
    apply hfreq.mpr
    refine ⟨2*D^2/zetaTwo, ?_⟩
    simpa only [arithmeticWeight, arithmeticDecay, hab, φ] using htail.frequently

/-- An unconditional positive fixed growth coefficient suffices for RH.
The coefficient comes from the checked Mertens estimate and its tail transfer. -/
theorem exists_riemannHypothesis_of_stretched_exponential_displacement :
    ∃ b : ℝ, 0 < b ∧ ∀ D : ℝ, (∀ᶠ n : ℕ in atTop,
      |qSequence displacement n| ≤ D * Real.exp (b *
        logProductPower (1/11) (6 + Real.log (n:ℝ)))) → RiemannHypothesis := by
  obtain ⟨b, hb, hiff⟩ := exists_residual_zero_iff_stretched_pointwise_displacement
  refine ⟨b, hb, fun D hd => ?_⟩
  have hr := hiff.mpr ⟨D, hd⟩
  have hm : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

/-- The only hypothesis on the actual displacement is the displayed little-o
bound. The Mertens estimate used here has already been proved in the project. -/
theorem riemannHypothesis_of_stretched_log_displacement
    (hd : Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      logProductPower (1/11) (6 + Real.log (n:ℝ))) atTop (𝓝 0)) : RiemannHypothesis := by
  obtain ⟨b, hb, hcrit⟩ := exists_riemannHypothesis_of_stretched_exponential_displacement
  apply hcrit 1
  have hL : Tendsto (fun n : ℕ => 6 + Real.log (n:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hΦ := (tendsto_logProductPower_atTop (1/11) (by norm_num)).comp hL
  filter_upwards [hd.eventually (gt_mem_nhds hb), hΦ.eventually (eventually_gt_atTop (0:ℝ))]
    with n hn hp
  have hlog := Real.exp_le_exp.mpr ((div_lt_iff₀ hp).1 hn).le
  rw [Real.exp_log (by positivity)] at hlog
  simp only [Function.comp_apply] at hlog
  linarith

end RiemannResearch.RH.QSquarefreeStretchedDisplacement
