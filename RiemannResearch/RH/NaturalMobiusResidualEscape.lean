import RiemannResearch.RH.ResidueGramCorrectionPairing
import RiemannResearch.RH.MobiusResidualEscape
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.Analysis.SublinearEnergyLimits

/-!
# Escape of raw Mobius residuals and the full inverse source energy

Source: user-requested continuation of the inverse-Gram correction problem,
24 September 2026. The argument combines the existing finite-dual
annihilation and totality theorems with exact Hilbert-space Pythagoras.
No mathematical novelty claim is made.

The raw residual pairs with the limiting residual to give its energy,
but annihilates the growing finite dual span. A positive limiting energy
therefore forces the raw norms, and the full quadratic inverse source
energies, to tend to infinity.

The cofinally bounded norm/energy criteria are conditional research
reductions. Their boundedness hypotheses remain OPEN. No dimension-uniform
absolute inverse bound or vanishing residual is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The complete limiting residual pairs with every raw residual to give its energy. -/
theorem naturalResidual_inner_limitResidual (n : ℕ) :
    inner ℝ (naturalResidual n) limitResidual = limitEnergy := by
  have hm : (∑ j : Fin n, mobiusVector n j • residueAtom j.val) ∈ closedSpace :=
    (Submodule.le_topologicalClosure _)
      (walkSpan_le residueAtom id n (mobiusSynthesis_mem n))
  have hz : inner ℝ (∑ j : Fin n, mobiusVector n j • residueAtom j.val)
      limitResidual = 0 :=
    (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hm
  rw [naturalResidual, inner_add_left, hz, add_zero, real_inner_comm]
  exact limitResidual_inner_one

/-- Finite dual annihilation extends to the actual finite orthogonal projection. -/
theorem naturalResidual_inner_dualProjection (n : ℕ) :
    inner ℝ (naturalResidual n) (dualCoordinateProjection limitResidual n) = 0 := by
  have hz (y : ThresholdHilbert)
      (hy : y ∈ walkSpan (fun i : ℕ => mobiusRieszHilbert (i+2)) id n) :
      inner ℝ (naturalResidual n) y = 0 := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have h := naturalResidual_inner_dual n i
      change inner ℝ (naturalResidual n) (-mobiusRieszHilbert (i.val+2)) = 0 at h
      simpa only [inner_neg_right, neg_eq_zero, id_eq] using h
    | zero => simp
    | add x y hx hy hix hiy => simp [inner_add_right, hix, hiy]
    | smul c x hx hix => simp [inner_smul_right, hix]
  change inner ℝ (naturalResidual n)
    ((walkSpan (fun i : ℕ => mobiusRieszHilbert (i+2)) id n).starProjection limitResidual) = 0
  exact hz _ (Submodule.starProjection_apply_mem _ _)

/-- The same nonvanishing pairing is carried by the shrinking dual error. -/
theorem naturalResidual_dual_error_pairing (n : ℕ) :
    inner ℝ (naturalResidual n)
      (limitResidual-dualCoordinateProjection limitResidual n) = limitEnergy := by
  rw [inner_sub_right, naturalResidual_inner_limitResidual,
    naturalResidual_inner_dualProjection, sub_zero]

/-- Exact Cauchy--Schwarz lower bound retaining the whole raw residual norm. -/
theorem naturalResidual_dual_error_bound (n : ℕ) :
    limitEnergy ^ 2 ≤ ‖naturalResidual n‖ ^ 2 *
      ‖limitResidual - dualCoordinateProjection limitResidual n‖ ^ 2 := by
  have hc := norm_inner_le_norm (𝕜 := ℝ) (naturalResidual n)
    (limitResidual - dualCoordinateProjection limitResidual n)
  have hE : 0 ≤ limitEnergy := sq_nonneg _
  rw [naturalResidual_dual_error_pairing, Real.norm_of_nonneg hE] at hc
  have hs := mul_self_le_mul_self hE hc
  simpa only [← pow_two, mul_pow] using hs

/-- Positive limiting energy forces raw residual norms to escape to infinity. -/
theorem naturalResidual_norm_tendsto_atTop (hE : 0 < limitEnergy) :
    Tendsto (fun n => ‖naturalResidual n‖) atTop atTop := by
  have hsmall : Tendsto (fun n =>
      ‖limitResidual-dualCoordinateProjection limitResidual n‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := limitResidual)).sub
      (dualCoordinateProjection_tendsto limitResidual)).norm
  apply RiemannResearch.Analysis.tendsto_atTop_of_pos_le_mul_tendsto_zero
    hE (Eventually.of_forall (fun n => norm_nonneg _)) hsmall
  exact Eventually.of_forall (fun n => by
    have hc := norm_inner_le_norm (𝕜 := ℝ) (naturalResidual n)
      (limitResidual-dualCoordinateProjection limitResidual n)
    rw [naturalResidual_dual_error_pairing, Real.norm_of_nonneg hE.le] at hc
    exact hc)

/-- Conditional research reduction: the cofinal raw norm bound is OPEN. -/
theorem riemannHypothesis_of_frequently_bounded_naturalResidual
    (C : ℝ) (hbounded : ∃ᶠ n : ℕ in atTop, ‖naturalResidual n‖ ≤ C) :
    RiemannHypothesis := by
  by_contra hRH
  have ht := naturalResidual_norm_tendsto_atTop (not_RH_limitEnergy_pos hRH)
  obtain ⟨n, hn, hn'⟩ := (hbounded.and_eventually (ht.eventually_gt_atTop C)).exists
  linarith


open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.Pareto.IntegerDPP

/-- The complete scalar quadratic form sᵀG⁻¹s for s=b+Gμ. -/
def inverseSourceEnergy (n : ℕ) : ℝ :=
  dotProduct (source n + (fullGram n).mulVec (mobiusVector n)) (correctionVector n)

/-- The pre-inversion correction source is the full raw residual Gram source. -/
theorem naturalResidual_cross (n : ℕ) :
    cross (fun i : Fin n => residueAtom i.val) (naturalResidual n) =
      source n + (fullGram n).mulVec (mobiusVector n) := by
  funext i
  simp [cross, naturalResidual, inner_add_right, inner_sum, inner_smul_right,
    source, Matrix.mulVec, dotProduct, fullGram, gramMatrix, mul_comm]

/-- The inverse quadratic form is a squared norm, with no truncation of physical tails. -/
theorem inverseSourceEnergy_eq_projection_norm_sq (n : ℕ) :
    inverseSourceEnergy n = ‖(finiteSpace n).starProjection (naturalResidual n)‖ ^ 2 := by
  have hp := projection_inner_eq_inverseGram (finiteResidue_independent n)
    (naturalResidual n) (naturalResidual n)
  change inner ℝ ((finiteSpace n).starProjection (naturalResidual n))
    ((finiteSpace n).starProjection (naturalResidual n)) = _ at hp
  rw [real_inner_self_eq_norm_sq, naturalResidual_cross] at hp
  exact hp.symm

/-- Exact Pythagorean split into inverse source energy and finite projection error. -/
theorem naturalResidual_norm_sq_eq_energy_add (n : ℕ) :
    ‖naturalResidual n‖ ^ 2 = energy n + inverseSourceEnergy n := by
  have hn : naturalResidual n - (finiteSpace n).starProjection (naturalResidual n) =
      hilbertOne - projection n := by
    simp only [naturalResidual, map_add,
      Submodule.starProjection_eq_self_iff.mpr (mobiusSynthesis_mem n)]
    change hilbertOne + _ - (projection n + _) = hilbertOne - projection n
    abel
  have hw : inner ℝ (naturalResidual n - (finiteSpace n).starProjection (naturalResidual n))
      ((finiteSpace n).starProjection (naturalResidual n)) = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal (naturalResidual n)) _
      (Submodule.starProjection_apply_mem _ _)
  have hp := norm_add_sq_real
    (naturalResidual n - (finiteSpace n).starProjection (naturalResidual n))
    ((finiteSpace n).starProjection (naturalResidual n))
  simp only [sub_add_cancel, hw, mul_zero, add_zero] at hp
  rw [hn, ← inverseSourceEnergy_eq_projection_norm_sq] at hp
  exact hp

/-- A positive limiting residual forces unbounded amplification of the full source energy. -/
theorem inverseSourceEnergy_tendsto_atTop (hE : 0 < limitEnergy) :
    Tendsto inverseSourceEnergy atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(naturalResidual_norm_tendsto_atTop hE).eventually_gt_atTop
    (|b| + |energy 0| + 1)] with n hn
  have he := energy_antitone (Nat.zero_le n)
  have hid := naturalResidual_norm_sq_eq_energy_add n
  have h1 := le_abs_self b
  have h2 := le_abs_self (energy 0)
  have h3 := abs_nonneg b
  have h4 := abs_nonneg (energy 0)
  nlinarith [sq_nonneg (‖naturalResidual n‖ - 1)]

/-- Conditional research reduction. A cofinal scalar inverse-energy bound suffices for RH;
no such bound is asserted or supplied. -/
theorem riemannHypothesis_of_frequently_bounded_inverseSourceEnergy
    (C : ℝ) (hbounded : ∃ᶠ n : ℕ in atTop, inverseSourceEnergy n ≤ C) :
    RiemannHypothesis := by
  by_contra hRH
  have ht := inverseSourceEnergy_tendsto_atTop (not_RH_limitEnergy_pos hRH)
  obtain ⟨n, hn, hn'⟩ := (hbounded.and_eventually (ht.eventually_gt_atTop C)).exists
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
