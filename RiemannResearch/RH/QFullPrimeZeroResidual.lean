/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualResidualSampling
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullResidualCorrectionCost
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.ZetaFockSpan
import RiemannResearch.Analysis.SampledGaugeCompleteness
import RiemannResearch.Analysis.ZeroSamplingQuadratic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Prime-Fock and actual-zero detection of the full-Q residual

Source: the user's request of 14 November 2026 to isolate the arithmetic
estimate that forces the actual residual to vanish, using the improved prime
and zero spaces. The existing full-conductor projection theorem supplies the
strong residual limit. ZetaFockKernel.fullIsometry supplies the actual
zeta-generated prime-Fock realization; all integer coordinates, including
composites, are retained.

The coefficient at positive n is sqrt(Q(n)) times the physical residual.
Its finite Dirichlet polynomial is evaluated at actual zero ordinates with
multiplicity. These are finite polynomial observations, not bounded evaluation
of the infinite zeta kernel on the critical line.

Given any positive uniform Selberg exponent, vanishing of every fixed-head
sampled energy is equivalent to vanishing of the limiting residual. Moreover,
density supplies cofinal sampling heights for any growing sequence of finite
heads, and vanishing of the resulting single energy sequence implies RH.
No uniform infinite-dimensional frame estimate or discarded-tail hypothesis
is used. The actual arithmetic cancellation remains explicitly Open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFullPrimeZeroResidual
open ZetaTwoHilbert QFullResidueProjection QFullResidualCorrectionCost QFullDisplacement
open RiemannResearch.Analysis.ActualResidualSampling
open RiemannResearch.Analysis.ActualZeroOrdinate
open RiemannResearch.Analysis.ZeroSamplingQuadratic

/-- Positive integer Dirichlet coordinates of the actual Q Hilbert vector. -/
def positiveCoefficients (f : QHilbert) (n : ℕ) : ℂ := (f (n - 1) : ℂ)


/-- Complexification of the genuine complete-Q coordinates. -/
def complexCoordinates (f : QHilbert) :
    RiemannResearch.Analysis.SampledGauge.Space ℕ :=
  ⟨fun n => (f n : ℂ), by
    apply Memℓp.of_norm
    simpa only [Complex.norm_real] using (lp.memℓp f).norm⟩

theorem complexCoordinates_norm (f : QHilbert) : ‖complexCoordinates f‖ = ‖f‖ := by
  have he : ‖complexCoordinates f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [RiemannResearch.Analysis.SampledGauge.norm_sq_eq_tsum, qNorm_sq]
    apply tsum_congr
    intro n
    simp [complexCoordinates, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg (complexCoordinates f), norm_nonneg f]

/-- The actual residual in the newly constructed zeta-generated prime Fock subspace.
No continuation of the positive zeta kernel to the critical strip is used. -/
def fockResidual (N : ℕ) :
    RiemannResearch.Analysis.ZetaFockKernel.coherentCombination.range.topologicalClosure :=
  RiemannResearch.Analysis.ZetaFockKernel.fullIsometry.symm (complexCoordinates (residual N))

theorem fockResidual_norm (N : ℕ) : ‖fockResidual N‖ = ‖residual N‖ := by
  rw [fockResidual, LinearIsometryEquiv.norm_map, complexCoordinates_norm]

theorem fockResidual_integer_coordinates (N n : ℕ) :
    RiemannResearch.Analysis.ZetaFockKernel.fullIsometry (fockResidual N) n =
      positiveCoefficients (residual N) (n + 1) := by
  simp [fockResidual, positiveCoefficients, complexCoordinates]

theorem positiveCoefficients_physical (f : QHilbert) (n : ℕ) :
    positiveCoefficients f (n + 1) =
      ((Real.sqrt (qWeight n) * qSequence f (n + 1) : ℝ) : ℂ) := by
  simp only [positiveCoefficients, Nat.add_sub_cancel, qSequence_succ]
  congr 1
  field_simp [(Real.sqrt_pos.mpr (qWeight_pos n)).ne']

/-- A finite-head observation, not a truncation of the Hilbert projection itself. -/
def sampledResidualEnergy (N H : ℕ) (T : ℝ) : ℝ :=
  sampledEnergy T (Finset.Icc 1 H) (positiveCoefficients (residual N))

private theorem cofinal_residual_tendsto (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => residual (N j)) atTop (𝓝 qResidual) := by
  exact tendsto_const_nhds.sub (candidate_tendsto_projection.comp hN)

/-- The samples and the inverse-Gram coefficients may move simultaneously.
Only a fixed finite observation head is used; no infinite frame bound enters. -/
theorem sampledResidualEnergy_tendsto
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (H : ℕ) :
    Tendsto (fun j => sampledResidualEnergy (N j) H (T j)) atTop
      (𝓝 (coefficientEnergy (Finset.Icc 1 H) (positiveCoefficients qResidual))) := by
  apply sampledEnergy_tendsto_of_coefficients ha hD
    (Finset.Icc 1 H) (fun n hn => (Finset.mem_Icc.mp hn).1) T hT
    (fun j => positiveCoefficients (residual (N j))) (positiveCoefficients qResidual)
  intro n hn
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 (n - 1)).continuous.continuousAt.tendsto).comp
      (cofinal_residual_tendsto N hN))

/-- Open arithmetic cancellation target for the actual residuals and actual
multiplicity-weighted zeta-zero samples. This definition supplies no proof. -/
def SampledResidualCancellation (N : ℕ → ℕ) (T : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, Tendsto (fun j => sampledResidualEnergy (N j) H (T j)) atTop (𝓝 0)

/-- The new prime/zero coordinate observations detect the full limiting residual.
This is an equivalence with the arithmetic target, not a cancellation provider. -/
theorem sampled_cancellation_iff_residual_zero
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    SampledResidualCancellation N T ↔ qResidual = 0 := by
  constructor
  · intro h
    have he (H : ℕ) :
        coefficientEnergy (Finset.Icc 1 H) (positiveCoefficients qResidual) = 0 :=
      tendsto_nhds_unique (sampledResidualEnergy_tendsto ha hD N hN T hT H) (h H)
    apply Subtype.ext
    funext k
    change qResidual k = 0
    have hmem : k + 1 ∈ Finset.Icc 1 (k + 1) := by simp
    have hsum := he (k + 1)
    unfold coefficientEnergy at hsum
    have hk : ‖positiveCoefficients qResidual (k + 1)‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => sq_nonneg
        ‖positiveCoefficients qResidual n‖)).mp hsum (k + 1) hmem
    have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp hk)
    simpa only [positiveCoefficients, Nat.add_sub_cancel, Complex.ofReal_eq_zero] using hz
  · intro h H
    simpa [h, positiveCoefficients, coefficientEnergy] using
      sampledResidualEnergy_tendsto ha hD N hN T hT H

theorem residual_tendsto_zero_of_sampled_cancellation
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hcancel : SampledResidualCancellation N T) :
    Tendsto (fun j => residual (N j)) atTop (𝓝 0) := by
  have hz := (sampled_cancellation_iff_residual_zero ha hD N hN T hT).mp hcancel
  simpa only [hz] using cofinal_residual_tendsto N hN

/-- Conditional RH consumer. The density hypothesis handles sampling;
the separate cancellation hypothesis is the remaining arithmetic obligation. -/
theorem riemannHypothesis_of_sampled_residual_cancellation
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hcancel : SampledResidualCancellation N T) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (qResidual_eq_zero_iff.mp
      ((sampled_cancellation_iff_residual_zero ha hD N hN T hT).mp hcancel))


/-- A single growing-head energy suffices when its finite observation
comparison is supplied. No bound on the discarded infinite tail is assumed:
the already-proved strong limit of the actual projections supplies tightness. -/
theorem residual_zero_of_growing_sampled_energy
    (N H : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hH : Tendsto H atTop atTop)
    (T : ℕ → ℝ)
    (hcompare : ∀ j, (1 / 2 : ℝ) *
      coefficientEnergy (Finset.Icc 1 (H j)) (positiveCoefficients (residual (N j))) ≤
        sampledResidualEnergy (N j) (H j) (T j))
    (henergy : Tendsto (fun j => sampledResidualEnergy (N j) (H j) (T j))
      atTop (𝓝 0)) :
    qResidual = 0 := by
  apply Subtype.ext
  funext k
  change qResidual k = 0
  have hcoord : Tendsto (fun j => (residual (N j)) k) atTop (𝓝 (qResidual k)) :=
    ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k).continuous.continuousAt.tendsto).comp
      (cofinal_residual_tendsto N hN)
  have hupper : ∀ᶠ j in atTop, ((residual (N j)) k) ^ 2 ≤
      2 * sampledResidualEnergy (N j) (H j) (T j) := by
    filter_upwards [hH.eventually (eventually_ge_atTop (k + 1))] with j hj
    have hmem : k + 1 ∈ Finset.Icc 1 (H j) := by
      exact Finset.mem_Icc.mpr ⟨by omega, hj⟩
    have hle : ‖positiveCoefficients (residual (N j)) (k + 1)‖ ^ 2 ≤
        coefficientEnergy (Finset.Icc 1 (H j)) (positiveCoefficients (residual (N j))) :=
      Finset.single_le_sum (fun n _ => sq_nonneg
        ‖positiveCoefficients (residual (N j)) n‖) hmem
    have hle' : ((residual (N j)) k) ^ 2 ≤
        coefficientEnergy (Finset.Icc 1 (H j)) (positiveCoefficients (residual (N j))) := by
      simpa only [positiveCoefficients, Nat.add_sub_cancel, Complex.norm_real,
        Real.norm_eq_abs, sq_abs] using hle
    linarith [hcompare j]
  have hzero : (qResidual k) ^ 2 ≤ 0 := by
    have he : Tendsto (fun j => 2 * sampledResidualEnergy (N j) (H j) (T j))
        atTop (𝓝 0) := by simpa using henergy.const_mul 2
    exact le_of_tendsto_of_tendsto (hcoord.pow 2) he hupper
  exact sq_eq_zero_iff.mp (le_antisymm hzero (sq_nonneg _))

/-- Density supplies the sampling schedule for any cofinal residual and head
sequences. Vanishing of the one displayed arithmetic energy is still open. -/
theorem exists_cofinal_sampling_RH_test
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (N H : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hH : Tendsto H atTop atTop) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      (Tendsto (fun j => sampledResidualEnergy (N j) (H j) (T j)) atTop (𝓝 0) →
        RiemannHypothesis) := by
  obtain ⟨T, hT, hb⟩ := exists_cofinal_detection_schedule ha hD
    (fun j => Finset.Icc 1 (H j)) (fun j n hn => (Finset.mem_Icc.mp hn).1)
  refine ⟨T, hT, fun henergy => ?_⟩
  apply riemannHypothesis_of_qOne_mem_full_closure
  apply qResidual_eq_zero_iff.mp
  exact residual_zero_of_growing_sampled_energy N H hN hH T
    (fun j => (hb j (positiveCoefficients (residual (N j)))).1) henergy

end RiemannResearch.RH.QFullPrimeZeroResidual
