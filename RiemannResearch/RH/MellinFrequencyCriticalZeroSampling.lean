import RiemannResearch.RH.MellinFrequencyScalingTargets
import RiemannResearch.RH.ProjectedDualMellinWitness
import RiemannResearch.RH.QFullDivisorProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Legal Mellin kernel determinants at actual critical zeros

Source: the user's Mellin/prime-orbit PCC handoff, §§1, 7–9. The
inverse-Gram kernel of the finite Pareto residue prefix has a common zeta
envelope. Every minor sampled on a tuple containing a critical-line zero
has determinant zero. The physical heights and the unfolding can vary with
the stage. The limit obstructions concern pointwise evaluation of this
specified kernel representative. They do not assert a gap distribution.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.MellinFrequency
open CoefficientStabilization RiemannResearch.Analysis.ComplexKernel

/-- Every vector of a finite legal prefix, in any basis, vanishes at a
supplied critical zero under the physical Mellin transform. -/
theorem finiteLegalFeature_at_criticalZero (n : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ finiteSpace n) {t : ℝ} (ht : riemannZeta (criticalPoint t) = 0) :
    paretoMellin f (criticalPoint t) = 0 :=
  paretoMellin_eq_zero_of_mem_finiteSpace n f hf _ (by simp) (criticalPoint_ne_one t) ht

open RiemannResearch.RH.QFullDivisorProjection RiemannResearch.RH.QSquarefreeLatticePackets
open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.ZetaTwoParetoTransfer
open RiemannResearch.RH.QParetoEquivalence

/-- Every vector in the physical full-divisor stage of period L is in the
legal prefix through conductor L+1. The divisor-one generator is zero. -/
theorem fullDivisorStage_le_finiteSpace (L : ℕ+) :
    paretoStage L ≤ finiteSpace (L : ℕ) := by
  rw [paretoStage, divisorStage, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro f ⟨q, ⟨d, hd, rfl⟩, rfl⟩
  have hpos := Nat.pos_of_dvd_of_pos hd L.pos
  have hle := Nat.le_of_dvd L.pos hd
  by_cases h : d = 1
  · subst d
    rw [qResidue_one, map_zero]
    exact (finiteSpace (L : ℕ)).zero_mem
  · let i : Fin (L : ℕ) := ⟨d - 2, by omega⟩
    have hi : i.val + 2 = d := by dsimp [i]; omega
    change toPareto (qResidue d) ∈ finiteSpace (L : ℕ)
    rw [← hi, toPareto_residueAtom]
    exact Submodule.subset_span ⟨i, rfl⟩

/-- Any finite collection of full-divisor legal features, including any
orthonormal basis used to form its projection kernel, is zero at the supplied
critical zero. Thus its feature Gram kernel vanishes on this row. -/
theorem fullDivisorFeatureKernel_row_zero {κ : Type*} [Fintype κ]
    (L : ℕ+) (w : κ → ThresholdHilbert) (hw : ∀ k, w k ∈ paretoStage L)
    {t : ℝ} (ht : riemannZeta (criticalPoint t) = 0) (u : ℝ) :
    ∑ k, paretoMellin (w k) (criticalPoint t) *
      star (paretoMellin (w k) (criticalPoint u)) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  rw [finiteLegalFeature_at_criticalZero (L : ℕ) (fullDivisorStage_le_finiteSpace L (hw k)) ht,
    zero_mul]

/-- At every full-divisor period, any sampled evaluation determinant
containing a critical zero is zero, for any finite basis or family. -/
theorem fullDivisorFeatureKernel_sample_det_zero {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (L : ℕ+) (w : κ → ThresholdHilbert) (hw : ∀ k, w k ∈ paretoStage L)
    (t : ι → ℝ) (i : ι) (hi : riemannZeta (criticalPoint (t i)) = 0) :
    (Matrix.of fun j l => ∑ k, paretoMellin (w k) (criticalPoint (t j)) *
      star (paretoMellin (w k) (criticalPoint (t l)))).det = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero i (fun l => fullDivisorFeatureKernel_row_zero L w hw hi (t l))

/-- Exact factorization of every finite evaluation determinant. It allows
repeated heights, arbitrary rank, and an empty tuple. -/
theorem kernel_sample_det_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (t : ι → ℝ) :
    (Matrix.of fun i j => kernel n (t i) (t j)).det =
      (∏ i, ((‖zetaEnvelope (t i)‖ : ℂ) ^ 2)) *
        (Matrix.of fun i j => core n (t i) (t j)).det := by
  let A : Matrix ι ι ℂ := Matrix.of fun i j => core n (t i) (t j)
  let v : ι → ℂ := fun i => zetaEnvelope (t i)
  let B : Matrix ι ι ℂ := Matrix.of fun i j => star (v j) * A i j
  have hmat : (Matrix.of fun i j => kernel n (t i) (t j)) =
      Matrix.of (fun i j => v i * B i j) := by
    ext i j
    simp only [Matrix.of_apply, B, A, v, kernel_factorization, envelopeKernel, mul_assoc]
  rw [hmat, Matrix.det_mul_column, show B.det = (∏ i, star (v i)) * A.det from
    Matrix.det_mul_row (fun i => star (v i)) A, ← mul_assoc, ← Finset.prod_mul_distrib]
  simp [v, A, Complex.mul_conj']

/-- The physical two-point determinant equals the product of the two squared
zeta envelopes times the exact inverse-Gram core determinant. -/
theorem kernel_two_point_det_factorization (n : ℕ) (t u : ℝ) :
    Matrix.det !![kernel n t t, kernel n t u; kernel n u t, kernel n u u] =
      (‖zetaEnvelope t‖ : ℂ)^2 * (‖zetaEnvelope u‖ : ℂ)^2 *
        (core n t t * core n u u - (‖core n t u‖ : ℂ)^2) := by
  have h := kernel_sample_det_factorization n (![t, u] : Fin 2 → ℝ)
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.prod_univ_two] at h ⊢
  rw [← core_hermitian n u t, Complex.star_def, Complex.mul_conj'] at h
  exact h

/-- One zero height suffices, however many other heights are sampled. -/
theorem kernel_sample_det_zero_of_criticalZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (t : ι → ℝ) (i : ι) (hi : riemannZeta (criticalPoint (t i)) = 0) :
    (Matrix.of fun j k => kernel n (t j) (t k)).det = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero i (fun k => kernel_row_zero_of_zeta_zero n hi (t k))

/-- No gauge or Jacobian changes a zero evaluation row. -/
theorem scaledKernel_row_zero_at_criticalZero (p : FrequencyScaling) (m : ℕ) (x y : ℝ)
    (hz : riemannZeta (criticalPoint (p.center m + x / p.scale m)) = 0) :
    scaledKernel p m x y = 0 := by
  simp [scaledKernel, kernel_row_zero_of_zeta_zero _ hz]

/-- Any stationary sine scaling of the legal kernel eventually avoids exact
critical zeros at each fixed unfolded location, including its moving center. -/
theorem eventually_avoid_criticalZero_of_sine_limit {p : FrequencyScaling}
    (hp : SineKernelLimitTarget p) (x : ℝ) :
    ∀ᶠ m in atTop, riemannZeta (criticalPoint (p.center m + x / p.scale m)) ≠ 0 := by
  have hlim := hp.2.2 x x
  rw [sineKernel_diagonal] at hlim
  filter_upwards [hlim.eventually_ne (zero_ne_one.symm : (1 : ℂ) ≠ 0)] with m hm
  exact fun hz => hm (scaledKernel_row_zero_at_criticalZero p m x x hz)

/-- Strict sine-Palm intensity away from its conditioned point. -/
theorem sinePalmIntensity_pos {x : ℝ} (hx : x ≠ 0) :
    0 < 1 - Real.sinc (Real.pi * x) ^ 2 := by
  have hπx := mul_ne_zero Real.pi_ne_zero hx
  have hs : |Real.sinc (Real.pi * x)| < 1 := by
    rw [Real.sinc_of_ne_zero hπx, abs_div, div_lt_one (abs_pos.mpr hπx)]
    exact Real.abs_sin_lt_abs hπx
  have hsq := (sq_lt_sq).mpr (show |Real.sinc (Real.pi * x)| < |(1 : ℝ)| by simpa using hs)
  linarith

/-- If a further critical zero occurs frequently on a moving coordinate
sequence, its legal intensity cannot converge to a positive sine-Palm
intensity. In particular this rules out a proposed locally uniform diagonal
limit along any such convergent sequence of nonzero limiting offset. -/
theorem no_positive_palm_limit_at_sampled_criticalZeros (p : FrequencyScaling)
    (u : ℕ → ℝ) {x : ℝ} (hx : x ≠ 0)
    (hz : ∃ᶠ m in atTop, riemannZeta (criticalPoint (p.center m + u m / p.scale m)) = 0) :
    ¬ Tendsto (fun m => (scaledKernel p m (u m) (u m)).re) atTop
      (𝓝 (1 - Real.sinc (Real.pi * x) ^ 2)) := by
  intro hl
  have hn := hl.eventually_ne (ne_of_gt (sinePalmIntensity_pos hx))
  apply hz
  filter_upwards [hn] with m hm
  intro h
  exact hm (by simp [scaledKernel_row_zero_at_criticalZero p m (u m) (u m) h])

private theorem moving_diagonal_tendsto {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {u : ℕ → ℝ} {x : ℝ}
    (hf : Continuous f) (hu : Tendsto u atTop (𝓝 x)) (h : TendstoLocallyUniformly F f atTop) :
    Tendsto (fun m => F m (u m)) atTop (𝓝 (f x)) := by
  have hpair := tendstoLocallyUniformly_iff_forall_tendsto.mp h x
  have hh : Tendsto (fun n => (n, u n)) atTop ((atTop : Filter ℕ) ×ˢ 𝓝 x) :=
    tendsto_id.prodMk hu
  exact (hf.continuousAt.tendsto.comp hu).congr_uniformity (hpair.comp hh)

/-- A further critical zero at a rescaled offset converging to x ≠ 0
precludes locally uniform convergence of the legal diagonal to the
reduced-Palm sine intensity. The zero need only occur along a subsequence. -/
theorem not_locallyUniform_palm_at_sampled_criticalZeros (p : FrequencyScaling)
    (u : ℕ → ℝ) {x : ℝ} (hx : x ≠ 0) (hu : Tendsto u atTop (𝓝 x))
    (hz : ∃ᶠ m in atTop, riemannZeta (criticalPoint (p.center m + u m / p.scale m)) = 0) :
    ¬ TendstoLocallyUniformly (fun m y => (scaledKernel p m y y).re)
      (fun y => 1 - Real.sinc (Real.pi * y) ^ 2) atTop := by
  intro h
  have hc : Continuous (fun y : ℝ => 1 - Real.sinc (Real.pi * y) ^ 2) :=
    continuous_const.sub ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2)
  have hlim := moving_diagonal_tendsto (F := fun m y => (scaledKernel p m y y).re)
    (f := fun y : ℝ => 1 - Real.sinc (Real.pi * y) ^ 2) hc hu h
  exact no_positive_palm_limit_at_sampled_criticalZeros p u hx hz hlim

end RiemannResearch.RH.Pareto.MellinFrequency
