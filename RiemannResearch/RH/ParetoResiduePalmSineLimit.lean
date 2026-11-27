import RiemannResearch.RH.ParetoResidueSineLimit
import RiemannResearch.RH.ParetoResidueFrequencyKernel
import RiemannResearch.Analysis.MontgomeryPrimeProbeEnergy

/-!
# Fixed-center reduced Palm limit of the Pareto residue kernel

Schur subtraction at the origin commutes with the microscopic limit because the
unfolded diagonal at the origin tends to one. The diagonal of the limiting
kernel gives the integrand of Montgomery's positive-gap prediction. The
determinants below refer to the auxiliary Mellin kernel.

Source: Mellin_Prime_Orbit_Montgomery_PCC_Handoff, §§1 and 6 (2026-11-27).
For the interpretation of the Schur subtraction as a reduced Palm kernel see
Shirai and Takahashi, J. Funct. Anal. 205 (2003), Theorem 6.5.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open SpectralObstruction

/-- Residue frequency kernel in units of its fixed-center mean spacing. -/
def unfoldedResidueKernel (N : ℕ) (t₀ x y : ℝ) : ℂ :=
  phaseStrippedCross
    (t₀ + 2 * Real.pi * x / Real.log ((N : ℝ) + 1))
    (t₀ + 2 * Real.pi * y / Real.log ((N : ℝ) + 1)) N

/-- Remove evaluation at the origin. The probabilistic interpretation uses a
nonzero denominator, which holds eventually in the fixed-center limit. -/
def palmAtOrigin (K : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  K x y - K x 0 * K 0 y / K 0 0

/-- Unit-intensity sine kernel after deleting the conditioned point. -/
def reducedSineKernel (x y : ℝ) : ℝ :=
  Real.sinc (Real.pi * (x - y)) - Real.sinc (Real.pi * x) * Real.sinc (Real.pi * y)

private def gaugeLeft (x : ℝ) : ℂ := Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I)
private def gaugeRight (x : ℝ) : ℂ := Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)

private theorem gauge_cancel (x : ℝ) : gaugeLeft x * gaugeRight x = 1 := by
  simp [gaugeLeft, gaugeRight, ← Complex.exp_add, neg_mul]

private theorem scaled_gauge (x y : ℝ) :
    logPhaseKernel (2 * Real.pi * (x - y)) =
      gaugeLeft x * (gaugeRight y * (Real.sinc (Real.pi * (x-y)) : ℂ)) := by
  have hgap : 2 * Real.pi * x - 2 * Real.pi * y = 2 * Real.pi * (x-y) := by ring
  have hhalf : 2 * Real.pi * (x-y) / 2 = Real.pi * (x-y) := by ring
  have hscale (u : ℝ) : (((2 * Real.pi * u : ℝ) : ℂ) / 2) =
      ((Real.pi * u : ℝ) : ℂ) := by push_cast; ring
  simpa only [hgap, hhalf, hscale, gaugeLeft, gaugeRight] using
    logPhaseKernel_sub_gauge (2 * Real.pi * x) (2 * Real.pi * y)

theorem unfoldedResidueKernel_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (t₀ x y : ℝ) :
    Tendsto (fun j => unfoldedResidueKernel (N j) t₀ x y) atTop
      (𝓝 (logPhaseKernel (2 * Real.pi * (x - y)))) := by
  have hNat : Tendsto (fun j => (N j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by
      change (N j : ℝ) ≤ (N j : ℝ) + 1
      linarith) (tendsto_natCast_atTop_atTop.comp hN)
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hNat)
  let t : ℕ → ℝ → ℝ := fun j a =>
    t₀ + 2 * Real.pi * a / Real.log ((N j : ℝ) + 1)
  have ht (a : ℝ) : Tendsto (fun j => t j a) atTop (𝓝 t₀) := by
    simpa only [t, div_eq_mul_inv, mul_zero, add_zero, Function.comp_apply] using
      ((hinv.const_mul (2 * Real.pi * a)).const_add t₀)
  have hpos : ∀ᶠ j in atTop, 0 < N j := hN.eventually (eventually_gt_atTop 0)
  apply phaseStrippedCross_microscopic_tendsto N (fun j => t j x) (fun j => t j y) _ hpos
  · have he : ∀ᶠ j in atTop, (t j x - t j y) * Real.log ((N j : ℝ) + 1) =
          2 * Real.pi * (x - y) := by
      filter_upwards [hpos] with j hj
      have hp : 0 < Real.log ((N j : ℝ) + 1) := Real.log_pos (by
        have hn : 0 < (N j : ℝ) := by exact_mod_cast hj
        linarith)
      dsimp only [t]
      field_simp [hp.ne']
      ring
    exact (tendsto_congr' he).2 tendsto_const_nhds
  · have hb := (continuous_microscopicCrossBudget.tendsto (t₀, t₀)).comp
      ((ht x).prodMk_nhds (ht y))
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using hb.mul hinv

theorem unfoldedResidueKernel_origin_eventually_ne_zero (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (t₀ : ℝ) :
    ∀ᶠ j in atTop, unfoldedResidueKernel (N j) t₀ 0 0 ≠ 0 := by
  have h : Tendsto (fun j => unfoldedResidueKernel (N j) t₀ 0 0) atTop (𝓝 1) := by
    simpa using unfoldedResidueKernel_tendsto N hN t₀ 0 0
  exact h.eventually_ne (by norm_num)

/-- Pointwise fixed-center convergence including the two unitary phase factors. -/
theorem unfoldedResidueKernel_palm_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (t₀ x y : ℝ) :
    Tendsto (fun j => palmAtOrigin (unfoldedResidueKernel (N j) t₀) x y) atTop
      (𝓝 (Complex.exp (-((Real.pi * x : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((Real.pi * y : ℝ) : ℂ) * Complex.I) *
          (reducedSineKernel x y : ℂ)))) := by
  have h := unfoldedResidueKernel_tendsto N hN t₀
  have h00 : Tendsto (fun j => unfoldedResidueKernel (N j) t₀ 0 0) atTop (𝓝 1) := by
    simpa using h 0 0
  have hp := (h x y).sub (((h x 0).mul (h 0 y)).div h00 (by norm_num))
  have he :
      logPhaseKernel (2 * Real.pi * (x-y)) -
        logPhaseKernel (2 * Real.pi * (x-0)) * logPhaseKernel (2 * Real.pi * (0-y)) / 1 =
      gaugeLeft x * (gaugeRight y * (reducedSineKernel x y : ℂ)) := by
    rw [scaled_gauge x y, scaled_gauge x 0, scaled_gauge 0 y]
    simp [gaugeLeft, gaugeRight, reducedSineKernel] <;> ring
  rw [he] at hp
  exact hp

theorem unfoldedResidueKernel_palm_det_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (t₀ : ℝ) (x : ι → ℝ) :
    Tendsto (fun j => Matrix.det (fun i k =>
      palmAtOrigin (unfoldedResidueKernel (N j) t₀) (x i) (x k))) atTop
      (𝓝 (Matrix.det (fun i k => (reducedSineKernel (x i) (x k) : ℂ)))) := by
  let S : Matrix ι ι ℂ := fun i k => (reducedSineKernel (x i) (x k) : ℂ)
  let G : Matrix ι ι ℂ := Matrix.of (fun i k => gaugeLeft (x i) *
    (Matrix.of (fun a b => gaugeRight (x b) * S a b)) i k)
  have hentry : Tendsto (fun j i k =>
      palmAtOrigin (unfoldedResidueKernel (N j) t₀) (x i) (x k)) atTop (𝓝 G) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k =>
      unfoldedResidueKernel_palm_tendsto N hN t₀ (x i) (x k)
  have hd := (continuous_id.matrix_det.tendsto G).comp hentry
  have hGS : G.det = S.det := by
    dsimp only [G]
    rw [Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc, ← Finset.prod_mul_distrib]
    simp only [gauge_cancel, Finset.prod_const_one, one_mul]
  simp only [id_eq, hGS] at hd
  exact hd

theorem reducedSineKernel_diag (x : ℝ) :
    reducedSineKernel x x = 1 - Real.sinc (Real.pi * x) ^ 2 := by
  simp [reducedSineKernel, pow_two]

theorem unfoldedResidueKernel_palm_diag_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (t₀ x : ℝ) :
    Tendsto (fun j => palmAtOrigin (unfoldedResidueKernel (N j) t₀) x x) atTop
      (𝓝 ((1 - Real.sinc (Real.pi * x) ^ 2 : ℝ) : ℂ)) := by
  have h := unfoldedResidueKernel_palm_tendsto N hN t₀ x x
  change Tendsto _ _ (𝓝 (gaugeLeft x * (gaugeRight x * (reducedSineKernel x x : ℂ)))) at h
  rwa [← mul_assoc, gauge_cancel, one_mul, reducedSineKernel_diag] at h

/-- The loss on the diagonal is exactly the continuum prime-probe energy density. -/
theorem reducedSineKernel_diag_add_primeContinuumProbe (x : ℝ) :
    reducedSineKernel x x +
        ‖RiemannResearch.Analysis.MontgomeryPrimeTrace.primeContinuumProbe x‖ ^ 2 = 1 := by
  rw [reducedSineKernel_diag,
    RiemannResearch.Analysis.MontgomeryPrimeTrace.norm_primeContinuumProbe_eq, sq_abs]
  ring


open RiemannResearch.Analysis.MontgomeryPositiveGap

/-- The limiting auxiliary Palm intensity integrates to the ordinary positive-gap target. -/
theorem reducedSineKernel_diag_integral (q : ℝ) :
    (∫ x in (0 : ℝ)..q, reducedSineKernel x x) = sineGapMass q := by
  simp only [reducedSineKernel_diag, sineGapMass]

/-- PCC for actual occurrences is equivalent to this anchored deficit for the
fixed-center auxiliary Palm intensity at each positive rational width. -/
theorem positiveGapPCC_iff_rationalPalmDiagonalDeficit :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => sampledArgumentIncrement T q) atTop
        (𝓝 ((∫ x in (0 : ℝ)..(q : ℝ), reducedSineKernel x x) - q)) := by
  simpa only [reducedSineKernel_diag_integral] using
    positiveGapPCC_iff_rationalSampledArgumentIncrement

end RiemannResearch.RH.Pareto.ResidueMellin
