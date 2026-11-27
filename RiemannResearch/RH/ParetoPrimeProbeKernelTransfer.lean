import RiemannResearch.RH.ParetoResiduePalmSineLimit

/-!
# A kernel comparison between the prime probe and the unfolded Pareto model

The logarithmic prime probe uses positive Fourier frequencies. In the Pareto
orientation the change of gauge multiplies it by
`exp(-2πi(x-y))`. The continuum identity is exact. The finite approximation
retains both the microscopic Mellin error and the weighted prime-CDF error.
All ordinates in these estimates are evaluation coordinates.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open SpectralObstruction RiemannResearch.Analysis.MontgomeryPrimeTrace

def primeMellinGauge (u : ℝ) : ℂ := Complex.exp (-((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

/-- The positive-frequency prime measure, with the Mellin kernel's orientation. -/
def orientedPrimeKernel (T x y : ℝ) : ℂ :=
  primeMellinGauge (x-y) * primeFourierProbe T (x-y)

theorem primeMellinGauge_split (x y : ℝ) :
    primeMellinGauge (x-y) = primeMellinGauge x / primeMellinGauge y := by
  simp only [primeMellinGauge, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem norm_primeMellinGauge (u : ℝ) : ‖primeMellinGauge u‖ = 1 := by
  simp [primeMellinGauge, Complex.norm_exp, Complex.mul_re]

theorem primeMellinGauge_continuum_eq (u : ℝ) :
    primeMellinGauge u * primeContinuumProbe u = logPhaseKernel (2 * Real.pi * u) := by
  let v : ℝ := 2 * Real.pi * u
  rw [primeContinuumProbe_eq]
  change Complex.exp (-(v : ℂ) * Complex.I) * logPhaseKernel (-v) = logPhaseKernel v
  simp only [logPhaseKernel, Complex.ofReal_neg, neg_div, neg_neg, Real.sinc_neg,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem orientedPrimeKernel_error {T : ℝ} (hT : 1 < T) (x y : ℝ) :
    ‖orientedPrimeKernel T x y - logPhaseKernel (2 * Real.pi * (x-y))‖ ≤
      ((Real.log 4 + 4) / Real.log T) * (1 + 2 * Real.pi * |x-y|) := by
  rw [orientedPrimeKernel, ← primeMellinGauge_continuum_eq, ← mul_sub, norm_mul,
    norm_primeMellinGauge, one_mul]
  exact primeFourierProbe_error hT (x-y)

/-- Holds at arbitrary centers with the full center-dependent error budget. -/
theorem unfoldedResidueKernel_sub_orientedPrimeKernel_bound
    (N : ℕ) (hN : 0 < N) {T : ℝ} (hT : 1 < T) (t₀ x y : ℝ) :
    ‖unfoldedResidueKernel N t₀ x y - orientedPrimeKernel T x y‖ ≤
      microscopicCrossBudget
          (t₀ + 2 * Real.pi * x / Real.log ((N : ℝ) + 1))
          (t₀ + 2 * Real.pi * y / Real.log ((N : ℝ) + 1)) / Real.log ((N : ℝ) + 1) +
        ((Real.log 4 + 4) / Real.log T) * (1 + 2 * Real.pi * |x-y|) := by
  let t (z : ℝ) := t₀ + 2 * Real.pi * z / Real.log ((N : ℝ) + 1)
  have hp : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by
    have hn : 0 < (N : ℝ) := by exact_mod_cast hN
    linarith)
  have hg : (t x - t y) * Real.log ((N : ℝ) + 1) = 2 * Real.pi * (x-y) := by
    dsimp only [t]
    field_simp [hp.ne']
    ring
  have hm := phaseStrippedCross_sub_logPhaseKernel_le (t x) (t y) N hN
  rw [hg] at hm
  refine (norm_sub_le_norm_sub_add_norm_sub _ (logPhaseKernel (2 * Real.pi * (x-y))) _).trans ?_
  rw [norm_sub_rev (logPhaseKernel _) (orientedPrimeKernel _ _ _)]
  exact add_le_add hm (orientedPrimeKernel_error hT x y)

theorem orientedPrimeKernel_tendsto (x y : ℝ) :
    Tendsto (fun T => orientedPrimeKernel T x y) atTop
      (𝓝 (logPhaseKernel (2 * Real.pi * (x-y)))) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have h := (Real.tendsto_log_atTop.const_div_atTop (Real.log 4 + 4)).mul_const
    (1 + 2 * Real.pi * |x-y|)
  apply squeeze_zero_norm' _ (by simpa using h)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact orientedPrimeKernel_error hT x y

/-- The arithmetic cutoff and residue period may tend to infinity independently. -/
theorem unfoldedResidueKernel_sub_orientedPrimeKernel_tendsto (N : ℕ → ℕ) (T : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop) (t₀ x y : ℝ) :
    Tendsto (fun j => unfoldedResidueKernel (N j) t₀ x y - orientedPrimeKernel (T j) x y)
      atTop (𝓝 0) := by
  simpa using (unfoldedResidueKernel_tendsto N hN t₀ x y).sub
    ((orientedPrimeKernel_tendsto x y).comp hT)

/-- Deletion of the origin commutes with the cross-model comparison. -/
theorem palmAtOrigin_sub_orientedPrimeKernel_tendsto (N : ℕ → ℕ) (T : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop) (t₀ x y : ℝ) :
    Tendsto (fun j => palmAtOrigin (unfoldedResidueKernel (N j) t₀) x y -
      palmAtOrigin (orientedPrimeKernel (T j)) x y) atTop (𝓝 0) := by
  have hm := unfoldedResidueKernel_tendsto N hN t₀
  have hp (a b : ℝ) := (orientedPrimeKernel_tendsto a b).comp hT
  have hne : logPhaseKernel (2 * Real.pi * ((0 : ℝ)-0)) ≠ 0 := by simp
  have hM := (hm x y).sub (((hm x 0).mul (hm 0 y)).div (hm 0 0) hne)
  have hP := (hp x y).sub (((hp x 0).mul (hp 0 y)).div (hp 0 0) hne)
  simpa only [palmAtOrigin, Function.comp_apply, Pi.div_apply, sub_self] using hM.sub hP

/-- The finite prime Schur determinants and the auxiliary Mellin Schur
determinants have the same limit for every fixed tuple. -/
theorem orientedPrimeKernel_palm_det_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (x : ι → ℝ) :
    Tendsto (fun j => Matrix.det (fun i k =>
      palmAtOrigin (orientedPrimeKernel (T j)) (x i) (x k))) atTop
      (𝓝 (Matrix.det (fun i k => (reducedSineKernel (x i) (x k) : ℂ)))) := by
  let G : Matrix ι ι ℂ := fun i k =>
    Complex.exp (-((Real.pi * x i : ℝ) : ℂ) * Complex.I) *
      (Complex.exp (((Real.pi * x k : ℝ) : ℂ) * Complex.I) *
        (reducedSineKernel (x i) (x k) : ℂ))
  let M (j : ℕ) : Matrix ι ι ℂ := fun i k =>
    palmAtOrigin (unfoldedResidueKernel j 0) (x i) (x k)
  let P (j : ℕ) : Matrix ι ι ℂ := fun i k =>
    palmAtOrigin (orientedPrimeKernel (T j)) (x i) (x k)
  have hm : Tendsto M atTop (𝓝 G) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k =>
      unfoldedResidueKernel_palm_tendsto id tendsto_id 0 (x i) (x k)
  have hp : Tendsto P atTop (𝓝 G) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k => ?_
    have h := (unfoldedResidueKernel_palm_tendsto id tendsto_id 0 (x i) (x k)).sub
      (palmAtOrigin_sub_orientedPrimeKernel_tendsto id T tendsto_id hT 0 (x i) (x k))
    simpa only [sub_zero, sub_sub_cancel] using h
  have hmg : Tendsto (fun j => (M j).det) atTop (𝓝 G.det) :=
    (continuous_id.matrix_det.tendsto G).comp hm
  have hms := unfoldedResidueKernel_palm_det_tendsto id tendsto_id 0 x
  have he := tendsto_nhds_unique hmg hms
  rw [← he]
  exact (continuous_id.matrix_det.tendsto G).comp hp

end RiemannResearch.RH.Pareto.ResidueMellin
