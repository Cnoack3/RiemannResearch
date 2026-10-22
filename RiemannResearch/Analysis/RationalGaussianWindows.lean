import RiemannResearch.Analysis.GaussianSpectralWindows
import RiemannResearch.Analysis.MarkedLaplaceKernel

/-!
# Original rational marked Fourier windows via a finite Gaussian transform

Source: user manuscript's marked tail. The exact original weight
`4 / (4 + (γᵢ-γⱼ)^2)` is retained. The established positive Laplace energy
identifies the unmarked rational form with a nonnegative real function.
A Gaussian transform of its complete finite pair sum gives unit-frequency
window mass from the occurrence-square budget, without an infinite Fubini
step. The displayed arithmetic budget is still a separate actual Tsang input.
-/
noncomputable section
open MeasureTheory Complex ProbabilityTheory
open scoped BigOperators NNReal ComplexConjugate

namespace RiemannResearch.Analysis.RationalGaussianWindows
open GaussianCellGeometry
open MarkedLaplaceKernel

/-- The original rational pair weight is nonnegative. -/
theorem weight_nonneg (a : ℝ) : 0 ≤ 4 / (4 + a ^ 2) := by positivity

/-- Its complete pair mass admits the Gaussian majorant without removing any pair. -/
theorem weight_le_one (a : ℝ) : (4 : ℝ) / (4 + a ^ 2) ≤ 1 := by
  exact (div_le_one (by positivity : (0 : ℝ) < 4 + a ^ 2)).2 (by nlinarith [sq_nonneg a])

/-- The positive unmarked Laplace energy is exactly the real part of a finite pair sum. -/
theorem energy_eq_re {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q : ℝ) :
    energy s γ q = (kernelForm s γ q 0).re := by
  rw [kernelForm_zero_eq_energy]
  rfl

theorem energy_continuous {ι : Type*} (s : Finset ι) (γ : ι → ℝ) :
    Continuous (energy s γ) := by
  have heq : energy s γ = fun q => (kernelForm s γ q 0).re :=
    funext (energy_eq_re s γ)
  rw [heq]
  unfold kernelForm phase
  fun_prop

/-- Elementary finite amplitude bound for the genuine positive rational energy. -/
theorem energy_le_card_sq {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q : ℝ) :
    energy s γ q ≤ (s.card : ℝ) ^ 2 := by
  calc
    _ = ‖(energy s γ q : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (energy_nonneg s γ q)]
    _ = ‖kernelForm s γ q 0‖ := congrArg norm (kernelForm_zero_eq_energy s γ q).symm
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ‖(phase 0 (γ i) * phase q (γ i - γ j)) *
          ((4 / (4 + (γ i - γ j) ^ 2) : ℝ) : ℂ)‖ := by
      unfold kernelForm
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => norm_sum_le _ _))
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa only [norm_mul, phase_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weight_nonneg _), one_mul] using weight_le_one (γ i - γ j)
    _ = _ := by simp [pow_two]

/-- Exact marked finite expansion in the external frequency. -/
theorem kernelForm_frequency_expansion {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q r u t : ℝ) :
    kernelForm s γ (q + r * t) u =
      ∑ i ∈ s, ∑ j ∈ s,
        ((phase u (γ i) * phase q (γ i - γ j)) *
          ((4 / (4 + (γ i - γ j) ^ 2) : ℝ) : ℂ)) *
          GaussianSpectralWindows.phase (r * (γ i - γ j)) t := by
  unfold kernelForm
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hp : phase (q + r * t) (γ i - γ j) =
      phase q (γ i - γ j) * GaussianSpectralWindows.phase (r * (γ i - γ j)) t := by
    unfold phase GaussianSpectralWindows.phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp]
  ring

/-- Exact actual Gaussian transform of the original complete rational marked matrix. -/
theorem integral_kernelForm_gaussian {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q r u m : ℝ) :
    (∫ t, kernelForm s γ (q + r * t) u ∂gaussianReal m 1) =
      ∑ i ∈ s, ∑ j ∈ s,
        ((phase u (γ i) * phase q (γ i - γ j)) *
          ((4 / (4 + (γ i - γ j) ^ 2) : ℝ) : ℂ)) *
          ((Real.exp (-(r * (γ i - γ j)) ^ 2 / 2) : ℂ) *
            GaussianSpectralWindows.phase (r * (γ i - γ j)) m) := by
  have hint (i j : ι) : Integrable
      (fun t => ((phase u (γ i) * phase q (γ i - γ j)) *
          ((4 / (4 + (γ i - γ j) ^ 2) : ℝ) : ℂ)) *
          GaussianSpectralWindows.phase (r * (γ i - γ j)) t)
      (gaussianReal m 1) :=
    (GaussianSpectralWindows.phase_integrable_gaussian (r * (γ i - γ j)) m).const_mul _
  simp_rw [kernelForm_frequency_expansion]
  rw [integral_finsetSum s (fun i hi => integrable_finsetSum s (fun j hj => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (fun j hj => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, GaussianSpectralWindows.integral_phase_gaussian]

private theorem scale_square (a b r : ℝ) :
    (r * a / Real.sqrt 2 - r * b / Real.sqrt 2) ^ 2 = (r * (a - b)) ^ 2 / 2 := by
  rw [← sub_div, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Unconditional Gaussian marked integral bound by all occurrence cells. -/
theorem integral_kernelForm_gaussian_norm_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q r u m : ℝ) :
    ‖∫ t, kernelForm s γ (q + r * t) u ∂gaussianReal m 1‖ ≤
      6 * GaussianSpectralWindows.squareBudget s (fun i => r * γ i) := by
  rw [integral_kernelForm_gaussian]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ‖((phase u (γ i) * phase q (γ i - γ j)) *
          ((4 / (4 + (γ i - γ j) ^ 2) : ℝ) : ℂ)) *
          ((Real.exp (-(r * (γ i - γ j)) ^ 2 / 2) : ℂ) *
            GaussianSpectralWindows.phase (r * (γ i - γ j)) m)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => norm_sum_le _ _))
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, Real.exp (-(r * (γ i - γ j)) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, phase_norm, GaussianSpectralWindows.phase_norm,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg _),
        abs_of_pos (Real.exp_pos _), one_mul, mul_one]
      exact (mul_le_mul_of_nonneg_right (weight_le_one _) (Real.exp_nonneg _)).trans_eq
        (one_mul _)
    _ = ∑ i ∈ s, ∑ j ∈ s,
        Real.exp (-(r * γ i / Real.sqrt 2 - r * γ j / Real.sqrt 2) ^ 2) := by
      simp_rw [scale_square, neg_div]
    _ ≤ _ := gaussian_pair_mass_le s (fun i => r * γ i / Real.sqrt 2)

/-- Positive original-kernel energy has genuine Gaussian mean controlled by the cells. -/
theorem integral_energy_gaussian_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q r m : ℝ) :
    (∫ t, energy s γ (q + r * t) ∂gaussianReal m 1) ≤
      6 * GaussianSpectralWindows.squareBudget s (fun i => r * γ i) := by
  have heq : ((∫ t, energy s γ (q + r * t) ∂gaussianReal m 1 : ℝ) : ℂ) =
      ∫ t, kernelForm s γ (q + r * t) 0 ∂gaussianReal m 1 := by
    calc
      _ = ∫ t, (energy s γ (q + r * t) : ℂ) ∂gaussianReal m 1 :=
        (integral_complex_ofReal (f := fun t : ℝ => energy s γ (q + r * t))
          (μ := gaussianReal m 1)).symm
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => (kernelForm_zero_eq_energy s γ _).symm)
  have hn : 0 ≤ ∫ t, energy s γ (q + r * t) ∂gaussianReal m 1 :=
    integral_nonneg (fun t => energy_nonneg s γ _)
  calc
    _ = ‖((∫ t, energy s γ (q + r * t) ∂gaussianReal m 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
    _ = ‖∫ t, kernelForm s γ (q + r * t) 0 ∂gaussianReal m 1‖ := congrArg norm heq
    _ ≤ _ := integral_kernelForm_gaussian_norm_le s γ q r 0 m

private theorem density_energy_integrable {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q r m : ℝ) : Integrable (fun t => gaussianPDFReal m 1 t * energy s γ (q + r * t)) := by
  have hc : Continuous (fun t => energy s γ (q + r * t)) :=
    (energy_continuous s γ).comp (by fun_prop)
  have hpdf : Continuous (gaussianPDFReal m 1) := by
    unfold gaussianPDFReal
    fun_prop
  refine Integrable.mono' ((integrable_gaussianPDFReal m 1).mul_const ((s.card : ℝ) ^ 2))
    ((hpdf.mul hc).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (energy_nonneg s γ _))]
    exact mul_le_mul_of_nonneg_left (energy_le_card_sq s γ _) (gaussianPDFReal_nonneg _ _ _))

/-- Uniform unmarked original rational Fourier mass on every unit-frequency window. -/
theorem unit_window_energy_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q r b : ℝ) :
    (∫ t in Set.Icc b (b + 1), energy s γ (q + r * t)) ≤
      (6 / GaussianSpectralWindows.windowFloor) *
        GaussianSpectralWindows.squareBudget s (fun i => r * γ i) := by
  have hc : Continuous (fun t => energy s γ (q + r * t)) :=
    (energy_continuous s γ).comp (by fun_prop)
  have hi : IntegrableOn (fun t => energy s γ (q + r * t))
      (Set.Icc b (b + 1)) volume := hc.continuousOn.integrableOn_Icc
  have hd := density_energy_integrable s γ q r (b + 1 / 2)
  have hbound : GaussianSpectralWindows.windowFloor *
      (∫ t in Set.Icc b (b + 1), energy s γ (q + r * t)) ≤
        6 * GaussianSpectralWindows.squareBudget s (fun i => r * γ i) := by
    calc
      _ = ∫ t in Set.Icc b (b + 1),
          GaussianSpectralWindows.windowFloor * energy s γ (q + r * t) :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ t in Set.Icc b (b + 1),
          gaussianPDFReal (b + 1 / 2) 1 t * energy s γ (q + r * t) := by
        apply integral_mono_ae (hi.const_mul _) hd.restrict
        exact ae_restrict_of_forall_mem measurableSet_Icc (fun t ht =>
          mul_le_mul_of_nonneg_right (GaussianSpectralWindows.windowFloor_le_density ht)
            (energy_nonneg s γ _))
      _ ≤ ∫ t, gaussianPDFReal (b + 1 / 2) 1 t * energy s γ (q + r * t) :=
        setIntegral_le_integral hd (Filter.Eventually.of_forall (fun t =>
          mul_nonneg (gaussianPDFReal_nonneg _ _ _) (energy_nonneg s γ _)))
      _ = ∫ t, energy s γ (q + r * t) ∂gaussianReal (b + 1 / 2) 1 := by
        rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
        simp only [smul_eq_mul]
      _ ≤ _ := integral_energy_gaussian_le s γ q r (b + 1 / 2)
  calc
    _ ≤ (6 * GaussianSpectralWindows.squareBudget s (fun i => r * γ i)) /
        GaussianSpectralWindows.windowFloor :=
      (le_div_iff₀ GaussianSpectralWindows.windowFloor_pos).2 (by simpa only [mul_comm] using hbound)
    _ = _ := by ring

/-- Actual integral Cauchy implies the pointwise arithmetic-mean marked bound. -/
theorem kernelForm_norm_le_energy_mean {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q u : ℝ) :
    ‖kernelForm s γ q u‖ ≤ (energy s γ (q + u) + energy s γ q) / 2 := by
  have hcs := kernelForm_norm_sq_le s γ q u
  have hn1 := energy_nonneg s γ (q + u)
  have hn2 := energy_nonneg s γ q
  nlinarith [sq_nonneg (energy s γ (q + u) - energy s γ q), norm_nonneg (kernelForm s γ q u)]

/-- Literal integral-of-norm original rational marked Fourier mass, uniform in both centres. -/
theorem unit_window_absolute_marked_mass_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q r u b : ℝ) :
    (∫ t in Set.Icc b (b + 1), ‖kernelForm s γ (q + r * t) u‖) ≤
      (6 / GaussianSpectralWindows.windowFloor) *
        GaussianSpectralWindows.squareBudget s (fun i => r * γ i) := by
  have hcleft : Continuous (fun t => energy s γ (q + u + r * t)) :=
    (energy_continuous s γ).comp (by fun_prop)
  have hcright : Continuous (fun t => energy s γ (q + r * t)) :=
    (energy_continuous s γ).comp (by fun_prop)
  have hleft : IntegrableOn (fun t => energy s γ (q + u + r * t))
      (Set.Icc b (b + 1)) volume := hcleft.continuousOn.integrableOn_Icc
  have hright : IntegrableOn (fun t => energy s γ (q + r * t))
      (Set.Icc b (b + 1)) volume := hcright.continuousOn.integrableOn_Icc
  have hprod : IntegrableOn (fun t => ‖kernelForm s γ (q + r * t) u‖)
      (Set.Icc b (b + 1)) volume :=
    (show Continuous (fun t => ‖kernelForm s γ (q + r * t) u‖) by
      unfold kernelForm phase; fun_prop).continuousOn.integrableOn_Icc
  have hmono : (∫ t in Set.Icc b (b + 1), ‖kernelForm s γ (q + r * t) u‖) ≤
      (1 / 2 : ℝ) * ((∫ t in Set.Icc b (b + 1), energy s γ (q + u + r * t)) +
        (∫ t in Set.Icc b (b + 1), energy s γ (q + r * t))) := by
    calc
      _ ≤ ∫ t in Set.Icc b (b + 1), (1 / 2 : ℝ) *
          (energy s γ (q + u + r * t) + energy s γ (q + r * t)) := by
        apply integral_mono_ae hprod ((hleft.add hright).const_mul _)
        exact Filter.Eventually.of_forall (fun t => by
          dsimp only
          have h := kernelForm_norm_le_energy_mean s γ (q + r * t) u
          have harg : q + r * t + u = q + u + r * t := by ring
          simpa only [harg, div_eq_mul_inv, mul_comm, Pi.add_apply, one_mul] using h)
      _ = _ := by rw [integral_const_mul, integral_add hleft hright]
  have hl := unit_window_energy_le s γ (q + u) r b
  have hr := unit_window_energy_le s γ q r b
  linarith

/-- The half-open unit windows used in the Fourier-tail partition have the same mass. -/
theorem unit_window_absolute_marked_Ico_mass_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q r u b : ℝ) :
    (∫ t in Set.Ico b (b + 1), ‖kernelForm s γ (q + r * t) u‖) ≤
      (6 / GaussianSpectralWindows.windowFloor) *
        GaussianSpectralWindows.squareBudget s (fun i => r * γ i) := by
  rw [← integral_Icc_eq_integral_Ico]
  exact unit_window_absolute_marked_mass_le s γ q r u b

end RiemannResearch.Analysis.RationalGaussianWindows
