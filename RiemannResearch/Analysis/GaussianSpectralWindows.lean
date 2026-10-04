import RiemannResearch.Analysis.GaussianCellGeometry
import RiemannResearch.Analysis.MarkedIntegralCauchy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp

/-!
# Finite Gaussian spectral representation and unit-window mass

Source: user manuscript's deterministic Gaussian spectral-window step.
Uses the proved Mathlib characteristic function of `gaussianReal`.
The index set contains arbitrary occurrences, including repeated positions.
The only arithmetic input in applications is an explicitly supplied bound on
`squareBudget`; no actual Tsang moment estimate is supplied by this module.
-/
noncomputable section
open MeasureTheory Complex ProbabilityTheory
open scoped BigOperators NNReal ComplexConjugate

namespace RiemannResearch.Analysis.GaussianSpectralWindows
open GaussianCellGeometry

/-- Positive angular phase. -/
def phase (a t : ℝ) : ℂ := Complex.exp ((a * t : ℝ) * I)

@[simp] theorem phase_norm (a t : ℝ) : ‖phase a t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- All finite occurrences are retained, even when the position map repeats. -/
def amplitude {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q t : ℝ) : ℂ :=
  ∑ i ∈ s, phase (γ i) (q + t)

theorem amplitude_norm_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q t : ℝ) :
    ‖amplitude s γ q t‖ ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ i ∈ s, ‖phase (γ i) (q + t)‖ := norm_sum_le _ _
    _ = _ := by simp

theorem amplitude_memLp_gaussian {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q m : ℝ) : MemLp (amplitude s γ q) 2 (gaussianReal m 1) := by
  apply MemLp.of_bound (show AEStronglyMeasurable (amplitude s γ q)
    (gaussianReal m 1) from
      (show Continuous (amplitude s γ q) by unfold amplitude phase; fun_prop).aestronglyMeasurable)
    (s.card : ℝ)
  exact Filter.Eventually.of_forall (amplitude_norm_le s γ q)

theorem phase_integrable_gaussian (a m : ℝ) :
    Integrable (phase a) (gaussianReal m 1) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (show AEStronglyMeasurable (phase a) (gaussianReal m 1) from
      (show Continuous (phase a) by unfold phase; fun_prop).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun t => (phase_norm a t).le)

/-- The genuine characteristic function, with arbitrary centre and variance one. -/
theorem integral_phase_gaussian (a m : ℝ) :
    (∫ t, phase a t ∂gaussianReal m 1) =
      (Real.exp (-a ^ 2 / 2) : ℂ) * phase a m := by
  calc
    _ = charFun (gaussianReal m 1) a := by
      rw [charFun_apply_real]
      simp only [phase, Complex.ofReal_mul]
    _ = _ := by
      rw [charFun_gaussianReal]
      unfold phase
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      simp only [NNReal.coe_one, Complex.ofReal_one, one_mul]
      congr 1
      push_cast
      ring

/-- Exact finite marked expansion; no diagonal or equal-position terms are discarded. -/
theorem amplitude_mul_star {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u t : ℝ) :
    amplitude s γ (q + u) t * star (amplitude s γ q t) =
      ∑ i ∈ s, ∑ j ∈ s,
        (phase u (γ i) * phase q (γ i - γ j)) * phase (γ i - γ j) t := by
  simp only [amplitude, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact complete Gaussian pair matrix. -/
def matrix {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q u m : ℝ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s,
    (phase u (γ i) * phase q (γ i - γ j)) *
      ((Real.exp (-(γ i - γ j) ^ 2 / 2) : ℂ) * phase (γ i - γ j) m)

/-- The marked matrix is an actual absolutely integrable Gaussian spectral integral. -/
theorem integral_amplitude_mul_star_gaussian {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u m : ℝ) :
    (∫ t, amplitude s γ (q + u) t * star (amplitude s γ q t)
      ∂gaussianReal m 1) = matrix s γ q u m := by
  have hint (i j : ι) : Integrable
      (fun t => (phase u (γ i) * phase q (γ i - γ j)) * phase (γ i - γ j) t)
      (gaussianReal m 1) := (phase_integrable_gaussian (γ i - γ j) m).const_mul _
  simp_rw [amplitude_mul_star]
  rw [integral_finsetSum s (fun i hi => integrable_finsetSum s (fun j hj => hint i j))]
  unfold matrix
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (fun j hj => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_phase_gaussian]

/-- The natural unit cells for the variance-one characteristic kernel. -/
def squareBudget {ι : Type*} (s : Finset ι) (γ : ι → ℝ) : ℝ :=
  ∑ a ∈ s.image (fun i => Int.floor (γ i / Real.sqrt 2)),
    occupancy s (fun i => Int.floor (γ i / Real.sqrt 2)) a ^ 2

theorem squareBudget_nonneg {ι : Type*} (s : Finset ι) (γ : ι → ℝ) :
    0 ≤ squareBudget s γ := by
  unfold squareBudget
  exact Finset.sum_nonneg (fun a _ => sq_nonneg _)

private theorem scale_square (a b : ℝ) :
    (a / Real.sqrt 2 - b / Real.sqrt 2) ^ 2 = (a - b) ^ 2 / 2 := by
  rw [← sub_div, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- All centres and all independent marks obey the same deterministic cell budget. -/
theorem matrix_norm_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q u m : ℝ) :
    ‖matrix s γ q u m‖ ≤ 6 * squareBudget s γ := by
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ‖(phase u (γ i) * phase q (γ i - γ j)) *
          ((Real.exp (-(γ i - γ j) ^ 2 / 2) : ℂ) * phase (γ i - γ j) m)‖ := by
      unfold matrix
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => norm_sum_le _ _))
    _ = ∑ i ∈ s, ∑ j ∈ s, Real.exp (-(γ i - γ j) ^ 2 / 2) := by
      simp only [norm_mul, phase_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), one_mul, mul_one]
    _ = ∑ i ∈ s, ∑ j ∈ s,
        Real.exp (-(γ i / Real.sqrt 2 - γ j / Real.sqrt 2) ^ 2) := by
      simp_rw [scale_square, neg_div]
    _ ≤ _ := gaussian_pair_mass_le s (fun i => γ i / Real.sqrt 2)

/-- The Gaussian L2 mass is controlled by the same full occurrence budget. -/
theorem gaussian_energy_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q m : ℝ) :
    (∫ t, ‖amplitude s γ q t‖ ^ 2 ∂gaussianReal m 1) ≤ 6 * squareBudget s γ := by
  have heq : ((∫ t, ‖amplitude s γ q t‖ ^ 2 ∂gaussianReal m 1 : ℝ) : ℂ) =
      matrix s γ q 0 m := by
    calc
      _ = ∫ t, ((‖amplitude s γ q t‖ ^ 2 : ℝ) : ℂ) ∂gaussianReal m 1 :=
        (integral_complex_ofReal (f := fun t : ℝ => ‖amplitude s γ q t‖ ^ 2)
          (μ := gaussianReal m 1)).symm
      _ = ∫ t, amplitude s γ (q + 0) t * star (amplitude s γ q t)
          ∂gaussianReal m 1 := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [add_zero, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = _ := integral_amplitude_mul_star_gaussian s γ q 0 m
  have hnonneg : 0 ≤ ∫ t, ‖amplitude s γ q t‖ ^ 2 ∂gaussianReal m 1 :=
    integral_nonneg (fun t => sq_nonneg _)
  calc
    _ = ‖((∫ t, ‖amplitude s γ q t‖ ^ 2 ∂gaussianReal m 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖matrix s γ q 0 m‖ := congrArg norm heq
    _ ≤ _ := matrix_norm_le s γ q 0 m

/-- Positive Gaussian density floor on a unit interval about its midpoint. -/
def windowFloor : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 8 : ℝ))

theorem windowFloor_pos : 0 < windowFloor := by
  unfold windowFloor
  positivity

theorem windowFloor_le_density {b t : ℝ} (ht : t ∈ Set.Icc b (b + 1)) :
    windowFloor ≤ gaussianPDFReal (b + 1 / 2) 1 t := by
  have hleft : -(1 / 2 : ℝ) ≤ t - (b + 1 / 2) := by linarith [ht.1]
  have hright : t - (b + 1 / 2) ≤ (1 / 2 : ℝ) := by linarith [ht.2]
  have hsq : (t - (b + 1 / 2)) ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hright) (sub_nonneg.mpr hleft)]
  unfold windowFloor gaussianPDFReal
  simp only [NNReal.coe_one, mul_one]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

private theorem density_energy_integrable {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q m : ℝ) : Integrable
      (fun t => gaussianPDFReal m 1 t * ‖amplitude s γ q t‖ ^ 2) := by
  refine Integrable.mono' ((integrable_gaussianPDFReal m 1).mul_const ((s.card : ℝ) ^ 2))
    (show AEStronglyMeasurable
      (fun t => gaussianPDFReal m 1 t * ‖amplitude s γ q t‖ ^ 2) volume by
      unfold amplitude phase gaussianPDFReal; fun_prop) ?_
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (amplitude_norm_le s γ q t) 2)
      (gaussianPDFReal_nonneg _ _ _))

theorem amplitude_memLp_window {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q b : ℝ) :
    MemLp (amplitude s γ q) 2 (volume.restrict (Set.Icc b (b + 1))) := by
  apply (memLp_two_iff_integrable_sq_norm
    (show AEStronglyMeasurable (amplitude s γ q)
      (volume.restrict (Set.Icc b (b + 1))) from
      (show Continuous (amplitude s γ q) by unfold amplitude phase; fun_prop).aestronglyMeasurable)).2
  exact (show Continuous (fun t => ‖amplitude s γ q t‖ ^ 2) by
    unfold amplitude phase; fun_prop).continuousOn.integrableOn_Icc

/-- Literal Lebesgue unit-window L2 mass, uniform in the window and the phase centre. -/
theorem unit_window_energy_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q b : ℝ) :
    (∫ t in Set.Icc b (b + 1), ‖amplitude s γ q t‖ ^ 2) ≤
      (6 / windowFloor) * squareBudget s γ := by
  have hi : IntegrableOn (fun t => ‖amplitude s γ q t‖ ^ 2) (Set.Icc b (b + 1)) :=
    (show Continuous (fun t => ‖amplitude s γ q t‖ ^ 2) by
      unfold amplitude phase; fun_prop).continuousOn.integrableOn_Icc
  have hd := density_energy_integrable s γ q (b + 1 / 2)
  have hbound : windowFloor * (∫ t in Set.Icc b (b + 1), ‖amplitude s γ q t‖ ^ 2) ≤
      6 * squareBudget s γ := by
    calc
      _ = ∫ t in Set.Icc b (b + 1), windowFloor * ‖amplitude s γ q t‖ ^ 2 :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ t in Set.Icc b (b + 1),
          gaussianPDFReal (b + 1 / 2) 1 t * ‖amplitude s γ q t‖ ^ 2 := by
        apply integral_mono_ae (hi.const_mul _) hd.restrict
        exact ae_restrict_of_forall_mem measurableSet_Icc (fun t ht =>
          mul_le_mul_of_nonneg_right (windowFloor_le_density ht) (sq_nonneg _))
      _ ≤ ∫ t, gaussianPDFReal (b + 1 / 2) 1 t * ‖amplitude s γ q t‖ ^ 2 :=
        setIntegral_le_integral hd (Filter.Eventually.of_forall (fun t =>
          mul_nonneg (gaussianPDFReal_nonneg _ _ _) (sq_nonneg _)))
      _ = ∫ t, ‖amplitude s γ q t‖ ^ 2 ∂gaussianReal (b + 1 / 2) 1 := by
        rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
        simp only [smul_eq_mul]
      _ ≤ _ := gaussian_energy_le s γ q (b + 1 / 2)
  calc
    _ ≤ (6 * squareBudget s γ) / windowFloor := (le_div_iff₀ windowFloor_pos).2 (by
      simpa only [mul_comm] using hbound)
    _ = _ := by ring

/-- Actual marked Cauchy estimate in a unit spectral window, including zero-energy cases. -/
theorem unit_window_marked_norm_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q u b : ℝ) :
    ‖∫ t in Set.Icc b (b + 1),
      amplitude s γ (q + u) t * star (amplitude s γ q t)‖ ≤
        (6 / windowFloor) * squareBudget s γ := by
  have hcs := MarkedIntegralCauchy.integral_mul_star_norm_sq_le
    (amplitude_memLp_window s γ (q + u) b) (amplitude_memLp_window s γ q b)
  have hleft := unit_window_energy_le s γ (q + u) b
  have hright := unit_window_energy_le s γ q b
  have hnleft : 0 ≤ ∫ t in Set.Icc b (b + 1), ‖amplitude s γ (q + u) t‖ ^ 2 :=
    integral_nonneg (fun t => sq_nonneg _)
  have hnright : 0 ≤ ∫ t in Set.Icc b (b + 1), ‖amplitude s γ q t‖ ^ 2 :=
    integral_nonneg (fun t => sq_nonneg _)
  have hb : 0 ≤ (6 / windowFloor) * squareBudget s γ :=
    mul_nonneg (div_nonneg (by norm_num) windowFloor_pos.le) (squareBudget_nonneg s γ)
  have hproduct := mul_le_mul hleft hright hnright hb
  nlinarith [norm_nonneg (∫ t in Set.Icc b (b + 1),
    amplitude s γ (q + u) t * star (amplitude s γ q t))]

/-- Uniform normalized mass consumer, with the arithmetic cluster-square input visible. -/
theorem normalized_unit_window_energy_le_of_squareBudget {ι : Type*}
    (s : Finset ι) (γ : ι → ℝ) (q b C : ℝ)
    (hM : 0 < s.card) (hbudget : squareBudget s γ ≤ C * (s.card : ℝ)) :
    (∫ t in Set.Icc b (b + 1), ‖amplitude s γ q t‖ ^ 2) / (s.card : ℝ) ≤
      (6 / windowFloor) * C := by
  have hMR : 0 < (s.card : ℝ) := by exact_mod_cast hM
  calc
    _ ≤ ((6 / windowFloor) * squareBudget s γ) / (s.card : ℝ) :=
      div_le_div_of_nonneg_right (unit_window_energy_le s γ q b) hMR.le
    _ ≤ ((6 / windowFloor) * (C * (s.card : ℝ))) / (s.card : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbudget (div_nonneg (by norm_num) windowFloor_pos.le)) hMR.le
    _ = _ := by field_simp

end RiemannResearch.Analysis.GaussianSpectralWindows
