import RiemannResearch.Analysis.SampledGaugeCompleteness
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Zero-ordinate equidistribution: Fourier-to-Haar bridge

The unconditional analytic estimates for the actual Riemann-zeta zeros are
NOT asserted in this file. Every analytic input is an explicit hypothesis.
No new axioms are declared. Averages use the first n+1 samples, so their
normalizing denominator is always nonzero.

The analytic motivation is Ford--Zaharescu, arXiv:math/0405459.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ZeroOrdinate

/-- The probability average over samples 0,...,n. -/
def mean (n : ℕ) (f : ℕ → ℂ) : ℂ :=
  ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ j ∈ Finset.range (n + 1), f j

@[simp] theorem mean_zero (n : ℕ) : mean n (fun _ => 0) = 0 := by
  simp [mean]

@[simp] theorem mean_const (n : ℕ) (c : ℂ) : mean n (fun _ => c) = c := by
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [mean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hn c

@[simp] theorem mean_add (n : ℕ) (f g : ℕ → ℂ) :
    mean n (fun j => f j + g j) = mean n f + mean n g := by
  simp [mean, Finset.sum_add_distrib, mul_add]

@[simp] theorem mean_sub (n : ℕ) (f g : ℕ → ℂ) :
    mean n (fun j => f j - g j) = mean n f - mean n g := by
  simp [mean, Finset.sum_sub_distrib, mul_sub]

@[simp] theorem mean_mul_left (n : ℕ) (c : ℂ) (f : ℕ → ℂ) :
    mean n (fun j => c * f j) = c * mean n f := by
  simp only [mean, ← Finset.mul_sum]
  ring

@[simp] theorem mean_mul_right (n : ℕ) (f : ℕ → ℂ) (c : ℂ) :
    mean n (fun j => f j * c) = mean n f * c := by
  simp only [mean, ← Finset.sum_mul]
  ring

@[simp] theorem mean_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℂ) (n : ℕ) :
    mean n (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, mean n (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

/-- Probability averaging is contractive for the supremum norm. -/
theorem norm_mean_le (n : ℕ) (f : ℕ → ℂ) (B : ℝ)
    (hB : ∀ j, ‖f j‖ ≤ B) : ‖mean n f‖ ≤ B := by
  have hsum : ‖∑ j ∈ Finset.range (n+1), f j‖ ≤ ((n+1 : ℕ) : ℝ) * B := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), ‖f j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n+1), B := Finset.sum_le_sum (fun j _ => hB j)
      _ = _ := by simp
  rw [mean, norm_mul]
  calc
    _ ≤ ‖((n+1 : ℕ) : ℂ)⁻¹‖ * (((n+1 : ℕ) : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = B := by
      rw [norm_inv, Complex.norm_natCast]
      exact inv_mul_cancel_left₀ (by positivity : ((n+1 : ℕ) : ℝ) ≠ 0) B

/-- The oscillatory phase, with angular frequency in radians. -/
def phase (u t : ℝ) : ℂ := Complex.exp ((u * t : ℝ) * Complex.I)

@[simp] theorem phase_zero (t : ℝ) : phase 0 t = 1 := by simp [phase]
@[simp] theorem phase_norm (u t : ℝ) : ‖phase u t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phase_add (u v t : ℝ) : phase (u+v) t = phase u t * phase v t := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_neg (u t : ℝ) : phase (-u) t = star (phase u t) := by
  simp [phase, ← Complex.exp_conj]

/-- The fixed-frequency input. This definition is NOT an assertion that the
actual zeta-zero ordinates satisfy it. -/
def FourierCancellation (times : ℕ → ℝ) : Prop :=
  ∀ u : ℝ, u ≠ 0 → Tendsto (fun n => mean n (fun j => phase u (times j)))
    atTop (𝓝 0)

section DenseTests
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Dense test families suffice for weak convergence of probability averages.
The limiting functional is an explicit contractive linear map. -/
theorem converge_of_dense_tests {ι : Type*} (test : ι → C(X, ℂ))
    (hdense : (Submodule.span ℂ (Set.range test)).topologicalClosure = ⊤)
    (samples : ℕ → X) (L : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ f, ‖L f‖ ≤ ‖f‖)
    (htest : ∀ i, Tendsto (fun n => mean n (fun j => test i (samples j)))
      atTop (𝓝 (L (test i))))
    (f : C(X, ℂ)) :
    Tendsto (fun n => mean n (fun j => f (samples j))) atTop (𝓝 (L f)) := by
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range test),
      Tendsto (fun n => mean n (fun j => g (samples j))) atTop (𝓝 (L g)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨i, rfl⟩ := hg
        exact htest i
    | zero => simp
    | add g h hg hh ihg ihh =>
        simpa only [ContinuousMap.add_apply, mean_add, map_add] using ihg.add ihh
    | smul c g hg ih =>
        simpa only [ContinuousMap.smul_apply, smul_eq_mul, mean_mul_left, map_smul,
          smul_eq_mul] using ih.const_mul c
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hf : f ∈ (Submodule.span ℂ (Set.range test)).topologicalClosure := by
    rw [hdense]
    trivial
  change f ∈ closure (Submodule.span ℂ (Set.range test) : Set C(X, ℂ)) at hf
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε/4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hspan g hg) (ε/2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have havg : ‖mean n (fun j => f (samples j)) - mean n (fun j => g (samples j))‖
      ≤ ‖f-g‖ := by
    rw [← mean_sub]
    exact norm_mean_le n _ _ (fun j => (f-g).norm_coe_le_norm (samples j))
  have hint : ‖L g - L f‖ ≤ ‖f-g‖ := by
    rw [← map_sub]
    calc
      _ ≤ ‖g-f‖ := hL (g-f)
      _ = _ := norm_sub_rev _ _
  have htri := norm_add_le
    (mean n (fun j => f (samples j)) - L g) (L g - L f)
  have htri2 := norm_add_le
    (mean n (fun j => f (samples j)) - mean n (fun j => g (samples j)))
    (mean n (fun j => g (samples j)) - L g)
  simp only [sub_add_sub_cancel] at htri htri2
  rw [dist_eq_norm] at hfg ⊢
  have hgn := hN n hn
  rw [dist_eq_norm] at hgn
  linarith

end DenseTests


section ProbabilityIntegral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

private theorem continuousMap_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℂ)) : Integrable f μ :=
  (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))

/-- Integration of continuous functions against a probability measure. -/
def probabilityIntegral (μ : Measure X) [IsProbabilityMeasure μ] : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (continuousMap_integrable μ f) (continuousMap_integrable μ g)
  map_smul' c f := by
    simpa only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul] using
      integral_const_mul c (fun x => f x)

theorem probabilityIntegral_bound (μ : Measure X) [IsProbabilityMeasure μ] (f : C(X, ℂ)) :
    ‖probabilityIntegral μ f‖ ≤ ‖f‖ := by
  simpa [probabilityIntegral] using
    (norm_integral_le_of_norm_le_const
      (μ := μ) (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x)))

end ProbabilityIntegral

section Circle
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem haarIntegral_fourier (k : ℤ) :
    probabilityIntegral (AddCircle.haarAddCircle (T := 1)) (fourier k) =
      if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) k) 0
  simpa [probabilityIntegral, fourierCoeff, Pi.single_apply, eq_comm] using h

theorem fourier_sample (k : ℤ) (α t : ℝ) :
    fourier k ((α*t : ℝ) : AddCircle (1 : ℝ)) = phase (2*Real.pi*(k:ℝ)*α) t := by
  rw [fourier_coe_apply]
  unfold phase
  congr 1
  push_cast
  ring

/-- Weyl's criterion specialized to real samples modulo one. The only
remaining sampling assumption is fixed-frequency cancellation. -/
theorem circle_equidistributed_of_fourier (times : ℕ → ℝ)
    (hcancel : FourierCancellation times) (α : ℝ) (hα : α ≠ 0)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun n => mean n (fun j => f ((α * times j : ℝ) : AddCircle (1 : ℝ))))
      atTop (𝓝 (∫ x, f x ∂(AddCircle.haarAddCircle (T := 1)))) := by
  apply converge_of_dense_tests (fourier (T := 1)) span_fourier_closure_eq_top
    (fun j => ((α * times j : ℝ) : AddCircle (1 : ℝ)))
    (probabilityIntegral AddCircle.haarAddCircle) (probabilityIntegral_bound _) _ f
  intro k
  rw [haarIntegral_fourier]
  by_cases hk : k = 0
  · subst k
    simp only [fourier_zero, mean_const]
    exact tendsto_const_nhds
  · have hu : 2 * Real.pi * (k : ℝ) * α ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (by exact_mod_cast hk)) hα
    simpa only [if_neg hk, fourier_sample] using hcancel _ hu

end Circle

/-- A covariance is precisely the Fourier mode at the difference frequency. -/
theorem phase_sub (u v t : ℝ) : phase (u-v) t = phase u t * star (phase v t) := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

theorem phase_average_limit (times : ℕ → ℝ) (hcancel : FourierCancellation times) (u : ℝ) :
    Tendsto (fun n => mean n (fun j => phase u (times j)))
      atTop (𝓝 (if u = 0 then 1 else 0)) := by
  by_cases hu : u = 0
  · subst u
    simp only [phase_zero, mean_const]
    exact tendsto_const_nhds
  · simpa only [if_neg hu] using hcancel u hu

theorem phase_covariance_limit (times : ℕ → ℝ) (hcancel : FourierCancellation times)
    (u v : ℝ) :
    Tendsto (fun n => mean n (fun j => phase u (times j) * star (phase v (times j))))
      atTop (𝓝 (if u = v then 1 else 0)) := by
  simpa only [phase_sub, sub_eq_zero] using phase_average_limit times hcancel (u-v)


/-- The corresponding real probability average. -/
def realMean (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((n+1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (n+1), f j

theorem realMean_nonneg (n : ℕ) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    0 ≤ realMean n f := by
  unfold realMean
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hf j))

theorem realMean_mono (n : ℕ) (f g : ℕ → ℝ) (h : ∀ j, f j ≤ g j) :
    realMean n f ≤ realMean n g := by
  unfold realMean
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => h j)) (by positivity)

theorem realMean_mul_left (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    realMean n (fun j => c*f j) = c*realMean n f := by
  simp only [realMean, ← Finset.mul_sum]
  ring

theorem norm_mean_le_realMean (n : ℕ) (f : ℕ → ℂ) :
    ‖mean n f‖ ≤ realMean n (fun j => ‖f j‖) := by
  rw [mean, norm_mul, norm_inv, Complex.norm_natCast, realMean]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

/-- Normalized finite Cauchy--Schwarz. -/
theorem realMean_abs_sq_le (n : ℕ) (d : ℕ → ℝ) :
    (realMean n (fun j => |d j|))^2 ≤ realMean n (fun j => (d j)^2) := by
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n+1))
    (fun _ => (1 : ℝ)) (fun j => |d j|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, sq_abs] at h
  unfold realMean
  rw [mul_pow]
  calc
    _ ≤ (((n+1 : ℕ) : ℝ)⁻¹)^2 *
        (((n+1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (n+1), (d j)^2) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by field_simp

/-- Mean-square horizontal concentration implies mean absolute concentration. -/
theorem mean_abs_tendsto_zero_of_mean_sq (d : ℕ → ℝ)
    (h : Tendsto (fun n => realMean n (fun j => (d j)^2)) atTop (𝓝 0)) :
    Tendsto (fun n => realMean n (fun j => |d j|)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => (realMean n (fun j => |d j|))^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun n => realMean_abs_sq_le n d) h
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (realMean_nonneg _ _ (fun j => abs_nonneg (d j))), Real.sqrt_zero] using ht

/-- Removing the horizontal exponential weight costs at most a constant times
absolute horizontal displacement. No hypothesis on zeta is used here. -/
theorem exponential_weight_bound (u d : ℝ) (hd : |d| ≤ 1/2) :
    ‖(Real.exp (u*d) : ℂ)-1‖ ≤ (|u| * Real.exp (|u| /2))* |d| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((u*d : ℝ) : ℂ) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_exp,
    abs_mul] at h
  have hu : |u| * |d| ≤ |u| /2 := by nlinarith [abs_nonneg u]
  calc
    _ ≤ (|u| * |d|) * Real.exp (|u| * |d|) := h
    _ ≤ (|u| * |d|) * Real.exp (|u| /2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) (by positivity)
    _ = _ := by ring

/-- Centered version of the exponential appearing in Landau's formula. -/
def tiltedPhase (u d t : ℝ) : ℂ := phase u t * (Real.exp (u*d) : ℂ)

theorem phase_tilted_difference_bound (u d t : ℝ) (hd : |d| ≤ 1/2) :
    ‖phase u t - tiltedPhase u d t‖ ≤ (|u| *Real.exp (|u| /2))* |d| := by
  have heq : phase u t - tiltedPhase u d t = phase u t * (1-(Real.exp (u*d) : ℂ)) := by
    unfold tiltedPhase
    ring
  rw [heq, norm_mul, phase_norm, one_mul, norm_sub_rev]
  exact exponential_weight_bound u d hd

theorem mean_phase_tilted_difference_bound (times d : ℕ → ℝ) (u : ℝ)
    (hd : ∀ j, |d j| ≤ 1/2) (n : ℕ) :
    ‖mean n (fun j => phase u (times j)) -
        mean n (fun j => tiltedPhase u (d j) (times j))‖ ≤
      (|u| *Real.exp (|u| /2))*realMean n (fun j => |d j|) := by
  rw [← mean_sub]
  calc
    _ ≤ realMean n (fun j => ‖phase u (times j) - tiltedPhase u (d j) (times j)‖) :=
      norm_mean_le_realMean _ _
    _ ≤ realMean n (fun j => (|u| *Real.exp (|u| /2))* |d j|) :=
      realMean_mono _ _ _ (fun j => phase_tilted_difference_bound _ _ _ (hd j))
    _ = _ := realMean_mul_left _ _ _

/-- An O(height) exponential-sum estimate is o(sample count) whenever
height/sample-count tends to zero. -/
theorem mean_tendsto_zero_of_sum_bound (f : ℕ → ℂ) (height : ℕ → ℝ) (C : ℝ)
    (hcount : Tendsto (fun n => height n / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0))
    (hbound : ∀ n, ‖∑ j ∈ Finset.range (n+1), f j‖ ≤ C*height n) :
    Tendsto (fun n => mean n f) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr; simp only [sub_zero]
  have ht : Tendsto (fun n => C*(height n / ((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using hcount.const_mul C
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  rw [mean, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹*(C*height n) :=
      mul_le_mul_of_nonneg_left (hbound n) (by positivity)
    _ = _ := by ring

/-- Analytic reduction. For actual zeta zeros, `d j = beta_j - 1/2`.
The two unproved zeta-specific inputs are explicitly visible: horizontal
mean-square concentration, and the centered Landau sum bound with zero counting.
Neither Fourier cancellation nor equidistribution is assumed. -/
theorem fourierCancellation_of_analytic_inputs (times d height : ℕ → ℝ)
    (hstrip : ∀ j, |d j| ≤ 1/2)
    (hdensity : Tendsto (fun n => realMean n (fun j => (d j)^2)) atTop (𝓝 0))
    (hcount : Tendsto (fun n => height n / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0))
    (hlandau : ∀ u : ℝ, u ≠ 0 → ∃ C : ℝ, ∀ n,
      ‖∑ j ∈ Finset.range (n+1), tiltedPhase u (d j) (times j)‖ ≤ C*height n) :
    FourierCancellation times := by
  intro u hu
  obtain ⟨C, hC⟩ := hlandau u hu
  have htilt := mean_tendsto_zero_of_sum_bound
    (fun j => tiltedPhase u (d j) (times j)) height C hcount hC
  have habs := mean_abs_tendsto_zero_of_mean_sq d hdensity
  have hmajor : Tendsto (fun n => (|u| *Real.exp (|u| /2))*realMean n (fun j => |d j|))
      atTop (𝓝 0) := by simpa using habs.const_mul (|u| *Real.exp (|u| /2))
  have hdiff : Tendsto (fun n => mean n (fun j => phase u (times j)) -
      mean n (fun j => tiltedPhase u (d j) (times j))) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr; simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => mean_phase_tilted_difference_bound times d u hstrip n) hmajor
  simpa only [sub_add_cancel, zero_add] using hdiff.add htilt

section AnalyticCircle
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- End-to-end conditional analytic-to-Haar theorem, with no equidistribution
hypothesis hidden in the statement. -/
theorem circle_equidistributed_of_analytic_inputs (times d height : ℕ → ℝ)
    (hstrip : ∀ j, |d j| ≤ 1/2)
    (hdensity : Tendsto (fun n => realMean n (fun j => (d j)^2)) atTop (𝓝 0))
    (hcount : Tendsto (fun n => height n / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0))
    (hlandau : ∀ u : ℝ, u ≠ 0 → ∃ C : ℝ, ∀ n,
      ‖∑ j ∈ Finset.range (n+1), tiltedPhase u (d j) (times j)‖ ≤ C*height n)
    (α : ℝ) (hα : α ≠ 0) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun n => mean n (fun j => f ((α*times j : ℝ) : AddCircle (1 : ℝ))))
      atTop (𝓝 (∫ x, f x ∂(AddCircle.haarAddCircle (T := 1)))) :=
  circle_equidistributed_of_fourier times
    (fourierCancellation_of_analytic_inputs times d height hstrip hdensity hcount hlandau) α hα f

end AnalyticCircle


/-- Exact finite signed covariance expansion. Cross terms are retained,
not replaced by their absolute values. -/
theorem finite_signed_covariance {ι : Type*} (s : Finset ι)
    (frequency : ι → ℝ) (a b : ι → ℂ) (times : ℕ → ℝ) (n : ℕ) :
    mean n (fun j => (∑ i ∈ s, a i * phase (frequency i) (times j)) *
      star (∑ k ∈ s, b k * phase (frequency k) (times j))) =
    ∑ i ∈ s, ∑ k ∈ s, (a i * star (b k)) *
      mean n (fun j => phase (frequency i-frequency k) (times j)) := by
  have hexpand (j : ℕ) :
      (∑ i ∈ s, a i * phase (frequency i) (times j)) *
        star (∑ k ∈ s, b k * phase (frequency k) (times j)) =
      ∑ i ∈ s, ∑ k ∈ s, (a i * star (b k)) *
        phase (frequency i-frequency k) (times j) := by
    simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, phase_sub]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hexpand, mean_sum, mean_mul_left]

/-- The limiting sesquilinear Parseval identity for fixed finite support. -/
theorem finite_covariance_limit {ι : Type*} (s : Finset ι)
    (frequency : ι → ℝ) (hfrequency : Function.Injective frequency)
    (a b : ι → ℂ) (times : ℕ → ℝ) (hcancel : FourierCancellation times) :
    Tendsto (fun n => mean n (fun j =>
      (∑ i ∈ s, a i * phase (frequency i) (times j)) *
        star (∑ k ∈ s, b k * phase (frequency k) (times j))))
      atTop (𝓝 (∑ i ∈ s, a i * star (b i))) := by
  classical
  simp_rw [finite_signed_covariance]
  have ht := tendsto_finsetSum s (fun i hi =>
    tendsto_finsetSum s (fun k hk =>
      (phase_average_limit times hcancel (frequency i-frequency k)).const_mul (a i * star (b k))))
  simpa [sub_eq_zero, hfrequency.eq_iff, mul_ite] using ht

/-- Matching equal coefficient vectors gives the quadratic Parseval identity. -/
theorem finite_parseval {ι : Type*} (s : Finset ι)
    (frequency : ι → ℝ) (hfrequency : Function.Injective frequency)
    (a : ι → ℂ) (times : ℕ → ℝ) (hcancel : FourierCancellation times) :
    Tendsto (fun n => mean n (fun j =>
      (∑ i ∈ s, a i * phase (frequency i) (times j)) *
        star (∑ i ∈ s, a i * phase (frequency i) (times j))))
      atTop (𝓝 (∑ i ∈ s, a i * star (a i))) :=
  finite_covariance_limit s frequency hfrequency a a times hcancel

/-- Converts scalar Fourier cancellation into the phase-covariance provider
required by the existing sampled-gauge completeness theorem. -/
theorem gaugeOrbit_dense_of_fourierCancellation {ι : Type*} [DecidableEq ι]
    (h : SampledGauge.Space ι) (frequency : ι → ℝ)
    (hfrequency : Function.Injective frequency) (times : ℕ → ℝ)
    (hsupport : ∀ i, h i ≠ 0) (hcancel : FourierCancellation times) :
    (Submodule.span ℂ (Set.range (SampledGauge.gaugeOrbit h frequency times))).topologicalClosure = ⊤ := by
  apply SampledGauge.gaugeOrbit_dense_of_phase_limits h frequency times hsupport
  intro q i
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have hker : ∀ n, SampledGauge.sampleKernel (SampledGauge.gaugePhase frequency times) q i (n+1) =
      mean n (fun j => phase (frequency i) (times j) * star (phase (frequency q) (times j))) := by
    intro n
    unfold SampledGauge.sampleKernel SampledGauge.gaugePhase mean phase
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm (times j) (frequency q), mul_comm (times j) (frequency i)]
    ring
  simp_rw [hker]
  simpa only [hfrequency.eq_iff] using
    phase_covariance_limit times hcancel (frequency i) (frequency q)

/-- Connects the explicit analytic inputs all the way to the existing l2
orbit-completeness theorem. Actual zeta estimates remain hypotheses. -/
theorem gaugeOrbit_dense_of_analytic_inputs {ι : Type*} [DecidableEq ι]
    (h : SampledGauge.Space ι) (frequency : ι → ℝ)
    (hfrequency : Function.Injective frequency) (hsupport : ∀ i, h i ≠ 0)
    (times d height : ℕ → ℝ)
    (hstrip : ∀ j, |d j| ≤ 1/2)
    (hdensity : Tendsto (fun n => realMean n (fun j => (d j)^2)) atTop (𝓝 0))
    (hcount : Tendsto (fun n => height n / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0))
    (hlandau : ∀ u : ℝ, u ≠ 0 → ∃ C : ℝ, ∀ n,
      ‖∑ j ∈ Finset.range (n+1), tiltedPhase u (d j) (times j)‖ ≤ C*height n) :
    (Submodule.span ℂ (Set.range (SampledGauge.gaugeOrbit h frequency times))).topologicalClosure = ⊤ :=
  gaugeOrbit_dense_of_fourierCancellation h frequency hfrequency times hsupport
    (fourierCancellation_of_analytic_inputs times d height hstrip hdensity hcount hlandau)

end RiemannResearch.Analysis.ZeroOrdinate
