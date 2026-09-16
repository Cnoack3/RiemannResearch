import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Signed quadratic forms, uniform sampling errors, and optimized residuals

The finite algebra and optimization statements in this file are unconditional.
A quantitative entrywise sampling estimate is a visible hypothesis when used;
no Landau or Selberg estimate is postulated as an axiom.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ZeroSamplingQuadratic

variable {ι : Type*}

/-- The full complex quadratic expression, retaining every cross term. -/
def form (s : Finset ι) (G : ι → ι → ℂ) (a : ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * G i j

/-- Haar coefficient energy on a finite character family. -/
def coefficientEnergy (s : Finset ι) (a : ι → ℂ) : ℝ :=
  ∑ i ∈ s, ‖a i‖ ^ 2

theorem coefficientEnergy_nonneg (s : Finset ι) (a : ι → ℂ) :
    0 ≤ coefficientEnergy s a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

@[simp] theorem form_sub (s : Finset ι) (G H : ι → ι → ℂ) (a : ι → ℂ) :
    form s (fun i j => G i j - H i j) a = form s G a - form s H a := by
  simp only [form, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem form_add (s : Finset ι) (G H : ι → ι → ℂ) (a : ι → ℂ) :
    form s (fun i j => G i j + H i j) a = form s G a + form s H a := by
  simp only [form, mul_add, Finset.sum_add_distrib]

@[simp] theorem form_mul (s : Finset ι) (c : ℂ) (G : ι → ι → ℂ) (a : ι → ℂ) :
    form s (fun i j => c * G i j) a = c * form s G a := by
  simp only [form, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[simp] theorem form_identity [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) :
    form s (fun i j => if i = j then 1 else 0) a = (coefficientEnergy s a : ℂ) := by
  classical
  simp [form, coefficientEnergy, mul_ite, Complex.mul_conj, Complex.sq_norm]

/-- Exact I - lambda B + R expansion; signed B is not absorbed in an error. -/
theorem form_signed_expansion [DecidableEq ι] (s : Finset ι) (B R : ι → ι → ℂ) (a : ι → ℂ) (t : ℝ) :
    form s (fun i j => (if i = j then 1 else 0) - (t : ℂ) * B i j + R i j) a =
      (coefficientEnergy s a : ℂ) - (t : ℂ) * form s B a + form s R a := by
  classical
  rw [form_add, form_sub, form_identity, form_mul]

/-- Entrywise error implies a coefficient-uniform quadratic estimate. -/
theorem form_bound (s : Finset ι) (R : ι → ι → ℂ) (a : ι → ℂ)
    (e : ℝ) (he : 0 ≤ e) (hR : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ ≤ e) :
    ‖form s R a‖ ≤ (s.card : ℝ) * e * coefficientEnergy s a := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    ‖form s R a‖ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * e := by
      unfold form
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro i hi
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hR i hi j hj) (by positivity)
    _ = e * (∑ i ∈ s, ‖a i‖) ^ 2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ e * ((s.card : ℝ) * coefficientEnergy s a) :=
      mul_le_mul_of_nonneg_left hcs he
    _ = _ := by ring

/-- Uniform form comparison, applicable to data-dependent coefficients. -/
theorem form_comparison (s : Finset ι) (G H : ι → ι → ℂ) (a : ι → ℂ)
    (e : ℝ) (he : 0 ≤ e)
    (hGH : ∀ i ∈ s, ∀ j ∈ s, ‖G i j - H i j‖ ≤ e) :
    ‖form s G a - form s H a‖ ≤ (s.card : ℝ) * e * coefficientEnergy s a := by
  rw [← form_sub]
  exact form_bound s _ a e he hGH

/-- The exact sampling Gram of an arbitrary finite weighted sample family. -/
def samplingGram {κ : Type*} (samples : Finset κ) (weight : κ → ℝ)
    (phase : κ → ι → ℂ) (i j : ι) : ℂ :=
  ∑ k ∈ samples, (weight k : ℂ) * phase k i * star (phase k j)

/-- No cancellation, independence, or zeta hypotheses are used in this identity. -/
theorem form_samplingGram {κ : Type*} (s : Finset ι) (samples : Finset κ)
    (weight : κ → ℝ) (phase : κ → ι → ℂ) (a : ι → ℂ) :
    form s (samplingGram samples weight phase) a =
      ∑ k ∈ samples, (weight k : ℂ) *
        ((∑ i ∈ s, a i * phase k i) * star (∑ i ∈ s, a i * phase k i)) := by
  classical
  simp only [form, samplingGram, Finset.mul_sum, star_sum, star_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := s) (t := samples)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A near-Haar bound remains valid after minimizing over an arbitrary nonempty
family. Both minima are infima, so existence of minimizers is not assumed. -/
theorem optimized_energy_comparison {A : Type*} [Nonempty A]
    (P Q : A → ℝ) (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a)
    (e : ℝ) (he : 0 ≤ e) (he1 : e < 1)
    (hlo : ∀ a, (1 - e) * P a ≤ Q a)
    (hhi : ∀ a, Q a ≤ (1 + e) * P a) :
    (1 - e) * (⨅ a, P a) ≤ (⨅ a, Q a) ∧
      (⨅ a, Q a) ≤ (1 + e) * (⨅ a, P a) := by
  have hbP : BddBelow (Set.range P) := ⟨0, by rintro _ ⟨a, rfl⟩; exact hP a⟩
  have hbQ : BddBelow (Set.range Q) := ⟨0, by rintro _ ⟨a, rfl⟩; exact hQ a⟩
  constructor
  · apply le_ciInf
    intro a
    exact (mul_le_mul_of_nonneg_left (ciInf_le hbP a) (by linarith)).trans (hlo a)
  · have hpos : 0 < 1 + e := by linarith
    have hdiv : (⨅ a, Q a) / (1 + e) ≤ (⨅ a, P a) := by
      apply le_ciInf
      intro a
      apply (div_le_iff₀ hpos).mpr
      simpa only [mul_comm] using (ciInf_le hbQ a).trans (hhi a)
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp hdiv

/-- Complex polarization for one edge, used to preserve signed graph energy. -/
theorem edge_identity (z w : ℂ) :
    2 * (z * star w).re = ‖z‖ ^ 2 + ‖w‖ ^ 2 - ‖z - w‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Exact signed divisibility-graph identity, valid for arbitrary complex
vertex amplitudes and arbitrary real edge coefficients. -/
theorem graph_energy_identity {E : Type*} (edges : Finset E)
    (left right : E → ι) (weight : E → ℝ) (b : ι → ℂ) :
    ∑ e ∈ edges, weight e * (2 * (b (left e) * star (b (right e))).re) =
      (∑ e ∈ edges, weight e * (‖b (left e)‖ ^ 2 + ‖b (right e)‖ ^ 2)) -
      ∑ e ∈ edges, weight e * ‖b (left e) - b (right e)‖ ^ 2 := by
  simp_rw [edge_identity, mul_sub, Finset.sum_sub_distrib]

theorem graph_energy_nonneg {E : Type*} (edges : Finset E)
    (left right : E → ι) (weight : E → ℝ) (b : ι → ℂ)
    (hw : ∀ e ∈ edges, 0 ≤ weight e) :
    0 ≤ ∑ e ∈ edges, weight e * ‖b (left e) - b (right e)‖ ^ 2 :=
  Finset.sum_nonneg (fun e he => mul_nonneg (hw e he) (sq_nonneg _))

/-- The diagonal-minus-graph decomposition yields an upper bound without
replacing the signed cross terms individually by absolute values. -/
theorem graph_signed_upper_bound {E : Type*} (edges : Finset E)
    (left right : E → ι) (weight : E → ℝ) (b : ι → ℂ)
    (hw : ∀ e ∈ edges, 0 ≤ weight e) :
    (∑ e ∈ edges, weight e * (2 * (b (left e) * star (b (right e))).re)) ≤
      ∑ e ∈ edges, weight e * (‖b (left e)‖ ^ 2 + ‖b (right e)‖ ^ 2) := by
  rw [graph_energy_identity]
  exact sub_le_self _ (graph_energy_nonneg edges left right weight b hw)

/-- The positive graph term has the claimed blind direction. -/
theorem graph_energy_constant_zero {E : Type*} (edges : Finset E)
    (left right : E → ι) (weight : E → ℝ) (c : ℂ) :
    (∑ e ∈ edges, weight e *
      ‖(fun _ : ι => c) (left e) - (fun _ : ι => c) (right e)‖ ^ 2) = 0 := by
  simp

/-- The real quadratic sampling error, uniform over every coefficient vector. -/
theorem real_form_error [DecidableEq ι] (S : Finset ι) (G : ι → ι → ℂ)
    (a : ι → ℂ) (e : ℝ) (he : 0 ≤ e)
    (hG : ∀ i ∈ S, ∀ j ∈ S, ‖G i j - (if i = j then 1 else 0)‖ ≤ e) :
    |(form S G a).re - coefficientEnergy S a| ≤
      (S.card : ℝ) * e * coefficientEnergy S a := by
  have h := form_comparison S G (fun i j => if i = j then 1 else 0) a e he hG
  rw [form_identity] at h
  simpa only [Complex.sub_re, Complex.ofReal_re] using
    (Complex.abs_re_le_norm (form S G a - (coefficientEnergy S a : ℂ))).trans h

/-- Two-sided near-Haar energy control, with the support cardinality explicit. -/
theorem near_identity_bounds [DecidableEq ι] (S : Finset ι) (G : ι → ι → ℂ)
    (a : ι → ℂ) (e : ℝ) (he : 0 ≤ e)
    (hG : ∀ i ∈ S, ∀ j ∈ S, ‖G i j - (if i = j then 1 else 0)‖ ≤ e) :
    (1 - (S.card : ℝ) * e) * coefficientEnergy S a ≤ (form S G a).re ∧
      (form S G a).re ≤ (1 + (S.card : ℝ) * e) * coefficientEnergy S a := by
  have h := abs_le.mp (real_form_error S G a e he hG)
  constructor <;> nlinarith [h.1, h.2]

/-- Relative error on each nonzero finite coefficient vector. -/
theorem relative_form_error [DecidableEq ι] (S : Finset ι) (G : ι → ι → ℂ)
    (a : ι → ℂ) (ha : 0 < coefficientEnergy S a) (e : ℝ) (he : 0 ≤ e)
    (hG : ∀ i ∈ S, ∀ j ∈ S, ‖G i j - (if i = j then 1 else 0)‖ ≤ e) :
    |(form S G a).re / coefficientEnergy S a - 1| ≤ (S.card : ℝ) * e := by
  have h := real_form_error S G a e he hG
  have heq : (form S G a).re / coefficientEnergy S a - 1 =
      ((form S G a).re - coefficientEnergy S a) / coefficientEnergy S a := by
    field_simp [ha.ne']
  rw [heq, abs_div, abs_of_pos ha]
  exact (div_le_iff₀ ha).mpr h

/-- Growing supports and coefficients may depend arbitrarily on the sample.
The only quantitative sampling input is the displayed entrywise error rate. -/
theorem data_dependent_energy_limit [DecidableEq ι]
    (S : ℕ → Finset ι) (G : ℕ → ι → ι → ℂ) (a : ℕ → ι → ℂ)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (ha : ∀ n, 0 < coefficientEnergy (S n) (a n))
    (hG : ∀ n, ∀ i ∈ S n, ∀ j ∈ S n,
      ‖G n i j - (if i = j then 1 else 0)‖ ≤ e n)
    (hsmall : Tendsto (fun n => ((S n).card : ℝ) * e n) atTop (𝓝 0)) :
    Tendsto (fun n => (form (S n) (G n) (a n)).re / coefficientEnergy (S n) (a n))
      atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using
      relative_form_error (S n) (G n) (a n) (ha n) (e n) (he n) (hG n)) hsmall

end RiemannResearch.Analysis.ZeroSamplingQuadratic
