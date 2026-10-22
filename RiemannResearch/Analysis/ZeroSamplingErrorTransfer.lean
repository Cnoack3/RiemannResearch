import RiemannResearch.Analysis.ZeroSamplingQuadratic

/-!
# Structured finite sampling error transfer

Source: user-provided zero-ordinate harmonic analysis note (2026-10-11).
The elementary finite-norm identities and Schur row-budget bounds below are
unconditional. An actual zeta-zero application must supply its displayed
entrywise analytic estimate; no Landau estimate, RH, or open provider is an axiom.

The pair transfer retains the linear arithmetic term and the quadratic error
remainder separately. Its row budget is `2 * e * K + card * e^2`, improving on
the dense bound when the arithmetic kernel has a small absolute row sum.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ZeroSamplingQuadratic

variable {ι : Type*}

/-- Preserve every coefficient weight before taking a uniform estimate. -/
theorem form_comparison_weighted (s : Finset ι) (S B : ι → ι → ℂ)
    (a : ι → ℂ) :
    ‖form s S a - form s B a‖ ≤
      ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * ‖S i j - B i j‖ := by
  rw [← form_sub]
  unfold form
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro i hi
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul, norm_star]
  exact le_rfl

/-- A symmetric nonnegative row envelope gives a Schur bound with no dense
support-cardinality loss. The conclusion is uniform in all coefficients. -/
theorem form_comparison_symmetric_row_bound (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (E : ι → ι → ℝ) (K : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (hentry : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ E i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, E i j = E j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, E i j ≤ K) :
    ‖form s S a - form s B a‖ ≤ K * coefficientEnergy s a := by
  let L : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ ^ 2 * E i j
  let M : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a j‖ ^ 2 * E i j
  have hLM : M = L := by
    dsimp [L, M]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have hL : L ≤ K * coefficientEnergy s a := by
    calc
      L = ∑ i ∈ s, ‖a i‖ ^ 2 * (∑ j ∈ s, E i j) := by
        simp only [L, Finset.mul_sum]
      _ ≤ ∑ i ∈ s, ‖a i‖ ^ 2 * K := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = K * coefficientEnergy s a := by
        simp only [coefficientEnergy, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  calc
    ‖form s S a - form s B a‖ ≤
        ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * ‖S i j - B i j‖ :=
      form_comparison_weighted s S B a
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hentry i hi j hj) (by positivity)
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ((‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2) * E i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hE i hi j hj)
      nlinarith [sq_nonneg (‖a i‖ - ‖a j‖)]
    _ = (L + M) / 2 := by
      have hterm : ∀ i j,
          ((‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2) * E i j =
            (‖a i‖ ^ 2 * E i j) / 2 + (‖a j‖ ^ 2 * E i j) / 2 := by
        intros
        ring
      simp_rw [hterm, Finset.sum_add_distrib]
      simp only [← Finset.sum_div]
      dsimp [L, M]
      ring
    _ = L := by rw [hLM]; ring
    _ ≤ K * coefficientEnergy s a := hL

/-- The exact square perturbation, retaining its signed linear term. -/
theorem norm_square_sub_exact (z b : ℂ) :
    ‖z‖ ^ 2 - ‖b‖ ^ 2 =
      2 * (b * star (z - b)).re + ‖z - b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Sharp elementary square-error transfer, before replacing the actual error
norm by any analytic envelope. -/
theorem abs_norm_square_sub_le (z b : ℂ) :
    |‖z‖ ^ 2 - ‖b‖ ^ 2| ≤
      2 * ‖b‖ * ‖z - b‖ + ‖z - b‖ ^ 2 := by
  have hdiff := abs_norm_sub_norm_le z b
  have hz : ‖z‖ ≤ ‖b‖ + ‖z - b‖ := by
    have h := norm_add_le (z - b) b
    rw [sub_add_cancel] at h
    simpa only [add_comm] using h
  calc
    |‖z‖ ^ 2 - ‖b‖ ^ 2| =
        |‖z‖ - ‖b‖| * (‖z‖ + ‖b‖) := by
      rw [show ‖z‖ ^ 2 - ‖b‖ ^ 2 =
        (‖z‖ - ‖b‖) * (‖z‖ + ‖b‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg b))]
    _ ≤ ‖z - b‖ * ((‖b‖ + ‖z - b‖) + ‖b‖) := by
      apply mul_le_mul hdiff (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

/-- Pointwise square transfer from a visible error bound. -/
theorem abs_norm_square_sub_le_of_error (z b : ℂ) (e : ℝ)
    (he : 0 ≤ e) (hz : ‖z - b‖ ≤ e) :
    |‖z‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * ‖b‖ * e + e ^ 2 := by
  apply (abs_norm_square_sub_le z b).trans
  have hsq : ‖z - b‖ ^ 2 ≤ e ^ 2 := by
    nlinarith [norm_nonneg (z - b)]
  have hlin : 2 * ‖b‖ * ‖z - b‖ ≤ 2 * ‖b‖ * e :=
    mul_le_mul_of_nonneg_left hz (by positivity)
  linarith

/-- Pair averaging squares Fourier coefficients. A structured arithmetic
row budget yields a linear-in-envelope term plus the full dense square remainder.
The scalar error hypothesis must be supplied by the analytic zero-sum theorem. -/
theorem square_kernel_form_comparison (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (e K : ℝ)
    (he : 0 ≤ e)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ e)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖B i j‖ ≤ K) :
    ‖form s (fun i j => (‖S i j‖ ^ 2 : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ 2 : ℂ)) a‖ ≤
      (2 * e * K + (s.card : ℝ) * e ^ 2) * coefficientEnergy s a := by
  apply form_comparison_symmetric_row_bound s _ _ a
    (fun i j => 2 * ‖B i j‖ * e + e ^ 2)
    (2 * e * K + (s.card : ℝ) * e ^ 2)
  · intro i hi j hj
    positivity
  · intro i hi j hj
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
      abs_norm_square_sub_le_of_error (S i j) (B i j) e he (herror i hi j hj)
  · intro i hi j hj
    rw [hsym i hi j hj]
  · intro i hi
    calc
      (∑ j ∈ s, (2 * ‖B i j‖ * e + e ^ 2)) =
          2 * e * (∑ j ∈ s, ‖B i j‖) + (s.card : ℝ) * e ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ 2 * e * K + (s.card : ℝ) * e ^ 2 := by
        have ht := mul_le_mul_of_nonneg_left (hrow i hi) (show 0 ≤ 2 * e by positivity)
        linarith

/-- In an actual empirical Fourier matrix the diagonal is exactly one.
Matching diagonals can be omitted from the linear arithmetic row budget,
leaving only the off-diagonal arithmetic sum and the full square remainder. -/
theorem square_kernel_form_comparison_off_diagonal [DecidableEq ι]
    (s : Finset ι) (S B : ι → ι → ℂ) (a : ι → ℂ) (e K : ℝ)
    (he : 0 ≤ e)
    (hdiag : ∀ i ∈ s, S i i = B i i)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ e)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, (if i = j then 0 else ‖B i j‖) ≤ K) :
    ‖form s (fun i j => (‖S i j‖ ^ 2 : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ 2 : ℂ)) a‖ ≤
      (2 * e * K + (s.card : ℝ) * e ^ 2) * coefficientEnergy s a := by
  apply form_comparison_symmetric_row_bound s _ _ a
    (fun i j => 2 * (if i = j then 0 else ‖B i j‖) * e + e ^ 2)
    (2 * e * K + (s.card : ℝ) * e ^ 2)
  · intro i hi j hj
    split_ifs <;> positivity
  · intro i hi j hj
    by_cases hij : i = j
    · subst j
      simpa only [hdiag i hi, sub_self, norm_zero, if_true, mul_zero,
        zero_mul, zero_add] using sq_nonneg e
    · simp only [if_neg hij]
      simpa only [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
        abs_norm_square_sub_le_of_error (S i j) (B i j) e he (herror i hi j hj)
  · intro i hi j hj
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [if_neg hij, if_neg (Ne.symm hij)]
      rw [hsym i hi j hj]
  · intro i hi
    calc
      (∑ j ∈ s, (2 * (if i = j then 0 else ‖B i j‖) * e + e ^ 2)) =
          2 * e * (∑ j ∈ s, (if i = j then 0 else ‖B i j‖)) +
            (s.card : ℝ) * e ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ 2 * e * K + (s.card : ℝ) * e ^ 2 := by
        have ht := mul_le_mul_of_nonneg_left (hrow i hi) (show 0 ≤ 2 * e by positivity)
        linarith

end RiemannResearch.Analysis.ZeroSamplingQuadratic
