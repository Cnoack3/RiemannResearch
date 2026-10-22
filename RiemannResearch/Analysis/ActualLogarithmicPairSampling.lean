import RiemannResearch.Analysis.ActualLogarithmicCovarianceAssembly

/-!
# Actual multiplicity-copy pair sampling and conditional logarithmic transfer

The pair sampling identity is finite algebra for the actual copies of all zeros.
The quantitative transfer uses the proved actual rational Landau provider and
an explicit exponential strict-tail density hypothesis. Weighted arithmetic row
estimates are also explicit hypotheses; no number-theoretic row estimate is
silently assumed. No compiler or server was run while drafting this module.
-/

noncomputable section
open Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualDirichletPolynomialGram
open ActualZeroOrdinate ZeroOrdinate ZeroSamplingQuadratic LogarithmicSamplingBounds

theorem pair_phase_comm (u t : ℝ) : phase u t = phase t u := by
  unfold phase
  rw [mul_comm u t]

theorem pair_phase_time_sub (u t s : ℝ) :
    phase u (t - s) = phase u t * star (phase u s) := by
  calc
    _ = phase (t - s) u := pair_phase_comm u (t - s)
    _ = phase t u * star (phase s u) := phase_sub t s u
    _ = phase u t * star (phase u s) := by
      rw [pair_phase_comm t u, pair_phase_comm s u]

theorem pair_complex_mul_star_normSquare (z : ℂ) :
    z * star z = (‖z‖ ^ 2 : ℂ) := by
  simpa only [Complex.star_def] using Complex.mul_conj' z

/-- Normalization of a complex square is exact even when the denominator is zero. -/
theorem pair_complex_div_mul_star (z : ℂ) (r : ℝ) :
    (z * star z) / (r : ℂ) ^ 2 =
      (z / (r : ℂ)) * star (z / (r : ℂ)) := by
  simp only [star_div₀, Complex.star_def, Complex.conj_ofReal,
    pow_two, div_mul_div_comm]

/-- The same literal Dirichlet polynomial, now at the difference of two actual
zero occurrences. The copies retain both analytic multiplicities. -/
def pairCopyPolynomial (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ)
    (c d : Copies T) : ℂ :=
  ∑ n ∈ s, a n * phase (Real.log (n : ℝ)) (c.1.1.im - d.1.1.im)

def actualPairCopiedSquare (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c : Copies T, ∑ d : Copies T,
    pairCopyPolynomial T s a c d * star (pairCopyPolynomial T s a c d)

/-- The literal real sum of squared absolute values requested in pair sampling. -/
def actualPairSampledEnergy (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ c : Copies T, ∑ d : Copies T, ‖pairCopyPolynomial T s a c d‖ ^ 2

theorem actualPairCopiedSquare_eq_real (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) :
    actualPairCopiedSquare T s a = (actualPairSampledEnergy T s a : ℂ) := by
  classical
  simp only [actualPairCopiedSquare, actualPairSampledEnergy,
    pair_complex_mul_star_normSquare, Complex.ofReal_sum, Complex.ofReal_pow]

def actualNormalizedPairGram (T : ℝ) (n m : ℕ) : ℂ :=
  actualNormalizedFullGram T n m * star (actualNormalizedFullGram T n m)

/-- The pair Fourier coefficient is exactly the squared absolute value of the
single Fourier coefficient, before any approximation. -/
theorem pair_copy_samplingGram_eq_product (T : ℝ) (n m : ℕ) :
    samplingGram (Finset.univ : Finset (Copies T × Copies T)) (fun _ => (1 : ℝ))
      (fun p (k : ℕ) => phase (Real.log (k : ℝ))
        (p.1.1.1.im - p.2.1.1.im)) n m =
      ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ)) *
        star (ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ))) := by
  classical
  simp only [samplingGram, Complex.ofReal_one, one_mul]
  simp_rw [← phase_sub]
  rw [Fintype.sum_prod_type]
  simp_rw [pair_phase_time_sub]
  simp only [ordinateSum, sum_eq_copies, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem actualPairCopiedSquare_div_eq_fullPairGram
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) :
    actualPairCopiedSquare T s a / (T : ℂ) ^ 2 =
      form s (actualNormalizedPairGram T) a := by
  classical
  let G : ℕ → ℕ → ℂ := fun n m =>
    ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ)) *
      star (ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ)))
  have hk : G =
      samplingGram (Finset.univ : Finset (Copies T × Copies T)) (fun _ => (1 : ℝ))
        (fun p (k : ℕ) => phase (Real.log (k : ℝ))
          (p.1.1.1.im - p.2.1.1.im)) := by
    funext n m
    exact (pair_copy_samplingGram_eq_product T n m).symm
  have hbase : form s G a = actualPairCopiedSquare T s a := by
    rw [hk, form_samplingGram]
    simp only [actualPairCopiedSquare, pairCopyPolynomial, Complex.ofReal_one,
      one_mul, Fintype.sum_prod_type]
  rw [← hbase]
  calc
    _ = ((T : ℂ) ^ 2)⁻¹ * form s G a := by ring
    _ = form s (fun n m => ((T : ℂ) ^ 2)⁻¹ * G n m) a :=
      (form_mul _ _ _ _).symm
    _ = form s (actualNormalizedPairGram T) a := by
      congr 1
      funext n m
      dsimp [G, actualNormalizedPairGram, actualNormalizedFullGram]
      calc
        _ = (ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ)) *
            star (ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ)))) /
              (T : ℂ) ^ 2 := by
          simp only [Complex.star_def]
          ring
        _ = _ := pair_complex_div_mul_star _ T

theorem actualNormalizedPairGram_split (T : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    actualNormalizedPairGram T n m =
      (if n = m then ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) ^ 2 else 0) +
        (‖actualOffDiagonal T n m‖ ^ 2 : ℂ) := by
  by_cases hnm : n = m
  · subst m
    have hfull := actualNormalizedFullGram_split T hn hn
    simp only [actualOffDiagonal, if_true, add_zero] at hfull
    simp [actualNormalizedPairGram, hfull, actualOffDiagonal,
      Complex.star_def, pow_two]
  · have hfull := actualNormalizedFullGram_split T hn hm
    simp only [if_neg hnm, zero_add] at hfull
    simpa only [actualNormalizedPairGram, if_neg hnm, zero_add, hfull] using
      pair_complex_mul_star_normSquare (actualOffDiagonal T n m)

/-- Exact pair centering uses the square of the original zero count. No zero
occurrence is omitted, and no probabilistic independence is invoked. -/
theorem actualPairCopiedSquare_centered_eq_offDiagonal
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, 1 ≤ n) :
    actualPairCopiedSquare T s a / (T : ℂ) ^ 2 -
        ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) ^ 2 * (coefficientEnergy s a : ℂ) =
      form s (fun n m => (‖actualOffDiagonal T n m‖ ^ 2 : ℂ)) a := by
  classical
  let D : ℕ → ℕ → ℂ := fun n m =>
    if n = m then ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) ^ 2 else 0
  have hdiag : form s D a =
      ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) ^ 2 * (coefficientEnergy s a : ℂ) := by
    have he : D = fun n m => ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) ^ 2 *
        (if n = m then 1 else 0) := by
      funext n m
      dsimp [D]
      by_cases hnm : n = m <;> simp [hnm]
    rw [he, form_mul, form_identity]
  have hsplit : form s (actualNormalizedPairGram T) a =
      form s D a + form s (fun n m => (‖actualOffDiagonal T n m‖ ^ 2 : ℂ)) a := by
    rw [← form_add]
    unfold form
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [actualNormalizedPairGram_split T (hs n hn) (hs m hm)] <;> rfl
  apply sub_eq_iff_eq_add.mpr
  calc
    _ = form s (actualNormalizedPairGram T) a :=
      actualPairCopiedSquare_div_eq_fullPairGram T s a
    _ = form s D a + form s (fun n m => (‖actualOffDiagonal T n m‖ ^ 2 : ℂ)) a := hsplit
    _ = form s (fun n m => (‖actualOffDiagonal T n m‖ ^ 2 : ℂ)) a +
        ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) ^ 2 * (coefficientEnergy s a : ℂ) := by
      rw [hdiag]
      ring

/-- Literal real pair sampled-square identity, embedded into the complex form. -/
theorem actualPairSampledEnergy_centered_eq_offDiagonal
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, 1 ≤ n) :
    ((actualPairSampledEnergy T s a / T ^ 2 -
        ((Zeta23.Ncount 0 T : ℝ) / T) ^ 2 * coefficientEnergy s a : ℝ) : ℂ) =
      form s (fun n m => (‖actualOffDiagonal T n m‖ ^ 2 : ℂ)) a := by
  have h := actualPairCopiedSquare_centered_eq_offDiagonal T s a hs
  rw [actualPairCopiedSquare_eq_real] at h
  push_cast
  exact h

/-- The exact cross contribution and dense square contribution are kept apart.
In particular, the logarithmic weighted row bound enters linearly. -/
def actualPairErrorCoefficient (X : ℕ) (d L η KA K0 : ℝ) : ℝ :=
  2 * (d / L) * KA + 2 * η * K0 +
    (d / L) ^ 2 * Real.sqrt (40320 * (X : ℝ) * ((X : ℝ) + 1)) +
    2 * (d / L) * η * Real.sqrt (24 * (X : ℝ) * ((X : ℝ) + 1)) +
    η ^ 2 * (X : ℝ)

theorem actual_pair_form_bound_from_positive
    (T : ℝ) (X : ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ) (d L η KA K0 : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hw : ∀ n ∈ Finset.Icc 1 X, 0 < w n)
    (hpositive : ∀ n ∈ Finset.Icc 1 X, ∀ m ∈ Finset.Icc 1 X, m < n →
      ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) -
          (-(rationalLandauMain n m : ℂ))‖ ≤
        d / L * logSquareEnvelope n m + η)
    (hrowA : ∀ n ∈ Finset.Icc 1 X,
      (∑ m ∈ Finset.Icc 1 X, (‖signedArithmetic n m‖ * logSquareEnvelope n m) * w m) ≤
        KA * w n)
    (hrow0 : ∀ n ∈ Finset.Icc 1 X,
      (∑ m ∈ Finset.Icc 1 X, ‖signedArithmetic n m‖ * w m) ≤ K0 * w n) :
    ‖form (Finset.Icc 1 X) (fun n m => (‖actualOffDiagonal T n m‖ ^ 2 : ℂ)) a -
        form (Finset.Icc 1 X) (fun n m => (‖signedArithmetic n m‖ ^ 2 : ℂ)) a‖ ≤
      actualPairErrorCoefficient X d L η KA K0 * coefficientEnergy (Finset.Icc 1 X) a := by
  exact logarithmic_square_kernel_weighted_exact_cross X (actualOffDiagonal T)
    signedArithmetic a w d L η KA K0 hd hL hη
    (fun n _ m _ => congrArg norm (signedArithmetic_swap n m)) hw
    (actual_all_sign_entry_envelope T X d L η hd hL hη hpositive) hrowA hrow0

/-- Actual rational Landau supplies the uniform height constant. Exponential
density and the two displayed arithmetic row estimates remain explicit inputs. -/
theorem exists_actual_pair_form_of_exponential_density_and_rows :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (T L C_D : ℝ) (X : ℕ) (a : ℕ → ℂ)
      (w : ℕ → ℝ) (KA K0 : ℝ),
      9 ≤ T → 0 ≤ C_D → 0 < L → Real.log (X : ℝ) ≤ L / 8 →
      (∀ v ∈ Icc (0 : ℝ) (1 / 2),
        strictTail T v ≤ 2 * C_D * T * L * Real.exp (-(L / 4) * v)) →
      (∀ n ∈ Finset.Icc 1 X, 0 < w n) →
      (∀ n ∈ Finset.Icc 1 X,
        (∑ m ∈ Finset.Icc 1 X, (‖signedArithmetic n m‖ * logSquareEnvelope n m) * w m) ≤
          KA * w n) →
      (∀ n ∈ Finset.Icc 1 X,
        (∑ m ∈ Finset.Icc 1 X, ‖signedArithmetic n m‖ * w m) ≤ K0 * w n) →
      ‖form (Finset.Icc 1 X) (fun n m => (‖actualOffDiagonal T n m‖ ^ 2 : ℂ)) a -
          form (Finset.Icc 1 X) (fun n m => (‖signedArithmetic n m‖ ^ 2 : ℂ)) a‖ ≤
        actualPairErrorCoefficient X (128 * C_D / 3) L
          ((C_A / T) * rationalLandauRpowEnvelope T (X : ℝ)) KA K0 *
            coefficientEnergy (Finset.Icc 1 X) a := by
  obtain ⟨C_A, hC_A, hentry⟩ :=
    exists_uniform_actual_rational_entry_bound_of_exponential_density
  refine ⟨C_A, hC_A, ?_⟩
  intro T L C_D X a w KA K0 hT hC_D hL hX hdensity hw hrowA hrow0
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hη : 0 ≤ (C_A / T) * rationalLandauRpowEnvelope T (X : ℝ) := by
    unfold rationalLandauRpowEnvelope
    positivity
  apply actual_pair_form_bound_from_positive T X a w (128 * C_D / 3) L
    ((C_A / T) * rationalLandauRpowEnvelope T (X : ℝ)) KA K0
    (by positivity) hL hη hw ?_ hrowA hrow0
  intro n hn m hm hmn
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hnX : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hyX : Real.log ((n : ℝ) / (m : ℝ)) ≤ Real.log (X : ℝ) :=
    (rational_frequency_bounds hm1 hmn hnX).2.1
  have h := hentry T (X : ℝ) L C_D n m hT hm1 hmn hnX hC_D hL
    (hyX.trans hX) hdensity
  calc
    _ ≤ (128 * C_D / 3) * (Real.log ((n : ℝ) / (m : ℝ))) ^ 2 / L +
        (C_A / T) * rationalLandauRpowEnvelope T (X : ℝ) := h
    _ = (128 * C_D / 3) / L * logSquareEnvelope n m +
        (C_A / T) * rationalLandauRpowEnvelope T (X : ℝ) := by
      unfold logSquareEnvelope
      ring

/-- Complete actual pair sampled covariance with the exact squared arithmetic
main term, conditional on exponential density and explicit arithmetic rows. -/
theorem exists_actual_pair_sampled_covariance_of_exponential_density_and_rows :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (T L C_D : ℝ) (X : ℕ) (a : ℕ → ℂ)
      (w : ℕ → ℝ) (KA K0 : ℝ),
      9 ≤ T → 0 ≤ C_D → 0 < L → Real.log (X : ℝ) ≤ L / 8 →
      (∀ v ∈ Icc (0 : ℝ) (1 / 2),
        strictTail T v ≤ 2 * C_D * T * L * Real.exp (-(L / 4) * v)) →
      (∀ n ∈ Finset.Icc 1 X, 0 < w n) →
      (∀ n ∈ Finset.Icc 1 X,
        (∑ m ∈ Finset.Icc 1 X, (‖signedArithmetic n m‖ * logSquareEnvelope n m) * w m) ≤
          KA * w n) →
      (∀ n ∈ Finset.Icc 1 X,
        (∑ m ∈ Finset.Icc 1 X, ‖signedArithmetic n m‖ * w m) ≤ K0 * w n) →
      ‖((actualPairSampledEnergy T (Finset.Icc 1 X) a / T ^ 2 -
          ((Zeta23.Ncount 0 T : ℝ) / T) ^ 2 *
            coefficientEnergy (Finset.Icc 1 X) a : ℝ) : ℂ) -
        form (Finset.Icc 1 X) (fun n m => (‖signedArithmetic n m‖ ^ 2 : ℂ)) a‖ ≤
        actualPairErrorCoefficient X (128 * C_D / 3) L
          ((C_A / T) * rationalLandauRpowEnvelope T (X : ℝ)) KA K0 *
            coefficientEnergy (Finset.Icc 1 X) a := by
  obtain ⟨C_A, hC_A, hform⟩ := exists_actual_pair_form_of_exponential_density_and_rows
  refine ⟨C_A, hC_A, ?_⟩
  intro T L C_D X a w KA K0 hT hC_D hL hX hdensity hw hrowA hrow0
  rw [actualPairSampledEnergy_centered_eq_offDiagonal T (Finset.Icc 1 X) a
    (fun n hn => (Finset.mem_Icc.mp hn).1)]
  exact hform T L C_D X a w KA K0 hT hC_D hL hX hdensity hw hrowA hrow0

end RiemannResearch.Analysis.ActualDirichletPolynomialGram
