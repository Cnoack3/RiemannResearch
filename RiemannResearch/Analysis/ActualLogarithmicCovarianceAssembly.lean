import RiemannResearch.Analysis.ActualZeroLogarithmicEntryBound
import RiemannResearch.Analysis.LogarithmicSamplingBounds

/-!
# Actual-zero logarithmic covariance, conditional only on exponential density

The actual rational Landau estimate supplies the height remainder. Complex
conjugation supplies the negative-frequency entries. Both matrices have exactly
zero diagonal, and the complete signed arithmetic coefficient is retained.
The exponential `strictTail` estimate is the sole remaining analytic premise
in the final provider and coefficient-uniform form theorem.

-/

noncomputable section
open Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualDirichletPolynomialGram
open ActualZeroOrdinate ZeroOrdinate ZeroSamplingQuadratic LogarithmicSamplingBounds

def actualOffDiagonal (T : ℝ) (n m : ℕ) : ℂ :=
  if n = m then 0 else ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ)

def signedArithmetic (n m : ℕ) : ℂ :=
  if n = m then 0 else -(rationalLandauMain (max n m) (min n m) : ℂ)

theorem actual_ordinateSum_neg (T y : ℝ) :
    ordinateSum T (-y) = star (ordinateSum T y) := by
  simp only [ordinateSum, ActualZeroOrdinate.sum, phase_neg,
    star_sum, star_mul, star_natCast]
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

theorem positive_log_div_swap {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Real.log ((n : ℝ) / (m : ℝ)) = -Real.log ((m : ℝ) / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [Real.log_div hn0 hm0, Real.log_div hm0 hn0]
  ring

theorem actualOffDiagonal_star_swap (T : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    actualOffDiagonal T n m = star (actualOffDiagonal T m n) := by
  by_cases hnm : n = m
  · subst m
    simp [actualOffDiagonal]
  · simp only [actualOffDiagonal, if_neg hnm, if_neg (Ne.symm hnm)]
    rw [positive_log_div_swap hn hm, actual_ordinateSum_neg]
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]

theorem signedArithmetic_swap (n m : ℕ) :
    signedArithmetic n m = signedArithmetic m n := by
  simp only [signedArithmetic, max_comm, min_comm, eq_comm]

theorem signedArithmetic_star (n m : ℕ) :
    star (signedArithmetic n m) = signedArithmetic n m := by
  unfold signedArithmetic
  split_ifs <;> simp [Complex.star_def]

theorem actual_error_norm_swap (T : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖actualOffDiagonal T n m - signedArithmetic n m‖ =
      ‖actualOffDiagonal T m n - signedArithmetic m n‖ := by
  calc
    _ = ‖star (actualOffDiagonal T m n - signedArithmetic m n)‖ := by
      rw [actualOffDiagonal_star_swap T hn hm, signedArithmetic_swap n m,
        star_sub, signedArithmetic_star]
    _ = _ := norm_star _

/-- A positive-frequency provider automatically supplies all signs, with the
diagonal removed exactly. This is a transfer lemma, not an analytic input. -/
theorem actual_all_sign_entry_envelope (T : ℝ) (X : ℕ) (d L η : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hpositive : ∀ n ∈ Finset.Icc 1 X, ∀ m ∈ Finset.Icc 1 X, m < n →
      ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) -
          (-(rationalLandauMain n m : ℂ))‖ ≤
        d / L * logSquareEnvelope n m + η) :
    ∀ n ∈ Finset.Icc 1 X, ∀ m ∈ Finset.Icc 1 X,
      ‖actualOffDiagonal T n m - signedArithmetic n m‖ ≤
        d / L * logSquareEnvelope n m + η := by
  intro n hn m hm
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  by_cases hnm : n = m
  · subst m
    simp only [actualOffDiagonal, signedArithmetic, if_true, sub_self, norm_zero]
    exact add_nonneg
      (mul_nonneg (div_nonneg hd hL.le) (logSquareEnvelope_nonneg _ _)) hη
  · rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have h := hpositive m hm n hn hlt
      have hmne : m ≠ n := Ne.symm hnm
      have he : ‖actualOffDiagonal T m n - signedArithmetic m n‖ =
          ‖ordinateSum T (Real.log ((m : ℝ) / (n : ℝ))) / (T : ℂ) -
            (-(rationalLandauMain m n : ℂ))‖ := by
        simp only [actualOffDiagonal, signedArithmetic, if_neg hmne,
          max_eq_left hlt.le, min_eq_right hlt.le]
      calc
        _ = ‖actualOffDiagonal T m n - signedArithmetic m n‖ :=
          actual_error_norm_swap T hn1 hm1
        _ = ‖ordinateSum T (Real.log ((m : ℝ) / (n : ℝ))) / (T : ℂ) -
            (-(rationalLandauMain m n : ℂ))‖ := he
        _ ≤ d / L * logSquareEnvelope m n + η := h
        _ = d / L * logSquareEnvelope n m + η := by
          rw [logSquareEnvelope_symm m n]
    · simpa only [actualOffDiagonal, signedArithmetic, if_neg hnm,
        max_eq_left hgt.le, min_eq_right hgt.le] using hpositive n hn m hm hgt

/-- Every complex coefficient family is controlled by the proved logarithmic
matrix moment. The complete signed arithmetic form remains in the statement. -/
theorem actual_offDiagonal_form_bound_from_positive
    (T : ℝ) (X : ℕ) (a : ℕ → ℂ) (d L η : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hpositive : ∀ n ∈ Finset.Icc 1 X, ∀ m ∈ Finset.Icc 1 X, m < n →
      ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) -
          (-(rationalLandauMain n m : ℂ))‖ ≤
        d / L * logSquareEnvelope n m + η) :
    ‖form (Finset.Icc 1 X) (actualOffDiagonal T) a -
        form (Finset.Icc 1 X) signedArithmetic a‖ ≤
      (d * Real.sqrt (24 * (X : ℝ) * ((X : ℝ) + 1)) / L + η * (X : ℝ)) *
        coefficientEnergy (Finset.Icc 1 X) a :=
  logarithmic_hilbertSchmidt_single X (actualOffDiagonal T) signedArithmetic a
    d L η hd hL hη (actual_all_sign_entry_envelope T X d L η hd hL hη hpositive)

/-- The actual Landau provider discharges every sampling entry premise.
The sole analytic hypothesis still visible here is the exponential density
bound on actual multiplicity-weighted strict tails. -/
theorem exists_actual_logarithmic_covariance_of_exponential_density :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (T L C_D : ℝ) (X : ℕ) (a : ℕ → ℂ),
      9 ≤ T → 0 ≤ C_D → 0 < L → Real.log (X : ℝ) ≤ L / 8 →
      (∀ v ∈ Icc (0 : ℝ) (1 / 2),
        strictTail T v ≤ 2 * C_D * T * L * Real.exp (-(L / 4) * v)) →
      ‖form (Finset.Icc 1 X) (actualOffDiagonal T) a -
          form (Finset.Icc 1 X) signedArithmetic a‖ ≤
        (((128 * C_D / 3) * Real.sqrt (24 * (X : ℝ) * ((X : ℝ) + 1)) / L) +
          ((C_A / T) * rationalLandauRpowEnvelope T (X : ℝ)) * (X : ℝ)) *
            coefficientEnergy (Finset.Icc 1 X) a := by
  obtain ⟨C_A, hC_A, hentry⟩ :=
    exists_uniform_actual_rational_entry_bound_of_exponential_density
  refine ⟨C_A, hC_A, ?_⟩
  intro T L C_D X a hT hC_D hL hX hdensity
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hη : 0 ≤ (C_A / T) * rationalLandauRpowEnvelope T (X : ℝ) := by
    unfold rationalLandauRpowEnvelope
    positivity
  apply actual_offDiagonal_form_bound_from_positive
    T X a (128 * C_D / 3) L ((C_A / T) * rationalLandauRpowEnvelope T (X : ℝ))
    (by positivity) hL hη
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

/-- Literal Dirichlet polynomial on an actual zero copy. -/
def copyPolynomial (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) (c : Copies T) : ℂ :=
  ∑ n ∈ s, a n * phase (Real.log (n : ℝ)) c.1.1.im

/-- Every analytic multiplicity is represented by an individual actual copy. -/
def actualCopiedSquare (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c : Copies T, copyPolynomial T s a c * star (copyPolynomial T s a c)

def actualNormalizedFullGram (T : ℝ) (n m : ℕ) : ℂ :=
  ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ)) / (T : ℂ)

theorem copy_samplingGram_eq_ordinate (T : ℝ) (n m : ℕ) :
    samplingGram (Finset.univ : Finset (Copies T)) (fun _ => (1 : ℝ))
      (fun c k => phase (Real.log (k : ℝ)) c.1.1.im) n m =
        ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ)) := by
  classical
  rw [ordinateSum, sum_eq_copies]
  simp only [samplingGram, Complex.ofReal_one, one_mul, phase_sub]

/-- Exact normalized Gram identity; no analytic estimate or zero deletion. -/
theorem actualCopiedSquare_div_eq_fullGram (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) :
    actualCopiedSquare T s a / (T : ℂ) = form s (actualNormalizedFullGram T) a := by
  classical
  have hk : (fun n m : ℕ => ordinateSum T
      (Real.log (n : ℝ) - Real.log (m : ℝ))) =
        samplingGram (Finset.univ : Finset (Copies T)) (fun _ => (1 : ℝ))
          (fun c (k : ℕ) => phase (Real.log (k : ℝ)) c.1.1.im) := by
    funext n m
    exact (copy_samplingGram_eq_ordinate T n m).symm
  have hbase : form s (fun n m => ordinateSum T
      (Real.log (n : ℝ) - Real.log (m : ℝ))) a = actualCopiedSquare T s a := by
    rw [hk, form_samplingGram]
    simp only [actualCopiedSquare, copyPolynomial, Complex.ofReal_one, one_mul]
  rw [← hbase]
  calc
    _ = (T : ℂ)⁻¹ * form s (fun n m => ordinateSum T
        (Real.log (n : ℝ) - Real.log (m : ℝ))) a := by ring
    _ = form s (fun n m => (T : ℂ)⁻¹ * ordinateSum T
        (Real.log (n : ℝ) - Real.log (m : ℝ))) a := (form_mul _ _ _ _).symm
    _ = form s (actualNormalizedFullGram T) a := by
      congr 1
      funext n m
      unfold actualNormalizedFullGram
      ring

theorem actualNormalizedFullGram_split (T : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    actualNormalizedFullGram T n m =
      (if n = m then (Zeta23.Ncount 0 T : ℂ) / (T : ℂ) else 0) +
        actualOffDiagonal T n m := by
  by_cases hnm : n = m
  · subst m
    simp [actualNormalizedFullGram, actualOffDiagonal, ordinateSum]
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    simp only [actualNormalizedFullGram, actualOffDiagonal, if_neg hnm, zero_add]
    rw [Real.log_div hn0 hm0]

/-- Original-count diagonal subtraction equals the actual off-diagonal form
exactly, including all signed cross terms and all zero occurrences. -/
theorem actualCopiedSquare_centered_eq_offDiagonal
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, 1 ≤ n) :
    actualCopiedSquare T s a / (T : ℂ) -
        ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) * (coefficientEnergy s a : ℂ) =
      form s (actualOffDiagonal T) a := by
  classical
  let D : ℕ → ℕ → ℂ := fun n m =>
    if n = m then (Zeta23.Ncount 0 T : ℂ) / (T : ℂ) else 0
  have hdiag : form s D a =
      ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) * (coefficientEnergy s a : ℂ) := by
    have he : D = fun n m => ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) *
        (if n = m then 1 else 0) := by
      funext n m
      dsimp [D]
      by_cases hnm : n = m <;> simp [hnm]
    rw [he, form_mul, form_identity]
  have hsplit : form s (actualNormalizedFullGram T) a =
      form s D a + form s (actualOffDiagonal T) a := by
    rw [← form_add]
    unfold form
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [actualNormalizedFullGram_split T (hs n hn) (hs m hm)] <;> rfl
  apply sub_eq_iff_eq_add.mpr
  calc
    _ = form s (actualNormalizedFullGram T) a := actualCopiedSquare_div_eq_fullGram T s a
    _ = form s D a + form s (actualOffDiagonal T) a := hsplit
    _ = form s (actualOffDiagonal T) a +
        ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) * (coefficientEnergy s a : ℂ) := by
      rw [hdiag]
      ring

/-- Complete actual sampled-square covariance, conditional only on the
explicit exponential strict-tail density bound. -/
theorem exists_actual_sampled_covariance_of_exponential_density :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (T L C_D : ℝ) (X : ℕ) (a : ℕ → ℂ),
      9 ≤ T → 0 ≤ C_D → 0 < L → Real.log (X : ℝ) ≤ L / 8 →
      (∀ v ∈ Icc (0 : ℝ) (1 / 2),
        strictTail T v ≤ 2 * C_D * T * L * Real.exp (-(L / 4) * v)) →
      ‖actualCopiedSquare T (Finset.Icc 1 X) a / (T : ℂ) -
          ((Zeta23.Ncount 0 T : ℂ) / (T : ℂ)) *
            (coefficientEnergy (Finset.Icc 1 X) a : ℂ) -
          form (Finset.Icc 1 X) signedArithmetic a‖ ≤
        (((128 * C_D / 3) * Real.sqrt (24 * (X : ℝ) * ((X : ℝ) + 1)) / L) +
          ((C_A / T) * rationalLandauRpowEnvelope T (X : ℝ)) * (X : ℝ)) *
            coefficientEnergy (Finset.Icc 1 X) a := by
  obtain ⟨C_A, hC_A, hform⟩ := exists_actual_logarithmic_covariance_of_exponential_density
  refine ⟨C_A, hC_A, ?_⟩
  intro T L C_D X a hT hC_D hL hX hdensity
  rw [actualCopiedSquare_centered_eq_offDiagonal T (Finset.Icc 1 X) a
    (fun n hn => (Finset.mem_Icc.mp hn).1)]
  exact hform T L C_D X a hT hC_D hL hX hdensity

end RiemannResearch.Analysis.ActualDirichletPolynomialGram
