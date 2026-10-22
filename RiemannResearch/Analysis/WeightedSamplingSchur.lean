import RiemannResearch.Analysis.ZeroSamplingErrorTransfer
import RiemannResearch.Analysis.ZeroSamplingHilbertSchmidt

/-!
# Weighted Schur budgets for arithmetic sampling kernels

The positive weight may be `w n = n^(-1/2)` in a zeta-zero application.
Weighted row budgets are kept as weighted row budgets; they are not replaced
by stronger unweighted bounds.

Source for the elementary weighted Young proof: the repository module
`FiniteWeightedSchurPairing.lean`, derived from the user's prime-phase manuscript.
The analytic arithmetic row and moment estimates remain explicit hypotheses.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ZeroSamplingQuadratic

variable {ι : Type*}

private theorem weighted_sampling_young (x y b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    2 * x * y ≤ x ^ 2 * c / b + y ^ 2 * b / c := by
  have hsq : 2 * x * y * (b * c) ≤ x ^ 2 * c ^ 2 + y ^ 2 * b ^ 2 := by
    nlinarith [sq_nonneg (x * c - y * b)]
  calc
    _ ≤ (x ^ 2 * c ^ 2 + y ^ 2 * b ^ 2) / (b * c) :=
      (le_div_iff₀ (mul_pos hb hc)).mpr hsq
    _ = _ := by field_simp [hb.ne', hc.ne'] <;> ring

/-- Positive weighted row bounds control the coefficient-weighted envelope.
The finite weights need no upper bound or lower bound uniform in the support. -/
theorem weighted_symmetric_schur_budget (s : Finset ι) (a : ι → ℂ)
    (E : ι → ι → ℝ) (w : ι → ℝ) (K : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, E i j = E j i)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, E i j * w j) ≤ K * w i) :
    (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j) ≤
      K * coefficientEnergy s a := by
  let Q : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j
  let U : ℝ := ∑ i ∈ s, ∑ j ∈ s, E i j * (‖a i‖ ^ 2 * w j / w i)
  let V : ℝ := ∑ i ∈ s, ∑ j ∈ s, E i j * (‖a j‖ ^ 2 * w i / w j)
  have hUV : V = U := by
    dsimp [V, U]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have htwo : 2 * Q ≤ U + V := by
    dsimp [Q, U, V]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have h := mul_le_mul_of_nonneg_left
      (weighted_sampling_young ‖a i‖ ‖a j‖ (w i) (w j) (hw i hi) (hw j hj))
      (hE i hi j hj)
    convert h using 1 <;> ring
  have hU : U ≤ K * coefficientEnergy s a := by
    calc
      U = ∑ i ∈ s, (‖a i‖ ^ 2 / w i) * (∑ j ∈ s, E i j * w j) := by
        dsimp [U]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ i ∈ s, (‖a i‖ ^ 2 / w i) * (K * w i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi)
          (div_nonneg (sq_nonneg _) (hw i hi).le)
      _ = K * coefficientEnergy s a := by
        simp only [coefficientEnergy, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [(hw i hi).ne'] <;> ring
  rw [hUV] at htwo
  change Q ≤ K * coefficientEnergy s a
  linarith

/-- A symmetric real envelope suffices for form comparison. No symmetry of the
complex error itself, nor any alignment of its arguments, is needed. -/
theorem form_comparison_weighted_schur (s : Finset ι)
    (S H : ι → ι → ℂ) (a : ι → ℂ) (E : ι → ι → ℝ)
    (w : ι → ℝ) (K : ℝ)
    (hE : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ E i j)
    (hentry : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - H i j‖ ≤ E i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, E i j = E j i)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, E i j * w j) ≤ K * w i) :
    ‖form s S a - form s H a‖ ≤ K * coefficientEnergy s a := by
  calc
    ‖form s S a - form s H a‖ ≤
        ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * ‖S i j - H i j‖ :=
      form_comparison_weighted s S H a
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * E i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hentry i hi j hj) (by positivity)
    _ ≤ K * coefficientEnergy s a :=
      weighted_symmetric_schur_budget s a E w K hE hsym hw hrow

/-- Keep the exact scalar expansion before bounding its mixed remainder. -/
theorem square_error_envelope_expansion (b d A η : ℝ) :
    2 * b * (d * A + η) + (d * A + η) ^ 2 =
      2 * d * b * A + 2 * η * b + d ^ 2 * A ^ 2 +
        2 * d * η * A + η ^ 2 := by ring

/-- A scalar norm envelope transfers to squared Fourier coefficients. The
mixed square remainder is bounded by its two complete squares. -/
theorem square_error_nonnegative_envelope (z b : ℂ) (d A η : ℝ)
    (hd : 0 ≤ d) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (herror : ‖z - b‖ ≤ d * A + η) :
    |‖z‖ ^ 2 - ‖b‖ ^ 2| ≤
      2 * d * ‖b‖ * A + 2 * η * ‖b‖ +
        2 * d ^ 2 * A ^ 2 + 2 * η ^ 2 := by
  apply (abs_norm_square_sub_le_of_error z b (d * A + η) (by positivity) herror).trans
  nlinarith [sq_nonneg (d * A - η)]

/-- Weighted arithmetic Schur budgets and an unweighted fourth-moment budget
give the pair covariance bound. The application must supply all displayed
row estimates and the actual zero-sum error envelope. -/
theorem square_kernel_weighted_arithmetic_transfer (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (A : ι → ι → ℝ)
    (w : ι → ℝ) (d η KA K0 M₄ : ℝ)
    (hd : 0 ≤ d) (hη : 0 ≤ η)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (hAsym : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i)
    (hBsym : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hw : ∀ i ∈ s, 0 < w i)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ d * A i j + η)
    (hrowA : ∀ i ∈ s,
      (∑ j ∈ s, (‖B i j‖ * A i j) * w j) ≤ KA * w i)
    (hrow0 : ∀ i ∈ s, (∑ j ∈ s, ‖B i j‖ * w j) ≤ K0 * w i)
    (hmoment : (∑ i ∈ s, ∑ j ∈ s, A i j ^ 4) ≤ M₄) :
    ‖form s (fun i j => (‖S i j‖ ^ 2 : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ 2 : ℂ)) a‖ ≤
      (2 * d * KA + 2 * η * K0 + 2 * d ^ 2 * Real.sqrt M₄ +
        2 * η ^ 2 * (s.card : ℝ)) * coefficientEnergy s a := by
  let P1 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (‖B i j‖ * A i j)
  let P0 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * ‖B i j‖
  let P2 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * A i j ^ 2
  let Pd : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖
  have h1 : P1 ≤ KA * coefficientEnergy s a := by
    apply weighted_symmetric_schur_budget s a (fun i j => ‖B i j‖ * A i j) w KA
    · intro i hi j hj
      exact mul_nonneg (norm_nonneg _) (hA i hi j hj)
    · intro i hi j hj
      rw [hBsym i hi j hj, hAsym i hi j hj]
    · exact hw
    · exact hrowA
  have h0 : P0 ≤ K0 * coefficientEnergy s a :=
    weighted_symmetric_schur_budget s a (fun i j => ‖B i j‖) w K0
      (fun i hi j hj => norm_nonneg _) hBsym hw hrow0
  have h2 : P2 ≤ Real.sqrt M₄ * coefficientEnergy s a := by
    apply weighted_envelope_hilbertSchmidt_bound s a (fun i j => A i j ^ 2) M₄
    · intro i hi j hj
      exact sq_nonneg _
    · simpa only [← pow_mul] using hmoment
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hdense : Pd ≤ (s.card : ℝ) * coefficientEnergy s a := by
    dsimp [Pd]
    calc
      _ = (∑ i ∈ s, ‖a i‖) ^ 2 := by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ _ := hcs
  have hnorm :
      ‖form s (fun i j => (‖S i j‖ ^ 2 : ℂ)) a -
          form s (fun i j => (‖B i j‖ ^ 2 : ℂ)) a‖ ≤
        2 * d * P1 + 2 * η * P0 + 2 * d ^ 2 * P2 + 2 * η ^ 2 * Pd := by
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ *
          ‖(‖S i j‖ ^ 2 : ℂ) - (‖B i j‖ ^ 2 : ℂ)‖ :=
        form_comparison_weighted s _ _ a
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ *
          (2 * d * ‖B i j‖ * A i j + 2 * η * ‖B i j‖ +
            2 * d ^ 2 * A i j ^ 2 + 2 * η ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [← Complex.ofReal_pow, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs] using
          square_error_nonnegative_envelope (S i j) (B i j) d (A i j) η
            hd (hA i hi j hj) hη (herror i hi j hj)
      _ = _ := by
        dsimp [P1, P0, P2, Pd]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  calc
    _ ≤ 2 * d * P1 + 2 * η * P0 + 2 * d ^ 2 * P2 + 2 * η ^ 2 * Pd := hnorm
    _ ≤ 2 * d * (KA * coefficientEnergy s a) +
        2 * η * (K0 * coefficientEnergy s a) +
        2 * d ^ 2 * (Real.sqrt M₄ * coefficientEnergy s a) +
        2 * η ^ 2 * ((s.card : ℝ) * coefficientEnergy s a) := by
      exact add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h0 (by positivity)))
        (mul_le_mul_of_nonneg_left h2 (by positivity)))
        (mul_le_mul_of_nonneg_left hdense (by positivity))
    _ = _ := by ring

/-- The complete five-term square envelope, retaining the mixed remainder. -/
theorem square_error_nonnegative_envelope_exact_cross (z b : ℂ) (d A η : ℝ)
    (hd : 0 ≤ d) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (herror : ‖z - b‖ ≤ d * A + η) :
    |‖z‖ ^ 2 - ‖b‖ ^ 2| ≤
      2 * d * ‖b‖ * A + 2 * η * ‖b‖ + d ^ 2 * A ^ 2 +
        2 * d * η * A + η ^ 2 := by
  calc
    _ ≤ 2 * ‖b‖ * (d * A + η) + (d * A + η) ^ 2 :=
      abs_norm_square_sub_le_of_error z b (d * A + η) (by positivity) herror
    _ = _ := square_error_envelope_expansion ‖b‖ d A η

/-- The sharper pair bound keeps the mixed remainder and uses separate exact
second- and fourth-moment budgets. All arithmetic providers are explicit. -/
theorem square_kernel_weighted_arithmetic_transfer_exact_cross (s : Finset ι)
    (S B : ι → ι → ℂ) (a : ι → ℂ) (A : ι → ι → ℝ)
    (w : ι → ℝ) (d η KA K0 M₂ M₄ : ℝ)
    (hd : 0 ≤ d) (hη : 0 ≤ η)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (hAsym : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i)
    (hBsym : ∀ i ∈ s, ∀ j ∈ s, ‖B i j‖ = ‖B j i‖)
    (hw : ∀ i ∈ s, 0 < w i)
    (herror : ∀ i ∈ s, ∀ j ∈ s, ‖S i j - B i j‖ ≤ d * A i j + η)
    (hrowA : ∀ i ∈ s,
      (∑ j ∈ s, (‖B i j‖ * A i j) * w j) ≤ KA * w i)
    (hrow0 : ∀ i ∈ s, (∑ j ∈ s, ‖B i j‖ * w j) ≤ K0 * w i)
    (hmoment2 : (∑ i ∈ s, ∑ j ∈ s, A i j ^ 2) ≤ M₂)
    (hmoment4 : (∑ i ∈ s, ∑ j ∈ s, A i j ^ 4) ≤ M₄) :
    ‖form s (fun i j => (‖S i j‖ ^ 2 : ℂ)) a -
        form s (fun i j => (‖B i j‖ ^ 2 : ℂ)) a‖ ≤
      (2 * d * KA + 2 * η * K0 + d ^ 2 * Real.sqrt M₄ +
        2 * d * η * Real.sqrt M₂ + η ^ 2 * (s.card : ℝ)) *
          coefficientEnergy s a := by
  let P1 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * (‖B i j‖ * A i j)
  let P0 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * ‖B i j‖
  let P2 : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * A i j ^ 2
  let PX : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ * A i j
  let Pd : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖
  have h1 : P1 ≤ KA * coefficientEnergy s a := by
    apply weighted_symmetric_schur_budget s a (fun i j => ‖B i j‖ * A i j) w KA
    · intro i hi j hj
      exact mul_nonneg (norm_nonneg _) (hA i hi j hj)
    · intro i hi j hj
      rw [hBsym i hi j hj, hAsym i hi j hj]
    · exact hw
    · exact hrowA
  have h0 : P0 ≤ K0 * coefficientEnergy s a :=
    weighted_symmetric_schur_budget s a (fun i j => ‖B i j‖) w K0
      (fun i hi j hj => norm_nonneg _) hBsym hw hrow0
  have h2 : P2 ≤ Real.sqrt M₄ * coefficientEnergy s a := by
    apply weighted_envelope_hilbertSchmidt_bound s a (fun i j => A i j ^ 2) M₄
    · intro i hi j hj
      exact sq_nonneg _
    · simpa only [← pow_mul] using hmoment4
  have hX : PX ≤ Real.sqrt M₂ * coefficientEnergy s a :=
    weighted_envelope_hilbertSchmidt_bound s a A M₂ hA hmoment2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hdense : Pd ≤ (s.card : ℝ) * coefficientEnergy s a := by
    dsimp [Pd]
    calc
      _ = (∑ i ∈ s, ‖a i‖) ^ 2 := by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ _ := hcs
  have hnorm :
      ‖form s (fun i j => (‖S i j‖ ^ 2 : ℂ)) a -
          form s (fun i j => (‖B i j‖ ^ 2 : ℂ)) a‖ ≤
        2 * d * P1 + 2 * η * P0 + d ^ 2 * P2 + 2 * d * η * PX + η ^ 2 * Pd := by
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ *
          ‖(‖S i j‖ ^ 2 : ℂ) - (‖B i j‖ ^ 2 : ℂ)‖ :=
        form_comparison_weighted s _ _ a
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ *
          (2 * d * ‖B i j‖ * A i j + 2 * η * ‖B i j‖ +
            d ^ 2 * A i j ^ 2 + 2 * d * η * A i j + η ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [← Complex.ofReal_pow, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs] using
          square_error_nonnegative_envelope_exact_cross (S i j) (B i j) d (A i j) η
            hd (hA i hi j hj) hη (herror i hi j hj)
      _ = _ := by
        dsimp [P1, P0, P2, PX, Pd]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  calc
    _ ≤ 2 * d * P1 + 2 * η * P0 + d ^ 2 * P2 + 2 * d * η * PX + η ^ 2 * Pd := hnorm
    _ ≤ 2 * d * (KA * coefficientEnergy s a) +
        2 * η * (K0 * coefficientEnergy s a) +
        d ^ 2 * (Real.sqrt M₄ * coefficientEnergy s a) +
        2 * d * η * (Real.sqrt M₂ * coefficientEnergy s a) +
        η ^ 2 * ((s.card : ℝ) * coefficientEnergy s a) := by
      exact add_le_add (add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h0 (by positivity)))
        (mul_le_mul_of_nonneg_left h2 (by positivity)))
        (mul_le_mul_of_nonneg_left hX (by positivity)))
        (mul_le_mul_of_nonneg_left hdense (by positivity))
    _ = _ := by ring

end RiemannResearch.Analysis.ZeroSamplingQuadratic
