import RiemannResearch.Analysis.ActualDirichletPolynomialGram
import RiemannResearch.Analysis.DirichletMeanSquare
import RiemannResearch.Analysis.RationalFrequencyHeightSeparation

/-!
Exact bridge from actual Dirichlet polynomials and multiplicity-weighted
zeta-zero samples to their aggregated rational-frequency polynomials.
The centered subtype is directly usable by the integrated-discrepancy and
fourth-frequency-energy estimates. No analytic provider is needed for these
finite identities.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Analysis.ActualRationalAutocorrelation
open RiemannResearch.Fourier ZeroOrdinate

/-- The actual distinct nonconstant rational frequencies of an integer support. -/
abbrev OffDiagonalRatios (s : Finset ℕ) :=
  {q : ℚ // q ∈ (rationalFrequencySupport s).erase 1}

def centeredCoefficient (s : Finset ℕ) (a : ℕ → ℂ) (q : OffDiagonalRatios s) : ℂ :=
  rationalAutocorrelation s a q.1

def centeredFrequency (s : Finset ℕ) (q : OffDiagonalRatios s) : ℝ :=
  Real.log (q.1 : ℝ)

def centeredPolynomial (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  DirichletMeanSquare.polynomial (centeredCoefficient s a) (centeredFrequency s) t

private theorem norm_sq_eq_star_mul (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  simpa only [Complex.star_def, mul_comm, Complex.ofReal_pow] using (Complex.mul_conj' z).symm

/-- Exact pointwise Fourier expansion, combining equal ratios before any norm. -/
theorem polynomial_norm_sq_eq_rational_sum
    (s : Finset ℕ) (a : ℕ → ℂ) (hs0 : ∀ n ∈ s, 0 < n) (t : ℝ) :
    ((‖ActualDirichletPolynomialGram.polynomial s a t‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ rationalFrequencySupport s,
        rationalAutocorrelation s a q * phase (Real.log (q : ℝ)) t := by
  have hgroup := sum_groupedFrequencyCoefficient_mul (s ×ˢ s)
    (fun p => (p.1 : ℚ) / (p.2 : ℚ)) (fun p => a p.1 * starRingEnd ℂ (a p.2))
    (rationalFrequencySupport s) (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    (fun q => phase (Real.log (q : ℝ)) t)
  calc
    _ = ActualDirichletPolynomialGram.polynomial s a t *
        star (ActualDirichletPolynomialGram.polynomial s a t) := by
      rw [norm_sq_eq_star_mul, mul_comm]
    _ = ∑ n ∈ s, ∑ m ∈ s, (a n * starRingEnd ℂ (a m)) *
        phase (Real.log n - Real.log m) t := by
      simp only [ActualDirichletPolynomialGram.polynomial, star_sum, star_mul,
        Finset.sum_mul_sum, phase_sub, starRingEnd_apply]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = ∑ p ∈ s ×ˢ s, (a p.1 * starRingEnd ℂ (a p.2)) *
        phase (Real.log (((p.1 : ℚ) / (p.2 : ℚ) : ℚ) : ℝ)) t := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (hs0 n hn))
      have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (hs0 m hm))
      simp only [Rat.cast_div, Rat.cast_natCast, Real.log_div hn0 hm0]
    _ = _ := hgroup.symm

/-- The finite-type polynomial is literally the off-diagonal rational sum. -/
theorem centeredPolynomial_eq_sum (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    centeredPolynomial s a t =
      ∑ q ∈ (rationalFrequencySupport s).erase 1,
        rationalAutocorrelation s a q * phase (Real.log (q : ℝ)) t := by
  unfold centeredPolynomial DirichletMeanSquare.polynomial centeredCoefficient centeredFrequency
  exact Finset.sum_coe_sort ((rationalFrequencySupport s).erase 1)
    (fun q : ℚ => rationalAutocorrelation s a q * phase (Real.log (q : ℝ)) t)

/-- The exact centered test F(t)=|A(t)|²−E used in the S₁ integration identity. -/
theorem centeredPolynomial_eq_norm_sq_sub_energy
    (s : Finset ℕ) (a : ℕ → ℂ) (hs0 : ∀ n ∈ s, 0 < n) (t : ℝ) :
    centeredPolynomial s a t =
      ((‖ActualDirichletPolynomialGram.polynomial s a t‖ ^ 2 : ℝ) : ℂ) -
        ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
  classical
  rw [centeredPolynomial_eq_sum]
  by_cases he : s = ∅
  · simp [he, rationalFrequencySupport, ActualDirichletPolynomialGram.polynomial]
  · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hq : (1 : ℚ) ∈ rationalFrequencySupport s := by
      apply Finset.mem_image.mpr
      refine ⟨(n, n), Finset.mem_product.mpr ⟨hn, hn⟩, ?_⟩
      exact div_self (Nat.cast_ne_zero.mpr (ne_of_gt (hs0 n hn)))
    have hsplit := Finset.sum_erase_add (rationalFrequencySupport s)
      (fun q => rationalAutocorrelation s a q * phase (Real.log (q : ℝ)) t) hq
    simp only [Rat.cast_one, Real.log_one, phase_zero, mul_one] at hsplit
    rw [rationalAutocorrelation_one s a (fun n hn => ne_of_gt (hs0 n hn)),
      ← polynomial_norm_sq_eq_rational_sum s a hs0 t] at hsplit
    exact eq_sub_of_add_eq hsplit

/-- The actual sampled square is the multiplicity-weighted sum of norm squares. -/
theorem sampledSquare_eq_actual_norm_sq (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) :
    ActualDirichletPolynomialGram.sampledSquare T s a =
      ActualZeroOrdinate.sum T
        (fun ρ => ((‖ActualDirichletPolynomialGram.polynomial s a ρ.im‖ ^ 2 : ℝ) : ℂ)) := by
  unfold ActualDirichletPolynomialGram.sampledSquare
  simp_rw [norm_sq_eq_star_mul]

/-- Exact actual-zero expansion into aggregated rational ordinate sums. -/
theorem sampledSquare_eq_rational_ordinateSum
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) (hs0 : ∀ n ∈ s, 0 < n) :
    ActualDirichletPolynomialGram.sampledSquare T s a =
      ∑ q ∈ rationalFrequencySupport s,
        rationalAutocorrelation s a q * ActualZeroOrdinate.ordinateSum T (Real.log (q : ℝ)) := by
  rw [sampledSquare_eq_actual_norm_sq]
  simp_rw [polynomial_norm_sq_eq_rational_sum s a hs0]
  simp only [ActualZeroOrdinate.sum, ActualZeroOrdinate.ordinateSum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

/-- Actual centered sampling is Q's unnormalized numerator minus N(T)E. -/
theorem actual_sum_centeredPolynomial
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) (hs0 : ∀ n ∈ s, 0 < n) :
    ActualZeroOrdinate.sum T (fun ρ => centeredPolynomial s a ρ.im) =
      ActualDirichletPolynomialGram.sampledSquare T s a -
        (Zeta23.Ncount 0 T : ℂ) * ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [centeredPolynomial_eq_norm_sq_sub_energy s a hs0]
  rw [ActualZeroOrdinate.sum_sub, ← sampledSquare_eq_actual_norm_sq]
  have hconst := ActualZeroOrdinate.sum_mul_const T (fun _ => 1)
    ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ)
  simpa only [one_mul, ActualZeroOrdinate.sum_one] using
    congrArg (fun z => ActualDirichletPolynomialGram.sampledSquare T s a - z) hconst

/-- There are no positive-height zero copies below height zero. -/
theorem actual_sum_zero_height (f : ℂ → ℂ) : ActualZeroOrdinate.sum 0 f = 0 := by
  unfold ActualZeroOrdinate.sum
  apply Finset.sum_eq_zero
  intro ρ hρ
  have h := ActualZeroOrdinate.mem_cutoff.mp hρ
  exfalso
  linarith [h.2.1, h.2.2]

theorem actual_sum_centeredPolynomial_zero (s : Finset ℕ) (a : ℕ → ℂ) :
    ActualZeroOrdinate.sum 0 (fun ρ => centeredPolynomial s a ρ.im) = 0 :=
  actual_sum_zero_height _

/-- The literal finite-type fourth energy is exactly the paper's actual J₄. -/
theorem centered_fourth_energy_eq (s : Finset ℕ) (a : ℕ → ℂ) :
    (∑ q : OffDiagonalRatios s,
      ‖centeredCoefficient s a q‖ ^ 2 * centeredFrequency s q ^ 4) =
      ∑ q ∈ (rationalFrequencySupport s).erase 1,
        ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 4 := by
  unfold centeredCoefficient centeredFrequency
  exact Finset.sum_coe_sort ((rationalFrequencySupport s).erase 1)
    (fun q : ℚ => ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 4)

/-- The height-only uniform gap is discharged for the exact centered test. -/
theorem centeredFrequency_separation_of_height
    (s : Finset ℕ) (M : ℕ) (hs0 : ∀ n ∈ s, 0 < n) (hsM : ∀ n ∈ s, n ≤ M)
    (q r : OffDiagonalRatios s) (hne : q ≠ r) :
    1 / (M : ℝ) ^ 2 ≤ |centeredFrequency s q - centeredFrequency s r| := by
  apply rationalFrequencySupport_log_separation s M hs0 hsM
    (Finset.mem_of_mem_erase q.2) (Finset.mem_of_mem_erase r.2)
  intro h
  exact hne (Subtype.ext h)

/-- The proved degree-sensitive J₄ budget, directly on the consumer's finite type. -/
theorem centered_fourth_energy_le_degree
    (s : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) (L U : ℝ)
    (hs0 : ∀ n ∈ s, 0 < n) (hsd : ∀ n ∈ s, primeDegree n ≤ d)
    (hu : ∀ n ∈ s, L ≤ Real.log n ∧ Real.log n ≤ U) :
    (∑ q : OffDiagonalRatios s,
      ‖centeredCoefficient s a q‖ ^ 2 * centeredFrequency s q ^ 4) ≤
      (U - L) ^ 4 * (((2 * d).choose d : ℝ) - 1) * (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 := by
  rw [centered_fourth_energy_eq]
  exact boundedPrimeDegree_rationalAutocorrelation_fourth_le s a d L U
    (fun n hn => ne_of_gt (hs0 n hn)) hsd hu

end RiemannResearch.Analysis.ActualRationalAutocorrelation
