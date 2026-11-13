import RiemannResearch.NumberTheory.DirichletExponentialMoments
import RiemannResearch.NumberTheory.DirichletExponentialScalarBounds
import RiemannResearch.RH.ParetoDirichletExponentialHilbert
import RiemannResearch.RH.ParetoResidueExponentialFiniteSpan

/-!
# Actual Pareto residue exponentials and their legality

Source: the convolution-exponential argument developed with Christian Noack,
13 November 2026.  The generalized-divisor moment estimate is supplied by a
proved theorem, so the Hilbert membership and unit limit below have no
additional analytic assumptions.  Membership in the closed residue space
remains an explicit hypothesis; on unbounded primes it is equivalent to
full residue density.  The optional RH converse displays the repository's
still-missing RH-to-density input explicitly.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory.DirichletExponential

/-- Every normalized residue is dominated by the positive constant-one input. -/
theorem residueAF_le_zetaReal (k n : ℕ) : residueAF k n ≤ zetaReal n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [zetaReal_apply, if_neg hn]
    exact (le_abs_self _).trans (residueAF_abs_le_one k n)

/-- The constant-input convolution exponential majorizes every residue exponential. -/
theorem residueAF_exp_le_zetaReal_exp (k n : ℕ) :
    convolutionExp (residueAF k) n ≤ convolutionExp zetaReal n :=
  convolutionExp_mono (C := 1) (by norm_num) (residueAF_nonneg k)
    (residueAF_le_zetaReal k) zetaReal_abs_le_one n

/-- Every bounded arithmetic input inherits the factorial second-moment bound. -/
theorem bounded_power_square_summable_and_bound
    (f : ArithmeticFunction ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C) (r : ℕ) :
    Summable (fun n => ((f ^ r) n) ^ 2 / (n : ℝ) ^ 2) ∧
      (∑' n, ((f ^ r) n) ^ 2 / (n : ℝ) ^ 2) ≤
        (C ^ 2 * (12 * Real.exp 2)) ^ r * (r.factorial : ℝ) := by
  obtain ⟨hsζ, hbζ⟩ := zetaReal_pow_square_summable_and_bound r
  have hterm (n : ℕ) : ((f ^ r) n) ^ 2 / (n : ℝ) ^ 2 ≤
      C ^ (2 * r) * (((zetaReal ^ r) n) ^ 2 / (n : ℝ) ^ 2) := by
    have hz := convolutionPower_nonneg zetaReal zetaReal_nonneg r n
    have hp := convolutionPower_abs_le_zetaReal f hC hf r n
    have hsq : ((f ^ r) n) ^ 2 ≤ (C ^ r * (zetaReal ^ r) n) ^ 2 := by
      have h := mul_le_mul hp hp (abs_nonneg _) (mul_nonneg (pow_nonneg hC r) hz)
      simpa only [← pow_two, sq_abs] using h
    calc
      ((f ^ r) n) ^ 2 / (n : ℝ) ^ 2 ≤
          (C ^ r * (zetaReal ^ r) n) ^ 2 / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hsq (sq_nonneg _)
      _ = C ^ (2 * r) * (((zetaReal ^ r) n) ^ 2 / (n : ℝ) ^ 2) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm r 2]
        ring
  have hdom := hsζ.mul_left (C ^ (2 * r))
  have hs : Summable (fun n => ((f ^ r) n) ^ 2 / (n : ℝ) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (sq_nonneg _) (sq_nonneg _))
      hterm hdom
  refine ⟨hs, ?_⟩
  calc
    (∑' n, ((f ^ r) n) ^ 2 / (n : ℝ) ^ 2) ≤
        ∑' n, C ^ (2 * r) * (((zetaReal ^ r) n) ^ 2 / (n : ℝ) ^ 2) :=
      hs.tsum_le_tsum hterm hdom
    _ = C ^ (2 * r) * (∑' n, ((zetaReal ^ r) n) ^ 2 / (n : ℝ) ^ 2) := by rw [tsum_mul_left]
    _ ≤ C ^ (2 * r) * ((12 * Real.exp 2) ^ r * (r.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hbζ (pow_nonneg hC _)
    _ = (C ^ 2 * (12 * Real.exp 2)) ^ r * (r.factorial : ℝ) := by
      simp only [mul_pow, ← pow_mul]
      ring

end RiemannResearch.NumberTheory.DirichletExponential

namespace RiemannResearch.RH.Pareto.ConvolutionExponential

open RiemannResearch.NumberTheory.DirichletExponential
open CoefficientStabilization

/-- Every bounded arithmetic input has its actual convolution exponential in H. -/
theorem bounded_convolutionExp_square_summable (f : ArithmeticFunction ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) :
    Summable (fun n => positiveWeight n * convolutionExp f n ^ 2) := by
  apply convolutionExp_square_summable_of_inv_sq_power_moments f
    (fun r => (bounded_power_square_summable_and_bound f hC hf r).1)
    (A := C ^ 2 * (12 * Real.exp 2)) (by positivity)
  intro r
  exact (bounded_power_square_summable_and_bound f hC hf r).2

/-- The genuine Hilbert Taylor series is absolutely convergent for every
bounded arithmetic input. -/
theorem bounded_convolutionExp_norm_summable (f : ArithmeticFunction ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) :
    Summable (fun r : ℕ =>
      ‖(1 / (r.factorial : ℝ)) • powerHilbert f r
        (weighted_square_summable_of_inv_sq _
          (bounded_power_square_summable_and_bound f hC hf r).1)‖) := by
  apply powerHilbert_exp_norm_summable f _
    (A := C ^ 2 * (12 * Real.exp 2)) (by positivity)
  intro r
  exact (weighted_square_tsum_le_inv_sq _
    (bounded_power_square_summable_and_bound f hC hf r).1).trans
    (bounded_power_square_summable_and_bound f hC hf r).2

/-- The common envelope exp⋆(1) has finite complete Pareto energy. -/
theorem zetaReal_exp_square_summable :
    Summable (fun n => positiveWeight n * convolutionExp zetaReal n ^ 2) :=
  bounded_convolutionExp_square_summable zetaReal (C := 1)
    (by norm_num) zetaReal_abs_le_one

/-- Every actual residue exponential has finite Pareto energy, unconditionally. -/
theorem residue_exp_square_summable (k : ℕ) :
    Summable (fun n => positiveWeight n * convolutionExp (residueAF k) n ^ 2) :=
  bounded_convolutionExp_square_summable (residueAF k) (C := 1)
    (by norm_num) (residueAF_abs_le_one k)

/-- The actual, unconditionally defined residue convolution exponential in H. -/
def residueExponential (k : ℕ) : ThresholdHilbert :=
  residueExpHilbert k (residue_exp_square_summable k)

@[simp] theorem residueExponential_sequence (k : ℕ) :
    hilbertSequence (residueExponential k) = convolutionExp (residueAF k) :=
  residueExpHilbert_sequence _ _

/-- The genuine residue exponentials converge in H to the Dirichlet unit. -/
theorem residueExponential_tendsto_unit :
    Tendsto residueExponential atTop (𝓝 (paretoPointHilbert 0)) := by
  exact residueExpHilbert_tendsto_unit zetaReal_exp_square_summable
    residueAF_exp_le_zetaReal_exp

/-- At a prime conductor the exponential is not an exact finite residue sum. -/
theorem residueExponential_not_mem_atomSpan {p : ℕ} (hp : p.Prime) :
    residueExponential p ∉ Submodule.span ℝ (Set.range residueAtom) :=
  not_mem_atomSpan_of_sequence_eq_residueExp hp (residueExponential_sequence p)

/-- Legality on unbounded primes is equivalent to actual Pareto residue density. -/
theorem residueExponential_unbounded_prime_legality_iff_density :
    UnboundedPrimeLegality residueExponential ↔ closedSpace = ⊤ :=
  unbounded_prime_legality_iff_closedSpace_eq_top _ residueExponential_tendsto_unit

/-- Actual exponential legality on arbitrarily large primes implies Mathlib RH. -/
theorem riemannHypothesis_of_residueExponential_unbounded_prime_legality
    (hlegal : UnboundedPrimeLegality residueExponential) : RiemannHypothesis :=
  riemannHypothesis_of_unbounded_prime_legality _ residueExponential_tendsto_unit hlegal

/-- The classical reverse approximation input remains visible in the type. -/
theorem residueExponential_unbounded_prime_legality_iff_riemannHypothesis
    (hDensity : RiemannHypothesis → closedSpace = ⊤) :
    UnboundedPrimeLegality residueExponential ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_residueExponential_unbounded_prime_legality
  · intro hRH
    exact residueExponential_unbounded_prime_legality_iff_density.mpr (hDensity hRH)

end RiemannResearch.RH.Pareto.ConvolutionExponential
