import RiemannResearch.RH.MultiRangeRationalCertificates
import RiemannResearch.RH.MultiRangeOptimizerConvergence

/-! Exact rational inverse-Gram coefficients and finite certificates.
These identities apply even before nondegeneracy is invoked; when the
truncated Gram matrix is positive definite the coefficients are its unique
optimizer. No numerical matrix approximation enters these equalities. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative Probability.ConditionalIID Analysis.Cesaro

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rational matrix inversion agrees exactly with real matrix inversion. -/
theorem rationalMatrixInverse_cast (M : Matrix ι ι ℚ) :
    (Rat.castHom ℝ).mapMatrix M⁻¹ = ((Rat.castHom ℝ).mapMatrix M)⁻¹ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  ext i j
  change (((M.det)⁻¹ * M.adjugate i j : ℚ) : ℝ) =
    (((Rat.castHom ℝ).mapMatrix M).det)⁻¹ *
      ((Rat.castHom ℝ).mapMatrix M).adjugate i j
  rw [Rat.cast_mul, Rat.cast_inv]
  have hd : (M.det : ℝ) = ((Rat.castHom ℝ).mapMatrix M).det :=
    (Rat.castHom ℝ).map_det M
  have ha : (M.adjugate i j : ℝ) = ((Rat.castHom ℝ).mapMatrix M).adjugate i j :=
    congrArg (fun Q : Matrix ι ι ℝ => Q i j) ((Rat.castHom ℝ).map_adjugate M)
  rw [hd, ha]

def rationalPrefixGram (U : ι → ℕ → ℚ) (N : ℕ) : Matrix ι ι ℚ :=
  fun i j => rationalPrefixPairing (U i) (U j) N

def rationalPrefixOptimizer (F : ℕ → ℚ) (U : ι → ℕ → ℚ) (N : ℕ) (i : ι) : ℚ :=
  -(∑ j, (rationalPrefixGram U N)⁻¹ i j * rationalPrefixPairing F (U j) N)

@[simp] theorem rationalPrefixGram_cast (U : ι → ℕ → ℚ) (N : ℕ) :
    (Rat.castHom ℝ).mapMatrix (rationalPrefixGram U N) =
      prefixMeanGram (fun i n => (U i n : ℝ)) N := by
  ext i j
  exact rationalPrefixPairing_cast (U i) (U j) N

@[simp] theorem rationalPrefixOptimizer_cast (F : ℕ → ℚ) (U : ι → ℕ → ℚ)
    (N : ℕ) (i : ι) :
    (rationalPrefixOptimizer F U N i : ℝ) =
      prefixMeanOptimizer (fun n => (F n : ℝ)) (fun j n => (U j n : ℝ)) N i := by
  have hi := rationalMatrixInverse_cast (rationalPrefixGram U N)
  rw [rationalPrefixGram_cast] at hi
  have hij (j : ι) : ((rationalPrefixGram U N)⁻¹ i j : ℝ) =
      (prefixMeanGram (fun k n => (U k n : ℝ)) N)⁻¹ i j :=
    congrArg (fun Q : Matrix ι ι ℝ => Q i j) hi
  simp only [rationalPrefixOptimizer, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul,
    hij, rationalPrefixPairing_cast, prefixMeanOptimizer, conditionalMeanPrefixInner]

/-- All finite divisor-family minimizing coefficients are rational. -/
theorem anchorPrefixOptimizer_rational {D : ℕ} (Y N : ℕ) (d : Fin D → ℕ) :
    ∃ q : Fin D → ℚ, ∀ i, (q i : ℝ) =
      prefixMeanOptimizer (canonicalMobiusHead Y)
        (fun j => divisorAnchorDirection (Y+1) (d j)) N i := by
  refine ⟨rationalPrefixOptimizer (rationalCanonicalMobiusHead Y)
    (fun j => rationalDivisorAnchor (Y+1) (d j)) N, ?_⟩
  intro i
  simpa only [rationalCanonicalMobiusHead_cast, rationalDivisorAnchor_cast] using
    rationalPrefixOptimizer_cast (rationalCanonicalMobiusHead Y)
      (fun j => rationalDivisorAnchor (Y+1) (d j)) N i

/-- Rational candidate energies have rational upper bounds with any rational
certified mean bound. The cast is equality, not floating-point approximation. -/
def rationalUpperCertificate (F : ℕ → ℚ) (L : ℚ) (N : ℕ) : ℚ :=
  rationalPrefixEnergy F N + 2 / ((N : ℚ)+2)*L^2

@[simp] theorem rationalUpperCertificate_cast (F : ℕ → ℚ) (L : ℚ) (N : ℕ) :
    (rationalUpperCertificate F L N : ℝ) =
      conditionalMeanUpperCertificate (fun n => (F n : ℝ)) (L : ℝ) N := by
  simp [rationalUpperCertificate, conditionalMeanUpperCertificate]

end RiemannResearch.RH.Pareto
