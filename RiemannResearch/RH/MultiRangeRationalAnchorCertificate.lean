import RiemannResearch.RH.MultiRangeRationalOptimizer
import RiemannResearch.RH.MultiRangeFiniteMinimum
import RiemannResearch.RH.ConditionalResidueGram

/-! Exact rational certificates for the actual anchored finite optimizer
candidates, including their infinite tails. The coefficients are chosen once
per finite family and truncation, never separately for latent endpoints. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative Probability.ConditionalIID Analysis.Cesaro

def rationalAnchorCandidate {D : ℕ} (Y : ℕ) (d : Fin D → ℕ) (N n : ℕ) : ℚ :=
  rationalCanonicalMobiusHead Y n + ∑ i,
    rationalPrefixOptimizer (rationalCanonicalMobiusHead Y)
      (fun j => rationalDivisorAnchor (Y+1) (d j)) N i *
        rationalDivisorAnchor (Y+1) (d i) n

def rationalAnchorMeanBound {D : ℕ} (Y : ℕ) (d : Fin D → ℕ) (N : ℕ) : ℚ :=
  (Y : ℚ) + ∑ i,
    |rationalPrefixOptimizer (rationalCanonicalMobiusHead Y)
      (fun j => rationalDivisorAnchor (Y+1) (d j)) N i| *
        (((Y+1 : ℕ) : ℚ)/(d i : ℚ)+1)/2

@[simp] theorem rationalAnchorCandidate_cast {D : ℕ} (Y : ℕ) (d : Fin D → ℕ)
    (N n : ℕ) :
    (rationalAnchorCandidate Y d N n : ℝ) = canonicalMobiusHead Y n +
      anchorSynthesis (Y+1) d (prefixMeanOptimizer (canonicalMobiusHead Y)
        (fun j => divisorAnchorDirection (Y+1) (d j)) N) n := by
  simp [rationalAnchorCandidate, anchorSynthesis]

theorem rationalAnchorMeanBound_nonneg {D : ℕ} (Y : ℕ) (d : Fin D → ℕ) (N : ℕ) :
    0 ≤ rationalAnchorMeanBound Y d N := by
  unfold rationalAnchorMeanBound
  apply add_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  positivity

theorem rationalAnchorCandidate_mean_bound {D : ℕ} (Y : ℕ) (hY : 0 < Y)
    (d : Fin D → ℕ) (hd : ∀ i, 0 < d i) (N t : ℕ) :
    |cesaro (fun n => (rationalAnchorCandidate Y d N n : ℝ)) t| ≤
      (rationalAnchorMeanBound Y d N : ℝ) := by
  let x := prefixMeanOptimizer (canonicalMobiusHead Y)
    (fun j => divisorAnchorDirection (Y+1) (d j)) N
  have he : cesaro (fun n => (rationalAnchorCandidate Y d N n : ℝ)) t =
      cesaro (canonicalMobiusHead Y) t +
        ∑ i, x i * cesaro (divisorAnchorDirection (Y+1) (d i)) t := by
    simp only [rationalAnchorCandidate_cast]
    have hh := cesaro_add_mul (canonicalMobiusHead Y) (anchorSynthesis (Y+1) d x) 1 t
    unfold anchorSynthesis at hh
    rw [cesaro_finsetCombination] at hh
    simpa only [one_mul, anchorSynthesis, x] using hh
  rw [he]
  have hb : (rationalAnchorMeanBound Y d N : ℝ) =
      (Y : ℝ) + ∑ i, |x i| * (((Y+1 : ℕ) : ℝ)/(d i : ℝ)+1)/2 := by
    simp [rationalAnchorMeanBound, x]
  rw [hb]
  apply (abs_add_le _ _).trans
  apply add_le_add (canonicalMobiusHead_mean_abs_le Y hY t)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hh := mul_le_mul_of_nonneg_left
    (divisorAnchorDirection_mean_bound (Y+1) (d i) t (by omega) (hd i)) (abs_nonneg (x i))
  simpa only [mul_div_assoc] using hh

/-- Both endpoints are actual rational computations; the upper one bounds the
whole infinite energy, not just the truncated objective. -/
theorem rationalAnchorCandidate_certificate {D : ℕ} (Y : ℕ) (hY : 0 < Y)
    (d : Fin D → ℕ) (hd : ∀ i, Y < d i) (N : ℕ) :
    (rationalPrefixEnergy (rationalAnchorCandidate Y d N) N : ℝ) ≤
      conditionalMeanSquare (fun n => (rationalAnchorCandidate Y d N n : ℝ)) ∧
    conditionalMeanSquare (fun n => (rationalAnchorCandidate Y d N n : ℝ)) ≤
      (rationalUpperCertificate (rationalAnchorCandidate Y d N)
        (rationalAnchorMeanBound Y d N) N : ℝ) := by
  have hlegal : (fun n => (rationalAnchorCandidate Y d N n : ℝ)) ∈
      legalSeedSpan (Set.Ici 1) := by
    simp only [rationalAnchorCandidate_cast]
    exact (anchor_affine_mem_class Y d hd _).1
  rw [rationalPrefixEnergy_cast, rationalUpperCertificate_cast]
  apply conditionalMeanSquare_finite_certificate _ hlegal N _
  · exact_mod_cast rationalAnchorMeanBound_nonneg Y d N
  · intro t _
    exact rationalAnchorCandidate_mean_bound Y hY d
      (fun i => by have := hd i; omega) N t

end RiemannResearch.RH.Pareto
