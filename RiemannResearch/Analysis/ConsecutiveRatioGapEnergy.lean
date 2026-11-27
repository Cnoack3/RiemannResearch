import RiemannResearch.Analysis.ConsecutiveRatioCovariance

/-! # Uniform centered reconstruction over all consecutive prime triples

Each member of a family of microscopic Fourier tests may choose its own
consecutive prime triple. The backward ratio words use the negatives of the
rounded orders in the forward convention for the empirical gap transform.
After equal characters are grouped, Parseval controls the whole reconstruction
error by the squared coefficients with a constant independent of the triples.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate CompactCharacter CompactGaugeOrbitLaw
local instance ratioGapEnergyTorusMeasurable : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance ratioGapEnergyTorusBorel : BorelSpace PrimeTorus := ⟨rfl⟩
local instance ratioGapEnergyPairMeasurable : MeasurableSpace (PrimeTorus × PrimeTorus) := borel _
local instance ratioGapEnergyPairBorel : BorelSpace (PrimeTorus × PrimeTorus) := ⟨rfl⟩

def roundedRatioWord (T : ℝ) (n : ℕ) (ξ η : ℝ) : RatioWord :=
  let scale := Real.log T / (2 * Real.pi)
  [(n, -roundedOrder (logPrimeStep (orderedPrime n) (orderedPrime (n+1))) (ξ*scale)),
   (n+1, -roundedOrder (logPrimeStep (orderedPrime (n+1)) (orderedPrime (n+2))) (η*scale))]

def ratioGapError (T : ℝ) (n : ℕ) (ξ η : ℝ) : ℂ :=
  roundedThreePrimeSample T (orderedPrime n) (orderedPrime (n+1)) (orderedPrime (n+2)) ξ η -
    unfoldedAdjacentGapTransform T ξ η

theorem roundedRatioWord_frequency (T : ℝ) (n : ℕ) (ξ η : ℝ) :
    let u := logPrimeStep (orderedPrime n) (orderedPrime (n+1))
    let v := logPrimeStep (orderedPrime (n+1)) (orderedPrime (n+2))
    let scale := Real.log T / (2*Real.pi)
    ratioFrequency (roundedRatioWord T n ξ η) =
      (roundedOrder u (ξ*scale) : ℝ)*u + (roundedOrder v (η*scale) : ℝ)*v := by
  simp [ratioFrequency, roundedRatioWord, pullRatioWord, wordFrequency, logPrimeStep]
  ring

theorem ratioGapError_le {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (ξ η : ℝ) :
    ‖ratioGapError T n ξ η‖ ≤ Real.log 2 * (T / (Ncount 0 T : ℝ)) :=
  roundedThreePrimeSample_error_consecutive hT (orderedPrime_next n) (orderedPrime_next (n+1)) ξ η

theorem centered_all_triples_gap_parseval {ι : Type*} {T : ℝ} (hT : 0 ≤ T)
    (n : ι → ℕ) (ξ η : ι → ℝ) (a g : ι → ℂ) (hg : ∀ i, ‖g i‖ = 1)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) :
    let w := fun i => roundedRatioWord T (n i) (ξ i) (η i)
    let e := fun i => ratioGapError T (n i) (ξ i) (η i)
    let b := fun i => if ratioFrequency (w i) = 0 then (0:ℂ) else g i * (a i * e i)
    Function.Injective (fun i => wordExponents (w i)) →
      Summable (fun i => b i • pairWordL2 (pullRatioWord (w i)) []) ∧
      ‖∑' i, b i • pairWordL2 (pullRatioWord (w i)) []‖ ^ 2 =
        (∑' i, if ratioFrequency (w i) = 0 then (0 : ℝ) else ‖a i * e i‖ ^ 2) ∧
      ‖∑' i, b i • pairWordL2 (pullRatioWord (w i)) []‖ ^ 2 ≤
        (Real.log 2 * (T / (Ncount 0 T : ℝ))) ^ 2 * ∑' i, ‖a i‖ ^ 2 := by
  intro w e b hinj
  let B := Real.log 2 * (T / (Ncount 0 T : ℝ))
  have he (i : ι) : ‖a i * e i‖ ^ 2 ≤ B ^ 2 * ‖a i‖ ^ 2 := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left (ratioGapError_le hT (n i) (ξ i) (η i)) (norm_nonneg (a i))
    exact (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h 2).trans_eq (by
      dsimp only [B]; ring)
  have hmaj := ha.mul_left (B ^ 2)
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) he hmaj
  obtain ⟨hseries, hnorm⟩ :=
    centered_ratio_gauge_parseval w hinj (fun i => a i * e i) g hg hs 1
  simp only [Complex.ofReal_one, one_mul, one_pow] at hseries hnorm
  refine ⟨hseries, hnorm, hnorm.trans_le ?_⟩
  have ht (i : ι) :
      (if ratioFrequency (w i) = 0 then (0:ℝ) else ‖a i * e i‖ ^ 2) ≤ B ^ 2 * ‖a i‖ ^ 2 := by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact he i
  have hsum := Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity) ht hmaj
  exact (hsum.tsum_le_tsum ht hmaj).trans_eq (tsum_mul_left ..)

theorem centered_gap_error_bound_tendsto_zero (energy : ℝ) :
    Tendsto (fun T : ℝ => (Real.log 2 * (T / (Ncount 0 T : ℝ))) ^ 2 * energy) atTop (𝓝 0) := by
  simpa using ((tendsto_height_div_zero_count.const_mul (Real.log 2)).pow 2).mul_const energy

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
