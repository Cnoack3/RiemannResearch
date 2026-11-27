/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryThreePrimeFMZResidual
import RiemannResearch.Analysis.MontgomeryNonconstantHaarCriterion
import RiemannResearch.Analysis.MontgomeryRationalHaarEnvelope

/-! # Physical ordinary PCC as a signed series of actual FMZ remainders

The three-prime mesh uses only mixed noncentral modes, so after deletion
of the asymptotically negligible central cell its entire ordinate-square
energy is a weighted sum of squared actual FMZ remainders. The collision
subtraction remains at the full occurrence multiplicity. The sine-law
limit on this moving height-normalized series is an arithmetic obligation.
-/

noncomputable section
open Filter MeasureTheory
open scoped FourierTransform Topology ContDiff

namespace RiemannResearch.Analysis.RoundedFourierCellParseval
open MontgomeryAllPairWordRounding MontgomeryPositiveGap MontgomeryEvenFourierTests
open ActualInfinitePrimeTorus ActualZeroOrdinate OrdinateCollisionCertificate

/-- Signed noncentral cells weighted by the squares of their actual FMZ
remainders, followed by the complete forward-atom correction. -/
def noncentralFMZStatistic (p q r : Nat.Primes) (a b : ℤ) (T : ℝ)
    (w : ℝ → ℝ) (f₀ : ℝ) : ℝ :=
  let h := meshFrequency p q r a b
  ((∑' k : ℤ, if k = 0 then 0 else cellMass (roundedOrder T h) w k *
      (T^2 * ‖wordRemainder T (ratioWord p q (k*a) ++ ratioWord q r (k*b))‖^2)) -
    (occurrenceCollision (copyOrdinate T) : ℝ) * f₀) /
      (2 * (T * Real.log T / (2 * Real.pi)))

/-- This identification of the signed noncentral series is exact at each
positive height, independently of the size of the three-prime integer orders. -/
theorem nonconstantHaarStatistic_eq_noncentralFMZStatistic {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) {a b : ℤ}
    (hh : meshFrequency p q r a b ≠ 0) {T : ℝ} (hT : T ≠ 0)
    (w : ℝ → ℝ) (f₀ : ℝ) :
    nonconstantHaarStatistic T (meshFrequency p q r a b) w f₀ =
      noncentralFMZStatistic p q r a b T w f₀ := by
  unfold nonconstantHaarStatistic noncentralFMZStatistic
  congr 2
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simp only [meshFrequency, threePrimeMesh_ordinateSum_norm_sq hpq hqr hh hT, if_neg hk]

/-- One common height-dependent mesh of primes 2, 3 and 5 works
simultaneously for every even smooth compactly supported physical test. -/
theorem exists_two_three_five_noncentralFMZ_pcc_criterion :
    let p : Nat.Primes := ⟨2, by decide⟩
    let q : Nat.Primes := ⟨3, by decide⟩
    let r : Nat.Primes := ⟨5, by decide⟩
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q r (a T) (b T) ∧
        meshFrequency p q r (a T) (b T) < 1 / T^3) ∧
      (PositiveGapPCC ↔ ∀ f : ℝ → ℝ, HasCompactSupport f → ContDiff ℝ ∞ f →
        (∀ x, f (-x) = f x) → ∀ R : ℝ, 0 < R → (∀ x, R ≤ |x| → f x = 0) →
        Tendsto (fun T => noncentralFMZStatistic p q r (a T) (b T) T
          (fun v => (𝓕 (fun x => (f x : ℂ)) v).re) (f 0)) atTop
          (𝓝 (∫ x in (0:ℝ)..R, f x * (1 - Real.sinc (Real.pi*x)^2)))) := by
  dsimp only
  obtain ⟨a, b, hmesh, hcriterion⟩ := exists_two_three_five_nonconstantHaar_pcc_criterion
  refine ⟨a, b, hmesh, hcriterion.trans ?_⟩
  have he (w : ℝ → ℝ) (f₀ : ℝ) :
      ∀ᶠ T in atTop,
        nonconstantHaarStatistic T (meshFrequency ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩
          (a T) (b T)) w f₀ =
        noncentralFMZStatistic ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩
          (a T) (b T) T w f₀ := by
    filter_upwards [hmesh, eventually_gt_atTop (0:ℝ)] with T hh ht
    exact nonconstantHaarStatistic_eq_noncentralFMZStatistic (by decide) (by decide)
      hh.1.ne' ht.ne' w f₀
  constructor
  · intro H f hc hs heven R hR hcut
    exact (H f hc hs heven R hR hcut).congr' (he _ _)
  · intro H f hc hs heven R hR hcut
    exact (H f hc hs heven R hR hcut).congr' ((he _ _).mono fun _ h => h.symm)


/-- A countable family suffices: the single smooth plateau for each rational
pair of positive radii. Bounds permit arbitrarily small fixed slack. -/
theorem exists_two_three_five_rational_noncentralFMZ_envelopes :
    let p : Nat.Primes := ⟨2, by decide⟩
    let q : Nat.Primes := ⟨3, by decide⟩
    let z : Nat.Primes := ⟨5, by decide⟩
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q z (a T) (b T) ∧
        meshFrequency p q z (a T) (b T) < 1 / T^3) ∧
      (PositiveGapPCC ↔ ∀ r s : ℚ, ∀ hr : 0 < r, ∀ hrs : r < s, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ T in atTop,
          sineGapMass r - ε ≤ noncentralFMZStatistic p q z (a T) (b T) T
            (rationalPlateauWeight r s hr hrs) 1 ∧
          noncentralFMZStatistic p q z (a T) (b T) T (rationalPlateauWeight r s hr hrs) 1 ≤
            sineGapMass s + ε) := by
  dsimp only
  obtain ⟨a, b, hm, hcrit⟩ := exists_two_three_five_rational_signedHaar_envelopes
  refine ⟨a, b, hm, hcrit.trans ?_⟩
  let h (T : ℝ) := meshFrequency ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩ (a T) (b T)
  have heq (r s : ℚ) (hr : 0 < r) (hrs : r < s) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ T in atTop,
      |signedHaarStatistic T (h T) (rationalPlateauWeight r s hr hrs) 1 -
        noncentralFMZStatistic ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩ (a T) (b T) T
          (rationalPlateauWeight r s hr hrs) 1| < ε := by
    let w := rationalPlateauWeight r s hr hrs
    have hb (v : ℝ) : |w v| ≤ ∫ x, ‖(rationalPlateau r s hr hrs x : ℂ)‖ :=
      abs_re_fourier_le_integral_norm (rationalPlateau r s hr hrs) v
    have hz := centralWordContribution_tendsto_zero
      (h := h) (hm.mono (fun T ht => ⟨ht.1, ht.2.le⟩)) w hb
    have hsmall := Metric.tendsto_nhds.mp hz ε hε
    filter_upwards [hsmall, hm, eventually_gt_atTop (0:ℝ)] with T hbound ht hT
    change |signedHaarStatistic T (h T) w 1 - _| < ε
    rw [← nonconstantHaarStatistic_eq_noncentralFMZStatistic (by decide) (by decide)
      ht.1.ne' hT.ne' w 1, nonconstantHaarStatistic_eq_sub T _ (rationalPlateauWeight_integral
        r s hr hrs).1]
    change |signedHaarStatistic T (h T) w 1 -
      (signedHaarStatistic T (h T) w 1 - centralWordContribution T (h T) w)| < ε
    simpa only [sub_sub_cancel, Real.dist_eq, sub_zero] using hbound
  constructor
  · intro H r s hr hrs ε hε
    filter_upwards [H r s hr hrs (ε/2) (half_pos hε), heq r s hr hrs (ε/2) (half_pos hε)]
      with T H₁ H₂
    have hu := abs_lt.mp H₂
    dsimp only [h] at hu
    constructor <;> linarith only [H₁.1, H₁.2, hu.1, hu.2]
  · intro H r s hr hrs ε hε
    filter_upwards [H r s hr hrs (ε/2) (half_pos hε), heq r s hr hrs (ε/2) (half_pos hε)]
      with T H₁ H₂
    have hu := abs_lt.mp H₂
    dsimp only [h] at hu
    constructor <;> linarith only [H₁.1, H₁.2, hu.1, hu.2]

end RiemannResearch.Analysis.RoundedFourierCellParseval
