import RiemannResearch.Analysis.MontgomerySignedHaarCriterion
import RiemannResearch.Analysis.MontgomeryRationalPlateau

/-! # Countably many signed Haar tests for the complete positive-gap law

The Fourier weight has total integral one because each physical plateau
equals one at zero. Every test therefore subtracts the same full
equal-ordinate atom before normalization.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology FourierTransform
namespace RiemannResearch.Analysis.RoundedFourierCellParseval
open MontgomeryAllPairWordRounding MontgomeryPositiveGap MontgomeryEvenFourierTests

theorem rationalPlateauWeight_integral (r s : ℚ) (hr : 0 < r) (hrs : r < s) :
    Integrable (rationalPlateauWeight r s hr hrs) ∧
    (∫ v, rationalPlateauWeight r s hr hrs v) = 1 := by
  let g := rationalPlateau r s hr hrs
  obtain ⟨hw,hzero⟩ := compact_smooth_even_fourier_test g g.hasCompactSupport g.contDiff g.neg
  have hg : g (0:ℝ) = 1 := g.one_of_mem_closedBall (by simp [g.rIn_pos.le])
  refine ⟨hw, ?_⟩
  simpa only [mul_zero, zero_mul, Real.cos_zero, mul_one, hg, g, rationalPlateauWeight] using
    (hzero 1 0).symm

theorem exists_two_three_five_rational_signedHaar_envelopes :
    let p : Nat.Primes := ⟨2, by decide⟩
    let q : Nat.Primes := ⟨3, by decide⟩
    let z : Nat.Primes := ⟨5, by decide⟩
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q z (a T) (b T) ∧
        meshFrequency p q z (a T) (b T) < 1 / T^3) ∧
      (PositiveGapPCC ↔ ∀ r s : ℚ, ∀ hr : 0 < r, ∀ hrs : r < s, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ T in atTop,
          sineGapMass r - ε ≤ signedHaarStatistic T (meshFrequency p q z (a T) (b T))
            (rationalPlateauWeight r s hr hrs) 1 ∧
          signedHaarStatistic T (meshFrequency p q z (a T) (b T)) (rationalPlateauWeight r s hr hrs) 1 ≤
            sineGapMass s + ε) := by
  dsimp only
  obtain ⟨a, b, hm, hcrit⟩ := exists_two_three_five_rational_plateau_envelopes
  refine ⟨a, b, hm, hcrit.trans ?_⟩
  have heq (T h : ℝ) (r s : ℚ) (hr : 0 < r) (hrs : r < s) :
      roundedFourierTest T h (rationalPlateauWeight r s hr hrs) =
      signedHaarStatistic T h (rationalPlateauWeight r s hr hrs) 1 :=
    roundedFourierTest_eq_signedHaarStatistic T h
      (rationalPlateauWeight_integral r s hr hrs).1 (rationalPlateauWeight_integral r s hr hrs).2.symm
  constructor
  · intro H r s hr hrs ε hε
    apply (H r s hr hrs ε hε).mono
    intro T hT
    have he := (threePrimeFourierTest_eq_rounded
      (⟨2, by decide⟩ : Nat.Primes) ⟨3, by decide⟩ ⟨5, by decide⟩ (a T) (b T) T
        (rationalPlateauWeight r s hr hrs)).trans (heq T _ r s hr hrs)
    exact ⟨le_trans hT.1 he.le, le_trans he.ge hT.2⟩
  · intro H r s hr hrs ε hε
    apply (H r s hr hrs ε hε).mono
    intro T hT
    have he := (threePrimeFourierTest_eq_rounded
      (⟨2, by decide⟩ : Nat.Primes) ⟨3, by decide⟩ ⟨5, by decide⟩ (a T) (b T) T
        (rationalPlateauWeight r s hr hrs)).trans (heq T _ r s hr hrs)
    exact ⟨le_trans hT.1 he.ge, le_trans he.le hT.2⟩

end RiemannResearch.Analysis.RoundedFourierCellParseval
