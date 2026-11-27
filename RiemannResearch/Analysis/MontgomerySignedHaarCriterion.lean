import RiemannResearch.Analysis.RoundedFourierCellParseval
import RiemannResearch.Analysis.MontgomeryThreePrimePCC

/-! # A signed Haar Parseval criterion for ordinary positive-gap PCC

Section 4 of the supplied Mellin–prime orbit handoff yields a common
two-three-five rounding mesh for every test. On its integer frequency cells,
Parseval gives the two norms below. The forward atom is subtracted with
its full occurrence multiplicity and the value of the test at zero.
-/

noncomputable section
open Filter MeasureTheory
open scoped FourierTransform Topology ContDiff
namespace RiemannResearch.Analysis.RoundedFourierCellParseval
open MontgomeryAllPairWordRounding MontgomeryPositiveGap MontgomeryEvenFourierTests
open ActualZeroOrdinate OrdinateCollisionCertificate

/-- The signed cell energy of the actual zero Fourier sums, with the forward
atom subtracted and the physical pair-correlation normalization. -/
def signedHaarStatistic (T h : ℝ) (w : ℝ → ℝ) (f₀ : ℝ) : ℝ :=
  let b := cellMass (roundedOrder T h) w
  let A := fun k : ℤ => ordinateSum T ((k : ℝ) * h)
  (‖cellWave b A‖ ^ 2 - ‖cellWave (fun k => -b k) A‖ ^ 2 -
    (occurrenceCollision (copyOrdinate T) : ℝ) * f₀) /
    (2 * (T * Real.log T / (2 * Real.pi)))

/-- Exact equality for any integrable weight whose integral is the assigned
zero-frequency test value. -/
theorem roundedFourierTest_eq_signedHaarStatistic (T h : ℝ) {w : ℝ → ℝ}
    (hw : Integrable w) {f₀ : ℝ} (h₀ : f₀ = ∫ v, w v) :
    roundedFourierTest T h w = signedHaarStatistic T h w f₀ := by
  subst f₀
  exact congrArg (fun e : ℝ => e / (2 * (T * Real.log T / (2 * Real.pi))))
    (actual_rounded_signed_parseval T h hw)

/-- For one common choice of prime words at each height, ordinary PCC is
equivalent to the signed Haar statistic having the sine-law limit for all
even smooth compactly supported tests. The arithmetic limits are explicit
open hypotheses in the reverse implication. -/
theorem exists_two_three_five_signedHaar_pcc_criterion :
    let p : Nat.Primes := ⟨2, by decide⟩
    let q : Nat.Primes := ⟨3, by decide⟩
    let r : Nat.Primes := ⟨5, by decide⟩
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q r (a T) (b T) ∧
        meshFrequency p q r (a T) (b T) < 1 / T^3) ∧
      (PositiveGapPCC ↔ ∀ f : ℝ → ℝ, HasCompactSupport f → ContDiff ℝ ∞ f →
        (∀ x, f (-x) = f x) → ∀ R : ℝ, 0 < R → (∀ x, R ≤ |x| → f x = 0) →
        Tendsto (fun T => signedHaarStatistic T (meshFrequency p q r (a T) (b T))
          (fun v => (𝓕 (fun x => (f x : ℂ)) v).re) (f 0)) atTop
          (𝓝 (∫ x in (0:ℝ)..R, f x * (1 - Real.sinc (Real.pi*x)^2)))) := by
  dsimp only
  obtain ⟨a, b, hmesh, hcriterion⟩ := exists_two_three_five_pcc_criterion
  refine ⟨a, b, hmesh, hcriterion.trans ?_⟩
  have heq (f : ℝ → ℝ) (hc : HasCompactSupport f) (hs : ContDiff ℝ ∞ f)
      (he : ∀ x, f (-x) = f x) (T h : ℝ) :
      roundedFourierTest T h (fun v => (𝓕 (fun x => (f x : ℂ)) v).re) =
        signedHaarStatistic T h (fun v => (𝓕 (fun x => (f x : ℂ)) v).re) (f 0) := by
    obtain ⟨hw, hzero⟩ := compact_smooth_even_fourier_test f hc hs he
    apply roundedFourierTest_eq_signedHaarStatistic T h hw
    simpa only [mul_zero, zero_mul, Real.cos_zero, mul_one] using hzero T 0
  constructor
  · intro H f hc hs he R hR hcut
    apply (H f hc hs he R hR hcut).congr
    intro T
    exact (threePrimeFourierTest_eq_rounded _ _ _ _ _ T _).trans (heq f hc hs he T _)
  · intro H f hc hs he R hR hcut
    apply (H f hc hs he R hR hcut).congr
    intro T
    exact ((threePrimeFourierTest_eq_rounded _ _ _ _ _ T _).trans (heq f hc hs he T _)).symm

end RiemannResearch.Analysis.RoundedFourierCellParseval
