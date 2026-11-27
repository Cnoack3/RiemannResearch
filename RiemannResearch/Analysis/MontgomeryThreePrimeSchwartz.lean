import RiemannResearch.Analysis.MontgomeryAllPairWordLimit
import RiemannResearch.Analysis.MontgomeryEvenFourierTests
import RiemannResearch.Analysis.ThreePrimeFrequencyMesh

/-! # One three-prime mesh for every even Schwartz test of all zero gaps

The squared amplitude here sums prime characters at every physical zeta
occurrence. The mesh is chosen once per height, independently of the test.
-/

noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators Topology ContDiff

namespace RiemannResearch.Analysis.MontgomeryAllPairWordRounding
open ActualInfinitePrimeTorus ActualZeroOrdinate OrdinateCollisionCertificate
open CompactCharacter CompactGaugeOrbitLaw MontgomeryEvenFourierTests

/-- A signed integer combination of the two adjacent ratio frequencies. -/
def meshFrequency (p q r : Nat.Primes) (a b : ℤ) : ℝ :=
  wordFrequency (ratioWord p q a ++ ratioWord q r b)

/-- Fold the entire occurrence list onto the character of one rounded
three-prime word, square it, and subtract all ordered equal-height pairs. -/
def threePrimeFourierTest (p q r : Nat.Primes) (a b : ℤ) (T : ℝ) (w : ℝ → ℝ) : ℝ :=
  let h := meshFrequency p q r a b
  (∫ v, let k := round (Real.log T*v/h)
        w v * (Complex.normSq (∑ i : Copies T,
          character (ratioWord p q (k*a) ++ ratioWord q r (k*b)) (phasePoint (copyOrdinate T i))) -
          (occurrenceCollision (copyOrdinate T) : ℝ))) /
    (2*(T*Real.log T/(2*Real.pi)))

theorem threePrimeFourierTest_eq_rounded (p q r : Nat.Primes) (a b : ℤ) (T : ℝ) (w : ℝ → ℝ) :
    threePrimeFourierTest p q r a b T w = roundedFourierTest T (meshFrequency p q r a b) w := by
  simp only [threePrimeFourierTest, meshFrequency, threePrimeMesh_character_phasePoint,
    roundedFourierTest, occurrenceAmplitude, occurrencePhase, ZeroOrdinate.phase]

/-- For any ordered fixed triple (in particular 2,3,5), the same pair of
integer-valued coefficients works at each height for every even Schwartz
test simultaneously. The measured sum uses actual prime characters. -/
theorem exists_threePrime_schwartz_reconstruction {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) :
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q r (a T) (b T) ∧
        meshFrequency p q r (a T) (b T) < 1/T^3) ∧
      ∀ f : 𝓢(ℝ, ℂ), (∀ x, (f (-x)).re = (f x).re) →
        Tendsto (fun T => actualPositiveTest T (fun x => (f x).re) -
          threePrimeFourierTest p q r (a T) (b T) T (fun v => ((𝓕 f) v).re))
          atTop (𝓝 0) := by
  classical
  let ε (T : ℝ) := if 1 < T then 1/T^3 else 1
  have hpos (T : ℝ) : 0 < ε T := by dsimp [ε]; split_ifs <;> positivity
  have hex (T : ℝ) : ∃ a b : ℤ,
      0 < meshFrequency p q r a b ∧ meshFrequency p q r a b < ε T := by
    obtain ⟨a, b, ha, hb, _⟩ := exists_threePrimeWordFrequency_mesh hpq hqr (hpos T)
    exact ⟨a, b, ha, hb⟩
  choose a b ha hb using hex
  have ht : ∀ᶠ T in atTop, 0 < meshFrequency p q r (a T) (b T) ∧
        meshFrequency p q r (a T) (b T) < 1/T^3 := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact ⟨ha T, by simpa [ε, hT] using hb T⟩
  refine ⟨a, b, ht, ?_⟩
  intro f he
  simp_rw [threePrimeFourierTest_eq_rounded]
  apply actualPositiveTest_sub_rounded_tendsto_zero (ht.mono fun T hT => ⟨hT.1, hT.2.le⟩)
    (integrable_schwartz_weight f)
  intro x
  simpa only [mul_assoc] using even_schwartz_cosine_inversion f he x

/-- The primes 2, 3 and 5 recover every even smooth compactly supported real
test with its ordinary Fourier transform. The height-dependent words are
chosen before the test, so one choice works for all such tests. -/
theorem exists_two_three_five_compact_smooth_reconstruction :
    let p : Nat.Primes := ⟨2, by decide⟩
    let q : Nat.Primes := ⟨3, by decide⟩
    let r : Nat.Primes := ⟨5, by decide⟩
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q r (a T) (b T) ∧
        meshFrequency p q r (a T) (b T) < 1/T^3) ∧
      ∀ f : ℝ → ℝ, HasCompactSupport f → ContDiff ℝ ∞ f → (∀ x, f (-x) = f x) →
        Tendsto (fun T => actualPositiveTest T f -
          threePrimeFourierTest p q r (a T) (b T) T
            (fun v => (𝓕 (fun x => (f x : ℂ)) v).re)) atTop (𝓝 0) := by
  dsimp only
  obtain ⟨a, b, hmesh, htests⟩ :=
    exists_threePrime_schwartz_reconstruction
      (p := ⟨2, by decide⟩) (q := ⟨3, by decide⟩) (r := ⟨5, by decide⟩)
      (by decide) (by decide)
  refine ⟨a, b, hmesh, ?_⟩
  intro f hc hs he
  let c : ℝ → ℂ := Complex.ofRealCLM ∘ f
  have hsupport : HasCompactSupport c := hc.comp_left rfl
  have hsmooth : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp hs
  let g := hsupport.toSchwartzMap hsmooth
  have hg (x : ℝ) : (g x).re = f x := rfl
  exact htests g (fun x => by simpa only [hg] using he x)

end RiemannResearch.Analysis.MontgomeryAllPairWordRounding
