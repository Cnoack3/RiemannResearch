import RiemannResearch.Analysis.MontgomeryThreePrimeSchwartz
import RiemannResearch.Analysis.MontgomerySmoothGapSandwich

/-!
# Countably many three-prime Fourier envelopes for ordinary pair correlation

The test for rational radii 0 < r < s equals one up to r and vanishes
from s onward. It is enough to bound its collision-subtracted arithmetic
Fourier pairing between the two cumulative sine masses, with arbitrarily small
fixed slack. The width s-r may be chosen after a physical test point is fixed.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology FourierTransform

namespace RiemannResearch.Analysis.MontgomeryAllPairWordRounding
open MontgomeryPositiveGap

/-- The canonical even compact smooth plateau with a rational transition interval. -/
def rationalPlateau (r s : ℚ) (hr : 0 < r) (hrs : r < s) : ContDiffBump (0 : ℝ) :=
  ⟨(r : ℝ), (s : ℝ), by exact_mod_cast hr, by exact_mod_cast hrs⟩

/-- The real Fourier weight of the single canonical plateau for each radius pair. -/
def rationalPlateauWeight (r s : ℚ) (hr : 0 < r) (hrs : r < s) : ℝ → ℝ :=
  let f : ℝ → ℝ := rationalPlateau r s hr hrs
  fun v => (𝓕 (fun x : ℝ => (f x : ℂ)) v).re

/-- An arithmetic envelope suffices; individual plateau pairings may have a
range of subsequential limits within the indicated interval in the hypothesis. -/
theorem exists_two_three_five_rational_plateau_envelopes :
    let p : Nat.Primes := ⟨2, by decide⟩
    let q : Nat.Primes := ⟨3, by decide⟩
    let z : Nat.Primes := ⟨5, by decide⟩
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q z (a T) (b T) ∧
        meshFrequency p q z (a T) (b T) < 1 / T^3) ∧
      (PositiveGapPCC ↔ ∀ r s : ℚ, ∀ hr : 0 < r, ∀ hrs : r < s, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ T in atTop,
          sineGapMass r - ε ≤ threePrimeFourierTest p q z (a T) (b T) T
            (rationalPlateauWeight r s hr hrs) ∧
          threePrimeFourierTest p q z (a T) (b T) T (rationalPlateauWeight r s hr hrs) ≤
            sineGapMass s + ε) := by
  dsimp only
  obtain ⟨a, b, hm, hrec⟩ := exists_two_three_five_compact_smooth_reconstruction
  refine ⟨a, b, hm, ?_⟩
  let Q (r s : ℚ) (hr : 0 < r) (hrs : r < s) (T : ℝ) :=
    threePrimeFourierTest ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩ (a T) (b T) T
      (rationalPlateauWeight r s hr hrs)
  have herr (r s : ℚ) (hr : 0 < r) (hrs : r < s) (e : ℝ) (he : 0 < e) :
      ∀ᶠ T : ℝ in atTop,
        |actualPositiveTest T (rationalPlateau r s hr hrs) - Q r s hr hrs T| < e := by
    let g := rationalPlateau r s hr hrs
    have h := Metric.tendsto_nhds.mp (hrec g g.hasCompactSupport g.contDiff g.neg) e he
    simpa only [g, Q, rationalPlateauWeight, Real.dist_eq, sub_zero] using h
  have hb (r s : ℚ) (hr : 0 < r) (hrs : r < s) {T : ℝ} (hT : 1 < T) :
      positiveGapMass T r ≤ actualPositiveTest T (rationalPlateau r s hr hrs) ∧
      actualPositiveTest T (rationalPlateau r s hr hrs) ≤ positiveGapMass T s :=
    actualPositiveTest_bump_bounds hT (rationalPlateau r s hr hrs)
  constructor
  · intro h r s hr hrs e he
    have hp := positiveGapPCC_iff_rationalWidthLimits.mp h
    have hl := (hp r hr).eventually_const_lt (show sineGapMass r-e/2 < sineGapMass r by linarith)
    have hu := (hp s (hr.trans hrs)).eventually_lt_const
      (show sineGapMass s < sineGapMass s+e/2 by linarith)
    filter_upwards [hl, hu, herr r s hr hrs (e/2) (half_pos he),
      eventually_gt_atTop (1 : ℝ)] with T hlow hhigh hd hT
    change sineGapMass r-e ≤ Q r s hr hrs T ∧ Q r s hr hrs T ≤ sineGapMass s+e
    have hd' := abs_lt.mp hd
    have hpair := hb r s hr hrs hT
    constructor <;> linarith only [hlow, hhigh, hd'.1, hd'.2, hpair.1, hpair.2]
  · intro h
    apply positiveGapPCC_iff_rationalWidthLimits.mpr
    intro q hq
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    apply tendsto_order.2
    constructor
    · intro l hl
      let e : ℝ := (sineGapMass q-l)/4
      have he : 0 < e := by dsimp only [e]; linarith
      obtain ⟨r, hlow, hrq⟩ := exists_rat_btwn
        (show max 0 ((q : ℝ)-e) < (q : ℝ) from max_lt hq' (by linarith))
      have hr : (0:ℚ) < r := by exact_mod_cast ((le_max_left _ _).trans_lt hlow)
      have hrq' : r < q := by exact_mod_cast hrq
      have hinc := (sineGapMass_increment_bounds hrq.le).2
      have hnear := (le_max_right _ _).trans_lt hlow
      filter_upwards [h r q hr hrq' e he, herr r q hr hrq' e he,
        eventually_gt_atTop (1:ℝ)] with T hp hd hT
      change sineGapMass r-e ≤ Q r q hr hrq' T ∧ _ at hp
      have htest := (hb r q hr hrq' hT).2
      have hd' := (abs_lt.mp hd).1
      dsimp only [e] at *
      linarith only [hp.1, hd', htest, hnear, hinc, hl]
    · intro u hu
      let e : ℝ := (u-sineGapMass q)/4
      have he : 0 < e := by dsimp only [e]; linarith
      obtain ⟨s, hqs, hnear⟩ := exists_rat_btwn (show (q : ℝ) < (q : ℝ)+e by linarith)
      have hqs' : q < s := by exact_mod_cast hqs
      have hinc := (sineGapMass_increment_bounds hqs.le).2
      filter_upwards [h q s hq hqs' e he, herr q s hq hqs' e he,
        eventually_gt_atTop (1:ℝ)] with T hp hd hT
      change _ ∧ Q q s hq hqs' T ≤ sineGapMass s+e at hp
      have htest := (hb q s hq hqs' hT).1
      have hd' := (abs_lt.mp hd).2
      dsimp only [e] at *
      linarith only [hp.2, hd', htest, hnear, hinc, hu]

end RiemannResearch.Analysis.MontgomeryAllPairWordRounding
