import RiemannResearch.Analysis.GaussianCollisionFiniteBand
import RiemannResearch.Analysis.MontgomeryReconstructedGapTests
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Translated Gaussian bounds for the finite-band collision test

Translation of an even Fourier weight gives a cosine factor. For the Gaussian
the unshifted pair weights are positive, so every translate costs at most the
centered energy. Comparing the two exterior half-lines with translates at the
band endpoints yields a relative tail estimate. All zero occurrences and the
signed horizontal Taylor reconstruction of the original test are retained.

For the transform of a translated Gaussian see Oregon State University,
*The Geometry of Mathematical Methods*, equation (21.7.5),
<https://books.physics.oregonstate.edu/GMM/ftransex.html>. The absolute
collision threshold below also uses the project's quarter-pair error and parity.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ActualZeroCollisionCertificate OrdinateCollisionCertificate MontgomeryPositiveGap

/-- Translation of a real even weight multiplies its cosine transform by a phase cosine. -/
theorem cosineGapProbe_translate_of_even {w : ℝ → ℝ} (hw : Integrable w)
    (heven : ∀ h, w (-h) = w h) (s x : ℝ) :
    cosineGapProbe (fun h => w (h-s)) x =
      cosineGapProbe w x * Real.cos (2 * Real.pi * s * x) := by
  let t := 2 * Real.pi * x
  have hc : Integrable (fun h : ℝ => Real.cos (t*h) * w h) :=
    hw.bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun h => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*h))
  have hs : Integrable (fun h : ℝ => Real.sin (t*h) * w h) :=
    hw.bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun h => by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t*h))
  have hodd := integral_neg_eq_self (fun h : ℝ => Real.sin (t*h) * w h) volume
  simp only [mul_neg, Real.sin_neg, heven, neg_mul, integral_neg] at hodd
  have hzero : (∫ h : ℝ, Real.sin (t*h) * w h) = 0 := by linarith only [hodd]
  have hfreq (h : ℝ) : 2 * Real.pi * h * x = t*h := by dsimp [t]; ring
  simp only [cosineGapProbe, hfreq]
  calc
    (∫ h : ℝ, Real.cos (t*h) * w (h-s)) =
        ∫ h : ℝ, Real.cos (t*(h+s)) * w h := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (μ := volume)
          (fun h : ℝ => Real.cos (t*h) * w (h-s)) s).symm
    _ = ∫ h : ℝ, ((Real.cos (t*h)*w h) * Real.cos (t*s) -
                  (Real.sin (t*h)*w h) * Real.sin (t*s)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun h => by dsimp only; rw [mul_add, Real.cos_add]; ring
    _ = _ := by
      rw [integral_sub (hc.mul_const _) (hs.mul_const _), integral_mul_const,
        integral_mul_const, hzero, zero_mul, sub_zero]

private theorem gaussianWeight_nonneg (a h : ℝ) : 0 ≤ gaussianFrequencyWeight a h := by
  unfold gaussianFrequencyWeight
  positivity

private theorem gaussianWeight_even (a h : ℝ) :
    gaussianFrequencyWeight a (-h) = gaussianFrequencyWeight a h := by
  simp only [gaussianFrequencyWeight, neg_sq]

private theorem fullSpectrum_nonneg (T u : ℝ) : 0 ≤ fullGapSpectrum T u := by
  rw [fullGapSpectrum, ← occurrenceAmplitude_normSq]
  exact div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

/-- Unnormalized power of the actual ordinate sum measured by a Gaussian centered at s. -/
def translatedGaussianPairPower (a T s : ℝ) : ℝ :=
  (Ncount 0 T : ℝ) * ∫ h : ℝ, fullGapSpectrum T
    (2 * Real.pi * h * (Real.log T / (2 * Real.pi))) * gaussianFrequencyWeight a (h-s)

/-- Exact signed pair expansion of a translated measurement, including equal ordinates. -/
theorem translatedGaussianPairPower_eq {a T : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T) (s : ℝ) :
    translatedGaussianPairPower a T s = ∑ i : Copies T, ∑ j : Copies T,
      Real.exp (-a * (gaussianSeparation T i j)^2) *
        Real.cos (2 * Real.pi * s * gaussianSeparation T i j) := by
  have hw := gaussianFrequencyWeight_spec ha
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [translatedGaussianPairPower,
    (fullGapSpectrum_cosine_pairing T (Real.log T/(2*Real.pi)) (hw.1.comp_sub_right s)).2]
  simp_rw [cosineGapProbe_translate_of_even hw.1 (gaussianWeight_even a), hw.2.2]
  change (Ncount 0 T : ℝ) * (_ / (Ncount 0 T : ℝ)) = _
  rw [div_eq_mul_inv, mul_left_comm (Ncount 0 T : ℝ), mul_inv_cancel₀ hn, mul_one]
  rfl

/-- All loss under translation comes from unequal ordinates, with nonnegative weight. -/
theorem translatedGaussianPairPower_deficit {a T : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T) (s : ℝ) :
    translatedGaussianPairPower a T 0 - translatedGaussianPairPower a T s =
      ∑ i : Copies T, ∑ j : Copies T, Real.exp (-a * (gaussianSeparation T i j)^2) *
        (1 - Real.cos (2 * Real.pi * s * gaussianSeparation T i j)) := by
  rw [translatedGaussianPairPower_eq ha hN, translatedGaussianPairPower_eq ha hN]
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, mul_sub, Finset.sum_sub_distrib]

theorem translatedGaussianPairPower_le_center {a T : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T)
    (s : ℝ) : translatedGaussianPairPower a T s ≤ translatedGaussianPairPower a T 0 := by
  apply sub_nonneg.mp
  rw [translatedGaussianPairPower_deficit ha hN]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _))

theorem translatedGaussianPairPower_zero {a T : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T) :
    translatedGaussianPairPower a T 0 = (actualCollision T : ℝ) + unequalGaussianTotal a T := by
  classical
  have hterm (i j : Copies T) : Real.exp (-a * (gaussianSeparation T i j)^2) =
      (if copyOrdinate T i = copyOrdinate T j then (1 : ℝ) else 0) +
        unequalGaussianTerm a T i j := by
    by_cases h : copyOrdinate T i = copyOrdinate T j
    · simp [unequalGaussianTerm, gaussianSeparation, h]
    · simp [unequalGaussianTerm, h]
  rw [translatedGaussianPairPower_eq ha hN, unequalGaussianTotal_eq_sum _ _ hN]
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, hterm, Finset.sum_add_distrib,
    actualCollision, occurrenceCollision, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private theorem gaussianWeight_le_right_translate {a B h : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hh : B ≤ h) : gaussianFrequencyWeight a h ≤
      Real.exp (-(Real.pi^2/a)*B^2) * gaussianFrequencyWeight a (h-B) := by
  let k := Real.pi^2/a
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have he : -k*h^2 ≤ -k*B^2 + -k*(h-B)^2 := by
    nlinarith only [mul_nonneg hk (mul_nonneg hB (sub_nonneg.mpr hh))]
  change Real.sqrt (Real.pi/a) * Real.exp (-k*h^2) ≤
    Real.exp (-k*B^2) * (Real.sqrt (Real.pi/a) * Real.exp (-k*(h-B)^2))
  calc
    _ ≤ Real.sqrt (Real.pi/a) * (Real.exp (-k*B^2) * Real.exp (-k*(h-B)^2)) := by
      rw [← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- True power outside the interval, measured in ordered-pair units. -/
def gaussianPairBandTail (a T B : ℝ) : ℝ :=
  (Ncount 0 T : ℝ) * ∫ h in (Icc (-B) B)ᶜ, fullGapSpectrum T
    (2 * Real.pi * h * (Real.log T / (2 * Real.pi))) * gaussianFrequencyWeight a h

/-- The sharper tail uses the power translated to the boundary. Its loss relative
to the centered comparison is given exactly by the pair deficit above. -/
theorem gaussian_pair_tail_le_translated {a T B : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T)
    (hB : 0 ≤ B) :
    gaussianPairBandTail a T B ≤
        2 * Real.exp (-(Real.pi^2/a)*B^2) * translatedGaussianPairPower a T B ∧
      2 * Real.exp (-(Real.pi^2/a)*B^2) * translatedGaussianPairPower a T B ≤
        2 * Real.exp (-(Real.pi^2/a)*B^2) * translatedGaussianPairPower a T 0 := by
  let L := Real.log T / (2*Real.pi)
  let F (h : ℝ) := fullGapSpectrum T (2*Real.pi*h*L)
  let w := gaussianFrequencyWeight a
  let g (s h : ℝ) := F h * w (h-s)
  let c := Real.exp (-(Real.pi^2/a)*B^2)
  let S := Icc (-B) B
  have hs : MeasurableSet S := measurableSet_Icc
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hF (h : ℝ) : 0 ≤ F h := fullSpectrum_nonneg _ _
  have hw (h : ℝ) : 0 ≤ w h := gaussianWeight_nonneg _ _
  have hi (s : ℝ) : Integrable (g s) :=
    (fullGapSpectrum_cosine_pairing T L ((gaussianFrequencyWeight_spec ha).1.comp_sub_right s)).1
  have hg (s h : ℝ) : 0 ≤ g s h := mul_nonneg (hF h) (hw _)
  have hmajor (h : ℝ) (hh : h ∈ Sᶜ) : w h ≤ c * (w (h-B) + w (h-(-B))) := by
    by_cases hright : B ≤ h
    · exact (gaussianWeight_le_right_translate ha hB hright).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hw _)) hc)
    · have hleft : B ≤ -h := by
        by_contra! hlt
        exact hh ⟨by linarith, le_of_lt (lt_of_not_ge hright)⟩
      have hmirror := gaussianWeight_le_right_translate ha hB hleft
      rw [show -h-B = -(h-(-B)) by ring, gaussianWeight_even, gaussianWeight_even] at hmirror
      exact hmirror.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hw _)) hc)
  have hGI := ((hi B).add (hi (-B))).const_mul c
  have hdom : (∫ h in Sᶜ, F h * w h) ≤ c * ((∫ h, g B h) + ∫ h, g (-B) h) := by
    calc
      _ ≤ ∫ h in Sᶜ, c * (g B h + g (-B) h) := by
        apply integral_mono_of_nonneg (ae_of_all _ fun h => mul_nonneg (hF h) (hw h))
          hGI.integrableOn
        apply ae_restrict_of_forall_mem hs.compl
        intro h hh
        exact (mul_le_mul_of_nonneg_left (hmajor h hh) (hF h)).trans_eq (by dsimp [g]; ring)
      _ ≤ ∫ h, c * (g B h + g (-B) h) := setIntegral_le_integral hGI
        (ae_of_all _ fun h => mul_nonneg hc (add_nonneg (hg _ _) (hg _ _)))
      _ = _ := by rw [integral_const_mul, integral_add (hi B) (hi (-B))]
  have hshift : translatedGaussianPairPower a T (-B) = translatedGaussianPairPower a T B := by
    rw [translatedGaussianPairPower_eq ha hN, translatedGaussianPairPower_eq ha hN]
    simp only [mul_neg, neg_mul, Real.cos_neg]
  have hn : 0 ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, mul_le_mul_of_nonneg_left
    (translatedGaussianPairPower_le_center ha hN B) (by positivity)⟩
  calc
    gaussianPairBandTail a T B ≤ (Ncount 0 T : ℝ) * (c * ((∫ h, g B h) + ∫ h, g (-B) h)) :=
      mul_le_mul_of_nonneg_left hdom hn
    _ = c * (translatedGaussianPairPower a T B + translatedGaussianPairPower a T (-B)) := by
      unfold translatedGaussianPairPower
      dsimp only [g, F, L, w]
      ring
    _ = _ := by rw [hshift]; dsimp [c]; ring

/-- After subtracting the true tail, the signed reconstructed band power still
has at most a quarter-pair error. The bound holds at every radius. -/
theorem gaussian_band_pair_reconstruction_error {a T : ℝ} (ha : 0 < a)
    (hN : 0 < Ncount 0 T) (B : ℝ) :
    |translatedGaussianPairPower a T 0 - gaussianPairBandTail a T B -
      (bandGaussianExcess a T B + (Ncount 0 T : ℝ))| ≤ 1/4 := by
  let n : ℝ := Ncount 0 T
  let L := Real.log T/(2*Real.pi)
  let b := gaussianCollisionAllowance T
  let S := Icc (-B) B
  let w := gaussianFrequencyWeight a
  let v := S.indicator w
  let F (h : ℝ) := fullGapSpectrum T (2*Real.pi*h*L)
  let R (h : ℝ) := reconstructedGapSpectrum T (2*Real.pi*h*L) b
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hS : MeasurableSet S := measurableSet_Icc
  have hw : Integrable w := (gaussianFrequencyWeight_spec ha).1
  have hv : Integrable v := hw.indicator hS
  have hmass : (∫ h : ℝ, |v h|) ≤ 1 := by
    apply le_trans (integral_mono hv.norm hw.norm ?_) (gaussianFrequencyWeight_spec ha).2.1.le
    intro h
    by_cases hh : h ∈ S <;> simp [v, hh, Real.norm_eq_abs]
  have restrict_eq (f : ℝ → ℝ) : (∫ h, f h * v h) = ∫ h in S, f h * w h := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact ae_of_all _ fun h => by by_cases hh : h ∈ S <;> simp [v, hh]
  have he := (reconstructed_cosine_gap_test T L b (gaussianCollisionAllowance_nonneg hN) hv).2
  rw [← (fullGapSpectrum_cosine_pairing T L hv).2] at he
  change |(∫ h, F h * v h) - ∫ h, R h * v h| ≤ (3*Real.exp (-b)) * ∫ h, |v h| at he
  rw [restrict_eq F, restrict_eq R] at he
  have hquarter : n * |(∫ h in S, F h * w h) - ∫ h in S, R h * w h| ≤ 1/4 := by
    calc
      _ ≤ n * ((3 * Real.exp (-b)) * 1) :=
        mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left hmass (by positivity))) hn
      _ = 3*n*Real.exp (-b) := by ring
      _ = _ := gaussianCollisionAllowance_error hN
  have hfull := integral_add_compl hS (fullGapSpectrum_cosine_pairing T L hw).1
  change (∫ h in S, F h * w h) + (∫ h in Sᶜ, F h * w h) = ∫ h, F h * w h at hfull
  rw [translatedGaussianPairPower]
  simp only [sub_zero]
  change |n * (∫ h, F h * w h) - n * (∫ h in Sᶜ, F h * w h) -
      (n * ((∫ h in S, R h * w h)-1) + n)| ≤ 1/4
  rw [← hfull, show ∀ x y z : ℝ, n*(x+y)-n*y-(n*(z-1)+n) = n*(x-z) by intros; ring,
    abs_mul, abs_of_nonneg hn]
  exact hquarter

/-- Direct lower bound for the signed band integral on the scale of a single pair. -/
theorem gaussian_band_relative_lower {a T B : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T)
    (hB : 0 ≤ B) :
    (1-2*Real.exp (-(Real.pi^2/a)*B^2)) * translatedGaussianPairPower a T 0 ≤
      bandGaussianExcess a T B + (Ncount 0 T : ℝ) + 1/4 := by
  obtain ⟨ht, hc⟩ := gaussian_pair_tail_le_translated ha hN hB
  have he := (abs_le.mp (gaussian_band_pair_reconstruction_error ha hN B)).2
  linarith only [he, ht.trans hc, show (1-2*Real.exp (-(Real.pi^2/a)*B^2)) *
    translatedGaussianPairPower a T 0 = translatedGaussianPairPower a T 0 -
      2*Real.exp (-(Real.pi^2/a)*B^2)*translatedGaussianPairPower a T 0 by ring]

/-- Radius calibrated against the first forbidden true power, N+2. -/
def relativeGaussianCollisionRadius (a T : ℝ) : ℝ :=
  Real.sqrt ((a/Real.pi^2) * Real.log (8*((Ncount 0 T : ℝ)+2)/3))

private theorem relativeRadius_factor {a : ℝ} (ha : 0 < a) (T : ℝ) :
    2 * Real.exp (-(Real.pi^2/a)*(relativeGaussianCollisionRadius a T)^2) =
      3 / (4*((Ncount 0 T : ℝ)+2)) := by
  let n : ℝ := Ncount 0 T
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hy : 1 ≤ 8*(n+2)/3 := by linarith
  have hypos := zero_lt_one.trans_le hy
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold relativeGaussianCollisionRadius
  rw [Real.sq_sqrt (mul_nonneg (by positivity) (Real.log_nonneg hy))]
  change 2 * Real.exp (-(Real.pi^2/a)*((a/Real.pi^2)*Real.log (8*(n+2)/3))) = _
  rw [show -(Real.pi^2/a)*((a/Real.pi^2)*Real.log (8*(n+2)/3)) = -Real.log (8*(n+2)/3) by
    field_simp [ha.ne', hp], Real.exp_neg, Real.exp_log hypos]
  change 2 * (8*(n+2)/3)⁻¹ = 3/(4*(n+2))
  field_simp [show n+2 ≠ 0 by linarith]
  ring

/-- Passing the shorter signed band forces the full true power, including all
unequal-height Gaussian mass, below N+2 at the very same precision. -/
theorem pair_power_lt_of_relative_band {a T : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T)
    (hpass : bandGaussianExcess a T (relativeGaussianCollisionRadius a T) < 1) :
    (actualCollision T : ℝ) + unequalGaussianTotal a T < (Ncount 0 T : ℝ)+2 := by
  let n : ℝ := Ncount 0 T
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hden : 0 < 4*(n+2) := by linarith
  have h := gaussian_band_relative_lower (B := relativeGaussianCollisionRadius a T) ha hN
    (Real.sqrt_nonneg _)
  rw [relativeRadius_factor ha, translatedGaussianPairPower_zero ha hN] at h
  by_contra! hge
  have hpos : 0 ≤ 1-3/(4*(n+2)) := sub_nonneg.mpr ((div_le_one hden).mpr (by linarith))
  have hmul := mul_le_mul_of_nonneg_left hge hpos
  have hcal : (1-3/(4*(n+2)))*(n+2) = n+5/4 := by
    field_simp [show n+2 ≠ 0 by linarith]
    ring
  change (1-3/(4*(n+2)))*(n+2) ≤ _ at hmul
  rw [hcal] at hmul
  change (1-3/(4*(n+2)))*_ ≤ _ + n + 1/4 at h
  linarith only [hmul, h, hpass]

/-- The same strict threshold characterizes the collision-free cutoff on the shorter band. -/
theorem relative_band_gaussian_certificate_iff {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    (∃ k : ℕ, let a : ℝ := (k:ℝ)+1
      bandGaussianExcess a T (relativeGaussianCollisionRadius a T) < 1) ↔
      actualCollision T = Ncount 0 T := by
  constructor
  · rintro ⟨k, hk⟩
    have hp := pair_power_lt_of_relative_band (a := (k:ℝ)+1) (by positivity) hN hk
    have hlt : (actualCollision T : ℝ) < (Ncount 0 T : ℝ)+2 := by
      linarith only [hp, unequalGaussianTotal_nonneg ((k:ℝ)+1) T]
    have hh : actualCollision T < Ncount 0 T + 2 := by exact_mod_cast hlt
    have hsum := actualCollision_eq_count_add_excess T
    obtain ⟨m,hm⟩ := actualCollision_sub_count_even T
    omega
  · intro hc
    obtain ⟨k,hk⟩ := (absolute_gaussian_finite_iff hT hN).mpr hc
    have ht := (absolute_gaussian_band_tail (a := (k:ℝ)+1)
      (B := relativeGaussianCollisionRadius ((k:ℝ)+1) T) (by positivity) hN (Real.sqrt_nonneg _)).1
    exact ⟨k, by dsimp only at hk ⊢; linarith only [hk, ht]⟩

/-- The cofinal strict arithmetic bound for this radius is equivalent to global
criticality and analytic simplicity. -/
theorem cofinal_relative_band_gaussian_iff_global :
    (∃ᶠ T : ℝ in atTop, ∃ k : ℕ, let a : ℝ := (k:ℝ)+1
      bandGaussianExcess a T (relativeGaussianCollisionRadius a T) < 1) ↔
      RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  rw [← cofinal_finite_band_gaussian_iff_global]
  constructor
  · intro h
    apply (h.and_eventually ((eventually_gt_atTop (1 : ℝ)).and eventually_count_pos)).mono
    rintro T ⟨hc, ht, hn⟩
    exact (finite_band_gaussian_certificate_iff ht hn).mpr
      ((relative_band_gaussian_certificate_iff ht hn).mp hc)
  · intro h
    apply (h.and_eventually ((eventually_gt_atTop (1 : ℝ)).and eventually_count_pos)).mono
    rintro T ⟨hc, ht, hn⟩
    exact (relative_band_gaussian_certificate_iff ht hn).mpr
      ((finite_band_gaussian_certificate_iff ht hn).mp hc)

/-- Width-two packing forces growing precision even for a pass on the shorter band.
The true unequal-ordinate mass is strictly below two at such a pass. -/
theorem eventually_relative_band_precision_lower :
    ∀ᶠ T : ℝ in atTop, ∀ a : ℝ, 0 < a →
      bandGaussianExcess a T (relativeGaussianCollisionRadius a T) < 1 →
      Real.log (unfoldedCutoff T / 12) < 4*a := by
  filter_upwards [eventually_microscopic_gap_two_gt_one_sixth, eventually_gt_atTop (1 : ℝ),
    eventually_count_pos] with T hpack hT hN
  intro a ha hpass
  have hW : 0 < unfoldedCutoff T := by
    unfold unfoldedCutoff
    exact div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hcount : Ncount 0 T ≤ actualCollision T := by
    rw [actualCollision_eq_count_add_excess]
    omega
  have hcount' : (Ncount 0 T : ℝ) ≤ (actualCollision T : ℝ) := by exact_mod_cast hcount
  have hp := pair_power_lt_of_relative_band ha hN hpass
  have hsmall : unequalGaussianTotal a T < 2 := by linarith only [hp, hcount']
  have hpair := width_two_gaussian_lower hT hN ha.le
  have hpck := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hpack hW) (Real.exp_pos (-4*a))
  have he : unfoldedCutoff T * (1/6 : ℝ) / Real.exp (4*a) < 2 := by
    rw [div_eq_mul_inv, ← Real.exp_neg, ← neg_mul]
    linarith only [hpck, hpair, hsmall]
  have hh := (div_lt_iff₀ (Real.exp_pos _)).mp he
  exact (Real.log_lt_iff_lt_exp (div_pos hW (by norm_num))).mpr (by linarith only [hh])

/-- Explicit lower bound for the Fourier radius of every sufficiently high pass. -/
theorem eventually_relative_band_radius_lower :
    ∀ᶠ T : ℝ in atTop, ∀ a : ℝ, 0 < a →
      bandGaussianExcess a T (relativeGaussianCollisionRadius a T) < 1 →
      Real.log (unfoldedCutoff T / 12) * Real.log (8*((Ncount 0 T : ℝ)+2)/3) <
        4*Real.pi^2*(relativeGaussianCollisionRadius a T)^2 := by
  filter_upwards [eventually_relative_band_precision_lower] with T hp
  intro a ha hpass
  let n : ℝ := Ncount 0 T
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hl : 0 < Real.log (8*(n+2)/3) := Real.log_pos (by linarith)
  have h := mul_lt_mul_of_pos_right (hp a ha hpass) hl
  rw [relativeGaussianCollisionRadius, Real.sq_sqrt (mul_nonneg (by positivity) hl.le)]
  apply h.trans_eq
  change 4*a*Real.log (8*(n+2)/3) = 4*Real.pi^2*((a/Real.pi^2)*Real.log (8*(n+2)/3))
  field_simp [Real.pi_ne_zero] <;> ring

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.gaussian_pair_tail_le_translated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gaussian_pair_tail_le_translated

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.cofinal_relative_band_gaussian_iff_global' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_relative_band_gaussian_iff_global

end RiemannResearch.Analysis.ActualZeroOrdinate
