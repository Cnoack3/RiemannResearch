import RiemannResearch.Analysis.GaussianAbsoluteCollision
import RiemannResearch.Analysis.MontgomeryMicroscopicGapPacking
import RiemannResearch.Analysis.FiniteCollisionCertificates

/-! # Frequency and precision costs of absolute collision certificates

All pairs use the original occurrence labels. The Gaussian lower bound uses the
project's unconditioned width-two packing estimate. The signed integral keeps the
entire nonconstant Landau Taylor head before squaring. The same reconstruction
accuracy applies to the finite two-prime Fejér sum. For the rational Landau formula
underlying the restricted prime-word band see Ford–Meng–Zaharescu, Lemma 1,
https://doi.org/10.1112/blms.12001.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ActualZeroCollisionCertificate OrdinateCollisionCertificate MontgomeryPositiveGap

/-- The exact full-real-frequency integral with every retained horizontal moment.
The signed cross term and the square of the whole correction are part of the power. -/
theorem gaussian_power_signed_landau_integral {T : ℝ} (hN : 0 < Ncount 0 T) (a b : ℝ) :
    (Ncount 0 T : ℝ) * reconstructedGaussianPowerWithAllowance a T b =
      ∫ h : ℝ, (let u := h * Real.log T
                let J := gapReconstructionOrder T u b
                let H := ∑ j ∈ Finset.range J, ((u : ℂ)^(2*(j+1)) / ((2*(j+1)).factorial : ℂ)) *
                  evenHorizontalMoment T u (j+1)
                ‖landauSum T u‖^2 - 2 * inner ℝ (landauSum T u) H + ‖H‖^2) *
                  gaussianFrequencyWeight a h := by
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [reconstructedGaussianPowerWithAllowance, ← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun h => ?_
  have hu : 2 * Real.pi * h * (Real.log T / (2 * Real.pi)) = h * Real.log T := by
    field_simp
  dsimp only
  rw [hu, reconstructedGapSpectrum, reconstructedOrdinateSum, norm_sub_sq_real]
  field_simp [hn]

/-- Finite cutoffs always have a positive separation bound on their different ordinates. -/
theorem exists_positive_gaussian_separation {T : ℝ} (hT : 1 < T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Copies T, copyOrdinate T i ≠ copyOrdinate T j →
      δ ≤ |gaussianSeparation T i j| := by
  classical
  let L := Real.log T / (2 * Real.pi)
  let f (i : Copies T) := L * copyOrdinate T i
  let D := FiniteCollisionCertificates.sampleGaps f
  have hL : L ≠ 0 := (div_pos (Real.log_pos hT) (by positivity)).ne'
  have hmem (i j : Copies T) (hne : copyOrdinate T i ≠ copyOrdinate T j) :
      |gaussianSeparation T i j| ∈ D := by
    have hf : f i ≠ f j := fun he => hne (mul_left_cancel₀ hL he)
    simpa only [f, ← mul_sub, gaussianSeparation, L] using
      FiniteCollisionCertificates.abs_sub_mem_sampleGaps f i j hf
  by_cases hD : D.Nonempty
  · refine ⟨D.min' hD, ?_, fun i j hne => D.min'_le _ (hmem i j hne)⟩
    have hm := D.min'_mem hD
    change D.min' hD ∈ ((Finset.univ.product Finset.univ).image
      (fun ij : Copies T × Copies T => |f ij.1 - f ij.2|)).erase 0 at hm
    obtain ⟨hn, hval⟩ := Finset.mem_erase.mp hm
    obtain ⟨ij, _, he⟩ := Finset.mem_image.mp hval
    exact lt_of_le_of_ne (he ▸ abs_nonneg (f ij.1 - f ij.2)) hn.symm
  · exact ⟨1, by norm_num, fun i j hne => False.elim (hD ⟨_, hmem i j hne⟩)⟩

/-- Both orientations of an attained nonzero gap contribute to the unequal-height sum. -/
theorem two_gaussian_terms_le_unequal {a T : ℝ} (hN : 0 < Ncount 0 T) {i j : Copies T}
    (hd : copyOrdinate T i ≠ copyOrdinate T j) :
    2 * Real.exp (-a * (gaussianSeparation T i j)^2) ≤ unequalGaussianTotal a T := by
  classical
  let f := unequalGaussianTerm a T
  have hij : i ≠ j := fun h => hd (congrArg (copyOrdinate T) h)
  have hi : f i j ≤ ∑ k : Copies T, f i k := Finset.single_le_sum
    (fun k _ => unequalGaussianTerm_nonneg _ _ i k) (Finset.mem_univ j)
  have hj : f j i ≤ ∑ k : Copies T, f j k := Finset.single_le_sum
    (fun k _ => unequalGaussianTerm_nonneg _ _ j k) (Finset.mem_univ i)
  have hs : ∑ r ∈ ({i,j} : Finset (Copies T)), ∑ k : Copies T, f r k ≤
      ∑ r : Copies T, ∑ k : Copies T, f r k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun r _ _ => Finset.sum_nonneg fun k _ => unequalGaussianTerm_nonneg _ _ r k)
  have hab : gaussianSeparation T j i = -gaussianSeparation T i j := by
    unfold gaussianSeparation
    ring
  rw [unequalGaussianTotal_eq_sum _ _ hN]
  have hnot : i ∉ ({j} : Finset (Copies T)) := by simpa using hij
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hs
  have he := (add_le_add hi hj).trans hs
  simpa only [f, unequalGaussianTerm, if_neg hd, if_neg hd.symm, hab, neg_sq, two_mul] using he

/-- An attained closest gap forces a minimum precision whenever a certificate passes. -/
theorem absolute_gaussian_necessary_separation_precision {a T : ℝ} (hN : 0 < Ncount 0 T)
    (ha : 0 < a) (hupper : absoluteGaussianExcess a T < 1) {i j : Copies T}
    (hd : copyOrdinate T i ≠ copyOrdinate T j) :
    Real.log (8/5 : ℝ) < a * (gaussianSeparation T i j)^2 := by
  have hc := collision_eq_count_of_absolute_gaussian_upper hN ha hupper
  have hb := (abs_le.mp (absolute_gaussian_quarter_error hN ha)).2
  rw [hc, sub_self, zero_add] at hb
  have hpair := two_gaussian_terms_le_unequal (a := a) hN hd
  rw [neg_mul, Real.exp_neg] at hpair
  have he : 2 / Real.exp (a * (gaussianSeparation T i j)^2) < 5 / 4 := by
    rw [div_eq_mul_inv]
    linarith only [hb, hupper, hpair]
  have hh := (div_lt_iff₀ (Real.exp_pos _)).mp he
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 8/5)).mpr (by linarith only [hh])

/-- Every strictly positive gap in the unfolded window (0,2] contributes at least exp(-4a).
One orientation already suffices for the precision obstruction. -/
theorem width_two_gaussian_lower {a T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) (ha : 0 ≤ a) :
    unfoldedCutoff T * positiveGapMass T 2 * Real.exp (-4*a) ≤ unequalGaussianTotal a T := by
  classical
  let step (i j : Copies T) : ℝ :=
    if 0 < gaussianSeparation T j i ∧ gaussianSeparation T j i ≤ 2 then 1 else 0
  have hW : unfoldedCutoff T ≠ 0 := by
    unfold unfoldedCutoff
    exact (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).ne'
  have hcount : unfoldedCutoff T * positiveGapMass T 2 = ∑ i : Copies T, ∑ j : Copies T, step i j := by
    change unfoldedCutoff T * ((∑ i : Copies T, ∑ j : Copies T, step i j) / unfoldedCutoff T) = _
    field_simp [hW]
  rw [hcount, unequalGaussianTotal_eq_sum _ _ hN, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hg : 0 < gaussianSeparation T j i ∧ gaussianSeparation T j i ≤ 2
  · have he : copyOrdinate T i ≠ copyOrdinate T j := by
      intro hz
      have hp := hg.1
      simp [gaussianSeparation, hz] at hp
    have hab : gaussianSeparation T i j = -gaussianSeparation T j i := by
      unfold gaussianSeparation
      ring
    simp only [step, if_pos hg, one_mul, unequalGaussianTerm, if_neg he, hab, neg_sq]
    apply Real.exp_le_exp.mpr
    have hsq : (gaussianSeparation T j i)^2 ≤ 4 := by
      simpa only [show (2 : ℝ)^2 = 4 by norm_num] using pow_le_pow_left₀ hg.1.le hg.2 2
    nlinarith only [mul_le_mul_of_nonneg_left hsq ha]
  · simpa only [step, if_neg hg, zero_mul] using unequalGaussianTerm_nonneg a T i j

/-- The actual width-two packing theorem forces logarithmically growing precision
at every sufficiently large passing cutoff. -/
theorem eventually_absolute_gaussian_precision_lower :
    ∀ᶠ T : ℝ in atTop, ∀ a : ℝ, 0 < a → absoluteGaussianExcess a T < 1 →
      Real.log ((2/15 : ℝ) * unfoldedCutoff T) < 4*a := by
  filter_upwards [eventually_microscopic_gap_two_gt_one_sixth,
    eventually_gt_atTop (1 : ℝ), eventually_count_pos] with T hpack ht hn
  intro a ha hu
  have hW : 0 < unfoldedCutoff T := by
    unfold unfoldedCutoff
    exact div_pos (mul_pos (zero_lt_one.trans ht) (Real.log_pos ht)) (by positivity)
  have hc := collision_eq_count_of_absolute_gaussian_upper hn ha hu
  have he := (abs_le.mp (absolute_gaussian_quarter_error hn ha)).2
  rw [hc, sub_self, zero_add] at he
  have hg := width_two_gaussian_lower ht hn ha.le
  have hsmall : unfoldedCutoff T * (1/6 : ℝ) / Real.exp (4*a) < 5/4 := by
    rw [div_eq_mul_inv, ← Real.exp_neg, ← neg_mul]
    have hp := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hpack hW) (Real.exp_pos (-4*a))
    linarith only [hg, he, hu, hp]
  have hprod := (div_lt_iff₀ (Real.exp_pos _)).mp hsmall
  apply (Real.log_lt_iff_lt_exp (mul_pos (by norm_num) hW)).mpr
  linarith only [hprod]

/-- One Taylor order works on a prescribed Gaussian Fourier band. It retains every
even horizontal moment through twice that order at every frequency in the band. -/
theorem gaussian_band_order_error {T B h : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T)
    (hB : |h| ≤ B) :
    ‖ordinateSum T (h*Real.log T) - reconstructedOrdinateSum T (h*Real.log T)
      (gapReconstructionOrder T (B*Real.log T) (gaussianCollisionAllowance T))‖ ≤
        1 / (12 * (Ncount 0 T : ℝ)) := by
  have hl := Real.log_pos hT
  have hb := (abs_nonneg h).trans hB
  have hn : (0 : ℝ) < Ncount 0 T := by exact_mod_cast hN
  have hJ := gapReconstructionOrder_sufficient T (B*Real.log T) (gaussianCollisionAllowance T)
  have hcomp : |h*Real.log T| ≤ |B*Real.log T| := by
    simpa only [abs_mul, abs_of_nonneg hb, abs_of_pos hl] using mul_le_mul_of_nonneg_right hB hl.le
  apply (ordinate_reconstruction_exp_error T (h*Real.log T) (gaussianCollisionAllowance T) _
    (by linarith only [hJ, hcomp])).trans_eq
  rw [gaussianCollisionAllowance, Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- Finite two-prime Fejér arithmetic with the same signed Landau reconstruction at each word. -/
def reconstructedTwoPrimeEnergy (T : ℝ) (M : ℕ) : ℝ :=
  (∑ i : Fin (M+1) × Fin (M+1), ∑ j : Fin (M+1) × Fin (M+1),
    let u := TwoPrimeCompactCollision.wordFrequency i - TwoPrimeCompactCollision.wordFrequency j
    ‖reconstructedOrdinateSum T u (gapReconstructionOrder T u (gaussianCollisionAllowance T))‖^2) /
    ((M+1 : ℕ) : ℝ)^4

/-- The quarter-pair accuracy holds also for the finite Fejér sum, independently of its width. -/
theorem two_prime_signed_reconstruction_quarter {T : ℝ} (hN : 0 < Ncount 0 T) (M : ℕ) :
    |TwoPrimeCompactCollision.compactEnergy (copyOrdinate T) M - reconstructedTwoPrimeEnergy T M| ≤
      1/4 := by
  classical
  let W := Fin (M+1) × Fin (M+1)
  let u (i j : W) :=
    TwoPrimeCompactCollision.wordFrequency i - TwoPrimeCompactCollision.wordFrequency j
  let f (i j : W) := Complex.normSq (occurrenceAmplitude (copyOrdinate T) (u i j))
  let g (i j : W) := ‖reconstructedOrdinateSum T (u i j)
    (gapReconstructionOrder T (u i j) (gaussianCollisionAllowance T))‖^2
  have hn : (0 : ℝ) < Ncount 0 T := by exact_mod_cast hN
  have hp (i j : W) : |f i j - g i j| ≤ 1/4 := by
    have he := gap_reconstruction_exp_error T (u i j) (gaussianCollisionAllowance T) _
      (gaussianCollisionAllowance_nonneg hN)
      (gapReconstructionOrder_sufficient T (u i j) (gaussianCollisionAllowance T))
    rw [← occurrenceAmplitude_normSq, abs_div, abs_of_pos hn] at he
    have hh := (div_le_iff₀ hn).mp he
    calc
      _ ≤ _ := hh
      _ = 3 * (Ncount 0 T : ℝ) * Real.exp (-gaussianCollisionAllowance T) := by ring
      _ = _ := gaussianCollisionAllowance_error hN
  rw [TwoPrimeCompactCollision.compactEnergy_eq_fourier]
  change |(∑ i : W, ∑ j : W, f i j) / ((M+1 : ℕ) : ℝ)^4 -
    (∑ i : W, ∑ j : W, g i j) / ((M+1 : ℕ) : ℝ)^4| ≤ 1/4
  have hd : 0 < ((M+1 : ℕ) : ℝ)^4 := by positivity
  rw [← sub_div, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : W, |∑ j : W, (f i j - g i j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : W, ∑ _j : W, (1/4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hp i j)
    _ = _ := by
      simp only [W, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Fintype.card_fin, Nat.cast_mul]
      ring

/-- A signed finite prime-word test with a quarter-pair safety margin detects the same
collision event as the Gaussian certificate. -/
theorem signed_two_prime_fejer_certificate_iff {T : ℝ} (hN : 0 < Ncount 0 T) :
    (∃ M : ℕ, reconstructedTwoPrimeEnergy T M < (Ncount 0 T : ℝ) + 7/4) ↔
      actualCollision T = Ncount 0 T := by
  constructor
  · rintro ⟨M, hM⟩
    have he := (abs_le.mp (two_prime_signed_reconstruction_quarter hN M)).2
    have hl := TwoPrimeCompactCollision.actualCollision_le_compactEnergy T M
    have hh : (actualCollision T : ℝ) < (Ncount 0 T : ℝ)+2 := by linarith only [hl, he, hM]
    have hlt : actualCollision T < Ncount 0 T + 2 := by exact_mod_cast hh
    have hsum := actualCollision_eq_count_add_excess T
    obtain ⟨k, hk⟩ := actualCollision_sub_count_even T
    omega
  · intro hc
    have he : (occurrenceCollision (copyOrdinate T) : ℝ) = (Ncount 0 T : ℝ) := by exact_mod_cast hc
    have hn1 : (occurrenceCollision (copyOrdinate T) : ℝ) < (Ncount 0 T : ℝ)+1 := by linarith
    obtain ⟨M,hM⟩ := ((TwoPrimeCompactCollision.compactEnergy_tendsto (copyOrdinate T)).eventually_lt_const
      hn1).exists
    have hr := (abs_le.mp (two_prime_signed_reconstruction_quarter hN M)).1
    exact ⟨M, by linarith only [hM, hr]⟩

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.eventually_absolute_gaussian_precision_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_absolute_gaussian_precision_lower

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.two_prime_signed_reconstruction_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_prime_signed_reconstruction_quarter

end RiemannResearch.Analysis.ActualZeroOrdinate
