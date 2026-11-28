import RiemannResearch.Analysis.GaussianCollisionBandwidth
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # A finite Fourier band for the absolute Gaussian collision test

The Gaussian tail can be discarded with a second quarter-pair allowance.
All retained frequencies use the signed Landau reconstruction and a bounded
range of Taylor orders. This gives a compact-interval arithmetic target.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ActualZeroCollisionCertificate

private theorem frequencyWeight_nonneg (a h : ℝ) : 0 ≤ gaussianFrequencyWeight a h := by
  unfold gaussianFrequencyWeight
  positivity

private theorem frequencyWeight_integral {a : ℝ} (ha : 0 < a) :
    (∫ h : ℝ, gaussianFrequencyWeight a h) = 1 := by
  have he := (gaussianFrequencyWeight_spec ha).2.1
  simpa only [abs_of_nonneg (frequencyWeight_nonneg _ _)] using he

/-- Comparison with a Gaussian of twice the variance outside a specified interval. -/
theorem gaussian_frequency_tail_comparison {a B h : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hh : B ≤ |h|) :
    gaussianFrequencyWeight a h ≤ Real.sqrt 2 * Real.exp (-(Real.pi^2/(2*a))*B^2) *
      gaussianFrequencyWeight (2*a) h := by
  have hc : Real.sqrt (Real.pi/a) = Real.sqrt 2 * Real.sqrt (Real.pi/(2*a)) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp [ha.ne']
  have hs := pow_le_pow_left₀ hB hh 2
  rw [sq_abs] at hs
  have hd : Real.pi^2/a = 2*(Real.pi^2/(2*a)) := by field_simp [ha.ne']
  have he : Real.exp (-(Real.pi^2/a)*h^2) ≤ Real.exp (-(Real.pi^2/(2*a))*B^2) *
      Real.exp (-(Real.pi^2/(2*a))*h^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hd]
    nlinarith only [mul_le_mul_of_nonneg_left hs (show 0 ≤ Real.pi^2/(2*a) by positivity)]
  unfold gaussianFrequencyWeight
  exact (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)).trans_eq (by rw [hc]; ring)

/-- The unnormalized reconstructed excess with only the band [-B,B] integrated. -/
def bandGaussianExcess (a T B : ℝ) : ℝ :=
  (Ncount 0 T : ℝ) * ((∫ h in Icc (-B) B,
    reconstructedGapSpectrum T (2 * Real.pi * h * (Real.log T / (2 * Real.pi)))
      (gaussianCollisionAllowance T) * gaussianFrequencyWeight a h) - 1)

/-- Discarded signed Landau power is nonnegative and has an absolute upper bound.
The projection is squared before frequency integration. -/
theorem absolute_gaussian_band_tail {a T B : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T) (hB : 0 ≤ B) :
    0 ≤ absoluteGaussianExcess a T - bandGaussianExcess a T B ∧
      absoluteGaussianExcess a T - bandGaussianExcess a T B ≤
        ((Ncount 0 T : ℝ)+1)^2 * (Real.sqrt 2 * Real.exp (-(Real.pi^2/(2*a))*B^2)) := by
  let n : ℝ := Ncount 0 T
  let b := gaussianCollisionAllowance T
  let u (h : ℝ) := 2 * Real.pi * h * (Real.log T / (2 * Real.pi))
  let F (h : ℝ) := reconstructedGapSpectrum T (u h) b * gaussianFrequencyWeight a h
  let G (h : ℝ) := n * F h
  let s := Icc (-B) B
  let K := (n+1)^2 * (Real.sqrt 2 * Real.exp (-(Real.pi^2/(2*a))*B^2))
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hN
  have hb : 0 ≤ b := gaussianCollisionAllowance_nonneg hN
  have hs : MeasurableSet s := measurableSet_Icc
  have hF : Integrable F := (reconstructed_cosine_gap_test T (Real.log T/(2*Real.pi)) b hb
    (gaussianFrequencyWeight_spec ha).1).1
  have hG : Integrable G := hF.const_mul n
  have hid : absoluteGaussianExcess a T - bandGaussianExcess a T B = ∫ h in sᶜ, G h := by
    have hh := integral_add_compl hs hG
    change n * ((∫ h, F h)-1) - n * ((∫ h in s, F h)-1) = ∫ h in sᶜ, G h
    simp only [G, integral_const_mul] at hh ⊢
    linarith only [hh]
  have hGeq (h : ℝ) : G h = ‖reconstructedOrdinateSum T (u h) (gapReconstructionOrder T (u h) b)‖^2 *
      gaussianFrequencyWeight a h := by
    change n * ((‖reconstructedOrdinateSum T (u h) (gapReconstructionOrder T (u h) b)‖^2 / n) * _) = _
    field_simp [hn.ne']
  have hGpos (h : ℝ) : 0 ≤ G h := by
    rw [hGeq]
    exact mul_nonneg (sq_nonneg _) (frequencyWeight_nonneg _ _)
  have hA (h : ℝ) : ‖reconstructedOrdinateSum T (u h) (gapReconstructionOrder T (u h) b)‖ ≤ n+1 := by
    have he := (abs_norm_sub_norm_le _ _).trans (ordinate_reconstruction_exp_error T (u h) b _
      (gapReconstructionOrder_sufficient T (u h) b))
    have hp := norm_ordinateSum_le_count T (u h)
    change _ ≤ n at hp
    have hdec : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb)
    linarith only [(abs_le.mp he).1, hp, hdec]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have h2 : 0 < 2*a := by positivity
  have hi := (gaussianFrequencyWeight_spec h2).1.const_mul K
  rw [hid]
  refine ⟨integral_nonneg hGpos, ?_⟩
  calc
    (∫ h in sᶜ, G h) ≤ ∫ h in sᶜ, K * gaussianFrequencyWeight (2*a) h := by
      apply integral_mono_of_nonneg (ae_of_all _ hGpos) hi.integrableOn
      apply ae_restrict_of_forall_mem hs.compl
      intro h hh
      have hhb : B ≤ |h| := by
        by_contra! hc
        exact hh (abs_le.mp hc.le)
      rw [hGeq]
      calc
        _ ≤ (n+1)^2 * gaussianFrequencyWeight a h :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hA h) 2)
            (frequencyWeight_nonneg _ _)
        _ ≤ _ := (mul_le_mul_of_nonneg_left (gaussian_frequency_tail_comparison ha hB hhb)
          (sq_nonneg (n+1))).trans_eq (by dsimp [K]; ring)
    _ ≤ ∫ h, K * gaussianFrequencyWeight (2*a) h :=
      setIntegral_le_integral hi (ae_of_all _ fun h => mul_nonneg hK (frequencyWeight_nonneg _ h))
    _ = _ := by rw [integral_const_mul, frequencyWeight_integral h2, mul_one]

/-- An explicit Fourier radius that guarantees at most one quarter of one pair in the tail. -/
def gaussianCollisionFrequencyRadius (a T : ℝ) : ℝ :=
  Real.sqrt ((2*a / Real.pi^2) * Real.log (4 * Real.sqrt 2 * ((Ncount 0 T : ℝ)+1)^2))

theorem calibrated_gaussian_band_tail {a T : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T) :
    0 ≤ absoluteGaussianExcess a T - bandGaussianExcess a T (gaussianCollisionFrequencyRadius a T) ∧
      absoluteGaussianExcess a T - bandGaussianExcess a T (gaussianCollisionFrequencyRadius a T) ≤ 1/4 := by
  let n : ℝ := Ncount 0 T
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hN
  let X := 4 * Real.sqrt 2 * (n+1)^2
  have ht : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le (by linarith only [ht])
    (one_le_pow₀ (by linarith only [hn]) : (1 : ℝ) ≤ (n+1)^2)
  have hB : 0 ≤ gaussianCollisionFrequencyRadius a T := Real.sqrt_nonneg _
  obtain ⟨hl,hu⟩ := absolute_gaussian_band_tail ha hN hB
  refine ⟨hl, hu.trans_eq ?_⟩
  have hcancel : (Real.pi^2/(2*a)) * (gaussianCollisionFrequencyRadius a T)^2 = Real.log X := by
    change (Real.pi^2/(2*a)) * (Real.sqrt ((2*a/Real.pi^2)*Real.log X))^2 = Real.log X
    rw [Real.sq_sqrt (mul_nonneg (by positivity) (Real.log_nonneg hX))]
    field_simp [ha.ne', Real.pi_ne_zero]
  rw [neg_mul, hcancel, Real.exp_neg, Real.exp_log (zero_lt_one.trans_le hX)]
  change (n+1)^2 * (Real.sqrt 2 * (4*Real.sqrt 2*(n+1)^2)⁻¹) = 1/4
  field_simp [(show n+1 ≠ 0 by linarith), (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)).ne']
  <;> ring

/-- The omitted tail lowers the statistic and the unequal-height mass raises it.
With both at most a quarter, the finite-band statistic still has half-unit accuracy. -/
theorem calibrated_gaussian_band_half_error {a T : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T)
    (hu : unequalGaussianTotal a T ≤ 1/4) :
    |bandGaussianExcess a T (gaussianCollisionFrequencyRadius a T) -
      ((actualCollision T : ℝ) - (Ncount 0 T : ℝ))| ≤ 1/2 := by
  obtain ⟨ht0,ht4⟩ := calibrated_gaussian_band_tail ha hN
  obtain ⟨hq1,hq2⟩ := abs_le.mp (absolute_gaussian_quarter_error hN ha)
  have hp := unequalGaussianTotal_nonneg a T
  exact abs_le.mpr ⟨by linarith only [ht4,hq2,hp], by linarith only [ht0,hq1,hu]⟩

/-- The same integer decoder recovers the complete collision count from the bounded band. -/
theorem finite_band_gaussian_recovers_collision {a T δ : ℝ} (hN : 0 < Ncount 0 T)
    (ha : 0 < a) (hδ : 0 < δ) (hprec : Real.log (4 * (Ncount 0 T : ℝ)^2) / δ^2 ≤ a)
    (hsep : ∀ i j : Copies T, copyOrdinate T i ≠ copyOrdinate T j → δ ≤ |gaussianSeparation T i j|) :
    2 * ⌊(bandGaussianExcess a T (gaussianCollisionFrequencyRadius a T)+1)/2⌋₊ =
      actualCollision T - Ncount 0 T :=
  decode_collision_of_half_error (calibrated_gaussian_band_half_error ha hN
    (unequalGaussianTotal_le_quarter hN ha.le hδ hprec hsep))

/-- All orders used by the retained integral are bounded by the order at the band edge. -/
theorem gaussian_order_le_band_edge {T h B b : ℝ} (hT : 1 < T) (hh : |h| ≤ B) :
    gapReconstructionOrder T (h*Real.log T) b ≤ gapReconstructionOrder T (B*Real.log T) b := by
  have hB := (abs_nonneg h).trans hh
  have hlog := Real.log_pos hT
  have hg : |h*Real.log T| ≤ |B*Real.log T| := by
    simpa only [abs_mul, abs_of_nonneg hB, abs_of_pos hlog] using
      mul_le_mul_of_nonneg_right hh hlog.le
  unfold gapReconstructionOrder
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (by linarith only [hg])
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))

/-- The same strict threshold also works for the explicitly bounded integral at finite height. -/
theorem finite_band_gaussian_certificate_iff {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    (∃ k : ℕ, let a : ℝ := (k:ℝ)+1
      bandGaussianExcess a T (gaussianCollisionFrequencyRadius a T) < 1) ↔
      actualCollision T = Ncount 0 T := by
  constructor
  · rintro ⟨k, hk⟩
    let a : ℝ := (k:ℝ)+1
    have ha : 0 < a := by dsimp [a]; positivity
    change bandGaussianExcess a T (gaussianCollisionFrequencyRadius a T) < 1 at hk
    have ht := (calibrated_gaussian_band_tail ha hN).2
    have he := (abs_le.mp (absolute_gaussian_quarter_error hN ha)).2
    have hlt : (actualCollision T : ℝ) < (Ncount 0 T : ℝ)+2 := by
      linarith only [ht, he, hk, unequalGaussianTotal_nonneg a T]
    have hh : actualCollision T < Ncount 0 T + 2 := by exact_mod_cast hlt
    have hsum := actualCollision_eq_count_add_excess T
    obtain ⟨m,hm⟩ := actualCollision_sub_count_even T
    omega
  · intro hc
    obtain ⟨k, hk⟩ := (absolute_gaussian_finite_iff hT hN).mpr hc
    have ht := (calibrated_gaussian_band_tail (T := T) (show 0 < (k:ℝ)+1 by positivity) hN).1
    exact ⟨k, by dsimp only; linarith only [hk,ht]⟩

/-- Cofinal bounded-band arithmetic upper bounds with finitely many horizontal orders settle
global criticality and simplicity. Establishing the upper bound remains open. -/
theorem cofinal_finite_band_gaussian_iff_global :
    (∃ᶠ T : ℝ in atTop, ∃ k : ℕ, let a : ℝ := (k:ℝ)+1
      bandGaussianExcess a T (gaussianCollisionFrequencyRadius a T) < 1) ↔
      RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  rw [← cofinal_absolute_gaussian_iff_global]
  constructor
  · intro h
    apply (h.and_eventually ((eventually_gt_atTop (1:ℝ)).and eventually_count_pos)).mono
    rintro T ⟨hc,ht,hn⟩
    exact (absolute_gaussian_finite_iff ht hn).mpr
      ((finite_band_gaussian_certificate_iff ht hn).mp hc)
  · intro h
    apply (h.and_eventually ((eventually_gt_atTop (1:ℝ)).and eventually_count_pos)).mono
    rintro T ⟨hc,ht,hn⟩
    exact (finite_band_gaussian_certificate_iff ht hn).mpr
      ((absolute_gaussian_finite_iff ht hn).mp hc)

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.cofinal_finite_band_gaussian_iff_global' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_finite_band_gaussian_iff_global

end RiemannResearch.Analysis.ActualZeroOrdinate
