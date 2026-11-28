import RiemannResearch.Analysis.GaussianCollisionTranslatedBand
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.RationalLandauInghamTangent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # A signed Gaussian collision test outside a prescribed central interval

The Gaussian precision can depend on the cutoff. The mass of a prescribed
central frequency interval can therefore be made smaller than a quarter-pair.
The remaining signed integral is over a bounded annulus with both endpoints
specified before evaluating it. For the Ingham tangent take the inner radius
to be 4/3. The rational Landau input has the additional numerator constraint
in `RationalLandauMovingBand`. For the arithmetic formula see Ford, Meng and
Zaharescu, Lemma 1, <https://arxiv.org/abs/1511.06814>. Their equation (1.2)
records the Riemann–von Mangoldt estimate underlying the local zero-count bound.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ActualZeroCollisionCertificate OrdinateCollisionCertificate

/-- Absolute pointwise upper bound from the true occurrence amplitude and the signed error. -/
theorem reconstructed_collision_spectrum_le {T : ℝ} (hN : 0 < Ncount 0 T) (u : ℝ) :
    (Ncount 0 T : ℝ) * reconstructedGapSpectrum T u (gaussianCollisionAllowance T) ≤
      (Ncount 0 T : ℝ)^2 + 1/4 := by
  let n : ℝ := Ncount 0 T
  let b := gaussianCollisionAllowance T
  have hn : 0 < n := by dsimp [n]; exact_mod_cast hN
  have htrue : n * fullGapSpectrum T u = ‖ordinateSum T u‖^2 := by
    rw [fullGapSpectrum, ← occurrenceAmplitude_normSq, actual_occurrenceAmplitude,
      Complex.normSq_eq_norm_sq]
    change n * (_ / n) = _
    rw [div_eq_mul_inv, mul_left_comm n, mul_inv_cancel₀ hn.ne', mul_one]
  have he := (abs_le.mp (fullGapSpectrum_sub_reconstructed_le T u b
    (gaussianCollisionAllowance_nonneg hN))).1
  have he' := mul_le_mul_of_nonneg_left he hn.le
  have hq : 3*n*Real.exp (-b) = 1/4 := gaussianCollisionAllowance_error hN
  have hs := pow_le_pow_left₀ (norm_nonneg _) (norm_ordinateSum_le_count T u) 2
  change ‖ordinateSum T u‖^2 ≤ n^2 at hs
  change n * reconstructedGapSpectrum T u b ≤ n^2 + 1/4
  nlinarith only [he', hq, htrue, hs]

/-- The reconstructed integral over the central interval, in ordered-pair units. -/
theorem central_gaussian_band_power_bounds {a T H : ℝ} (ha : 0 < a)
    (hN : 0 < Ncount 0 T) (hH : 0 ≤ H) :
    0 ≤ bandGaussianExcess a T H + (Ncount 0 T : ℝ) ∧
      bandGaussianExcess a T H + (Ncount 0 T : ℝ) ≤
        2*H*((Ncount 0 T : ℝ)^2+1/4)*Real.sqrt (Real.pi/a) := by
  let n : ℝ := Ncount 0 T
  let L := Real.log T/(2*Real.pi)
  let b := gaussianCollisionAllowance T
  let u (h : ℝ) := 2*Real.pi*h*L
  let R (h : ℝ) := reconstructedGapSpectrum T (u h) b
  let w := gaussianFrequencyWeight a
  let S := Icc (-H) H
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hK : 0 ≤ n^2+1/4 := by positivity
  have hw (h : ℝ) : 0 ≤ w h := by dsimp [w, gaussianFrequencyWeight]; positivity
  have hR (h : ℝ) : 0 ≤ R h := div_nonneg (sq_nonneg _) hn
  have hi := (gaussianFrequencyWeight_spec ha).1
  have hid : bandGaussianExcess a T H + n = ∫ h in S, n * (R h * w h) := by
    rw [integral_const_mul]
    change n*((∫ h in S, R h*w h)-1) + n = _
    ring
  have hmass : (∫ h in S, w h) ≤ 2*H*Real.sqrt (Real.pi/a) := by
    rw [show S = Icc (-H) H by rfl, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (neg_le_self hH)]
    exact gaussianFrequencyWeight_band_mass_le ha hH
  rw [hid]
  refine ⟨integral_nonneg (fun h => mul_nonneg hn (mul_nonneg (hR h) (hw h))), ?_⟩
  calc
    _ ≤ ∫ h in S, (n^2+1/4)*w h := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun h => mul_nonneg hn (mul_nonneg (hR h) (hw h)))
        (hi.const_mul (n^2+1/4)).integrableOn
      exact ae_of_all _ fun h => by
        change n*(R h*w h) ≤ (n^2+1/4)*w h
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (reconstructed_collision_spectrum_le hN (u h)) (hw h)
    _ = (n^2+1/4) * ∫ h in S, w h := integral_const_mul _ _
    _ ≤ (n^2+1/4) * (2*H*Real.sqrt (Real.pi/a)) := mul_le_mul_of_nonneg_left hmass hK
    _ = _ := by dsimp only [n]; ring


/-- The reference width π² is controlled by the local multiplicity count.
The comparison is termwise and keeps the full collision mass. -/
theorem exists_gaussian_reference_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      translatedGaussianPairPower (Real.pi^2) T 0 ≤ C*(Ncount 0 T : ℝ)*Real.log (T+3) := by
  obtain ⟨C, hC, hrow⟩ := MontgomeryLocalMass.exists_actual_cauchy_row_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (0 : ℝ),
    eventually_count_pos] with T hlog hT hN
  have hterm (i j : Copies T) : Real.exp (-(Real.pi^2)*(gaussianSeparation T i j)^2) ≤
      MontgomeryPoisson.cauchyWeight (copyOrdinate T i-copyOrdinate T j) := by
    let y := copyOrdinate T i-copyOrdinate T j
    let v := (Real.log T)^2*y^2/4
    have hv : Real.pi^2*(gaussianSeparation T i j)^2 = v := by
      dsimp [gaussianSeparation, v, y]
      field_simp [Real.pi_ne_zero]
      ring
    rw [neg_mul, hv, Real.exp_neg, ← one_div]
    change 1 / Real.exp v ≤ 4/(4+y^2)
    rw [div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    have hsq := mul_le_mul_of_nonneg_right (one_le_pow₀ hlog (n := 2)) (sq_nonneg y)
    have he := Real.add_one_le_exp v
    dsimp only [v] at he
    linarith only [he, hsq]
  rw [translatedGaussianPairPower_eq (by positivity) hN]
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  calc
    _ ≤ ∑ _i : Copies T, C * Real.log (T+3) :=
      Finset.sum_le_sum fun i _ => (Finset.sum_le_sum fun j _ => hterm i j).trans
        (hrow T hT (copyOrdinate T i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_copies]
      ring

private theorem gaussianWeight_le_reference {a H h : ℝ} (ha : 0 < a) (hh : |h| ≤ H) :
    gaussianFrequencyWeight a h ≤ (Real.pi/Real.sqrt a * Real.exp (H^2)) *
      gaussianFrequencyWeight (Real.pi^2) h := by
  have hroot : (Real.pi/Real.sqrt a) * Real.sqrt (Real.pi/Real.pi^2) =
      Real.sqrt (Real.pi/a) := by
    simp only [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq Real.pi_pos.le]
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr ha).ne']
  have hh2 := pow_le_pow_left₀ (abs_nonneg h) hh 2
  rw [sq_abs] at hh2
  have he : Real.exp (-(Real.pi^2/a)*h^2) ≤ Real.exp (H^2)*Real.exp (-(h^2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by
      linarith only [hh2, mul_nonneg (show 0 ≤ Real.pi^2/a by positivity) (sq_nonneg h)])
  unfold gaussianFrequencyWeight
  rw [div_self (pow_ne_zero _ Real.pi_ne_zero), neg_one_mul]
  calc
    _ ≤ Real.sqrt (Real.pi/a) * (Real.exp (H^2)*Real.exp (-(h^2))) :=
      mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
    _ = _ := by rw [← hroot]; ring

/-- The reference Gaussian gives the central integral an upper bound of order
N log(T+3) / √a at each fixed inner radius. -/
theorem exists_central_gaussian_band_local_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ a H : ℝ, 0 < a → 0 ≤ H →
      bandGaussianExcess a T H + (Ncount 0 T : ℝ) ≤
        (Real.pi/Real.sqrt a * Real.exp (H^2)) *
          (C*(Ncount 0 T : ℝ)*Real.log (T+3)+1/4) := by
  obtain ⟨C,hC,hP⟩ := exists_gaussian_reference_power_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [hP, eventually_count_pos] with T hP hN
  intro a H ha _hH
  let n : ℝ := Ncount 0 T
  let b := gaussianCollisionAllowance T
  let L := Real.log T/(2*Real.pi)
  let R (h : ℝ) := reconstructedGapSpectrum T (2*Real.pi*h*L) b
  let w := gaussianFrequencyWeight (Real.pi^2)
  let f (h : ℝ) := R h * w h
  let k := Real.pi/Real.sqrt a * Real.exp (H^2)
  let S := Icc (-H) H
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hR (h : ℝ) : 0 ≤ R h := div_nonneg (sq_nonneg _) hn
  have hw (z h : ℝ) : 0 ≤ gaussianFrequencyWeight z h := by
    unfold gaussianFrequencyWeight
    positivity
  have hi : Integrable f := (reconstructed_cosine_gap_test T L b
    (gaussianCollisionAllowance_nonneg hN) (gaussianFrequencyWeight_spec (by positivity)).1).1
  have hdom : (∫ h in S, R h * gaussianFrequencyWeight a h) ≤ k * ∫ h, f h := by
    calc
      _ ≤ ∫ h in S, k * f h := by
        apply integral_mono_of_nonneg (ae_of_all _ fun h => mul_nonneg (hR h) (hw a h))
          (hi.const_mul k).integrableOn
        apply ae_restrict_of_forall_mem (show MeasurableSet S from measurableSet_Icc)
        intro h hh
        have hh' : |h| ≤ H := abs_le.mpr hh
        exact (mul_le_mul_of_nonneg_left (gaussianWeight_le_reference ha hh') (hR h)).trans_eq
          (by dsimp only [f, w, k]; ring)
      _ ≤ ∫ h, k * f h := setIntegral_le_integral (hi.const_mul k)
        (ae_of_all _ fun h => mul_nonneg hk (mul_nonneg (hR h) (hw _ h)))
      _ = _ := integral_const_mul _ _
  have hbase : n*(∫ h, f h) ≤ translatedGaussianPairPower (Real.pi^2) T 0 + 1/4 := by
    have he := (abs_le.mp (absolute_gaussian_quarter_error (a := Real.pi^2) hN (by positivity))).1
    rw [translatedGaussianPairPower_zero (by positivity) hN]
    have hid : n*(∫ h, f h) = absoluteGaussianExcess (Real.pi^2) T + n := by
      change n*(∫ h, f h) = n*((∫ h, f h)-1)+n
      ring
    rw [hid]
    dsimp [n]
    linarith only [he]
  calc
    _ = n*(∫ h in S, R h * gaussianFrequencyWeight a h) := by
      change n*((∫ h in S, R h * gaussianFrequencyWeight a h)-1)+n = _
      ring
    _ ≤ n*(k*∫ h, f h) := mul_le_mul_of_nonneg_left hdom hn
    _ = k*(n*∫ h, f h) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbase.trans (add_le_add hP (le_refl (1/4 : ℝ)))) hk

/-- Unnormalized reconstructed power on H < |h| ≤ B, with the frequency-dependent
horizontal moments included before taking the squared modulus. -/
def outerGaussianPower (a T H : ℝ) : ℝ :=
  let B := relativeGaussianCollisionRadius a T
  (Ncount 0 T : ℝ) * ∫ h in Icc (-B) B \ Icc (-H) H, reconstructedGapSpectrum T
    (2*Real.pi*h*(Real.log T/(2*Real.pi))) (gaussianCollisionAllowance T) *
    gaussianFrequencyWeight a h

/-- Exact partition of the signed reconstructed power into its central and outer integrals. -/
theorem outerGaussianPower_eq_sub {a T H : ℝ} (ha : 0 < a) (hN : 0 < Ncount 0 T)
    (hHB : H ≤ relativeGaussianCollisionRadius a T) :
    outerGaussianPower a T H = bandGaussianExcess a T (relativeGaussianCollisionRadius a T) -
      bandGaussianExcess a T H := by
  let B := relativeGaussianCollisionRadius a T
  let s := Icc (-B) B
  let t := Icc (-H) H
  let L := Real.log T/(2*Real.pi)
  let b := gaussianCollisionAllowance T
  let f (h : ℝ) := reconstructedGapSpectrum T (2*Real.pi*h*L) b * gaussianFrequencyWeight a h
  let n : ℝ := Ncount 0 T
  have hi : Integrable f := (reconstructed_cosine_gap_test T L b
    (gaussianCollisionAllowance_nonneg hN) (gaussianFrequencyWeight_spec ha).1).1
  have hsub : t ⊆ s := Icc_subset_Icc (neg_le_neg hHB) hHB
  have hd : Disjoint t (s \ t) := Set.disjoint_left.mpr fun _ hx hy => hy.2 hx
  have hm : MeasurableSet (s \ t) := measurableSet_Icc.diff measurableSet_Icc
  have hu : t ∪ (s \ t) = s := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hsub hx
      · exact hx.1
    · intro hx
      by_cases hxt : x ∈ t
      · exact Or.inl hxt
      · exact Or.inr ⟨hx,hxt⟩
  have hs := setIntegral_union (f := f) hd hm hi.integrableOn hi.integrableOn
  rw [hu] at hs
  change n * (∫ h in s \ t, f h) =
    n*((∫ h in s, f h)-1) - n*((∫ h in t, f h)-1)
  rw [hs]
  ring

/-- With central power at most D / √a, the only energy to estimate in this test
is the reconstructed integral on H < |h| ≤ B. -/
def OuterGaussianCertificate (T H D : ℝ) : Prop :=
  ∃ k : ℕ, let a : ℝ := (k:ℝ)+1
    H ≤ relativeGaussianCollisionRadius a T ∧
      D / Real.sqrt a ≤ 1/4 ∧
      outerGaussianPower a T H < (Ncount 0 T : ℝ) + 3/4

/-- A central bound suffices at finite height. The local zero-count bound
supplies its coefficient unconditionally at all sufficiently high cutoffs. -/
theorem outer_gaussian_certificate_iff {T H D : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T)
    (hH : 0 ≤ H) (hcentral : ∀ a : ℝ, 0 < a →
      bandGaussianExcess a T H + (Ncount 0 T : ℝ) ≤ D / Real.sqrt a) :
    OuterGaussianCertificate T H D ↔ actualCollision T = Ncount 0 T := by
  let n : ℝ := Ncount 0 T
  constructor
  · rintro ⟨k, hHB, hcost, ho⟩
    let a : ℝ := (k:ℝ)+1
    have ha : 0 < a := by dsimp [a]; positivity
    have hinner := (hcentral a ha).trans hcost
    have hsplit := outerGaussianPower_eq_sub ha hN hHB
    apply (relative_band_gaussian_certificate_iff hT hN).mp
    refine ⟨k, ?_⟩
    change bandGaussianExcess a T (relativeGaussianCollisionRadius a T) < 1
    change outerGaussianPower a T H < (Ncount 0 T : ℝ)+3/4 at ho
    linarith only [hinner, hsplit, ho]
  · intro hc
    have hlim : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1)
    have hU : Tendsto (fun k : ℕ => unequalGaussianTotal ((k:ℝ)+1) T) atTop (𝓝 0) := by
      simpa only [unequalGaussianTotal, mul_zero] using
        (MontgomeryPositiveGap.unequalGaussian_tendsto_zero_at_fixed_height hT).const_mul n
    have hcost : Tendsto (fun k : ℕ => D / Real.sqrt ((k:ℝ)+1)) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp hlim).const_div_atTop D
    let l := Real.log (8*(n+2)/3)
    have hn : 0 ≤ n := Nat.cast_nonneg _
    have hl : 0 < l := Real.log_pos (by linarith)
    have hB : ∀ᶠ k : ℕ in atTop, H ≤ relativeGaussianCollisionRadius ((k:ℝ)+1) T := by
      filter_upwards [hlim.eventually_ge_atTop (H^2*Real.pi^2/l)] with k hk
      have hm := (div_le_iff₀ hl).mp hk
      apply Real.le_sqrt_of_sq_le
      change H^2 ≤ ((k:ℝ)+1)/Real.pi^2*l
      rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
      exact hm
    have good := ((hU.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).and
      (hcost.eventually_le_const (by norm_num : (0:ℝ)<1/4))).and hB
    obtain ⟨k, ⟨hu, hcost'⟩, hB'⟩ := good.exists
    let a : ℝ := (k:ℝ)+1
    have ha : 0 < a := by dsimp [a]; positivity
    refine ⟨k, hB', hcost', ?_⟩
    have hsplit := outerGaussianPower_eq_sub ha hN hB'
    have hinner := (central_gaussian_band_power_bounds ha hN hH).1
    have hband := (absolute_gaussian_band_tail (a := a) (B := relativeGaussianCollisionRadius a T)
      ha hN (Real.sqrt_nonneg _)).1
    have he := (abs_le.mp (absolute_gaussian_quarter_error hN ha)).1
    rw [hc] at he
    change unequalGaussianTotal a T < 1/2 at hu
    change outerGaussianPower a T H < (Ncount 0 T : ℝ)+3/4
    linarith only [hsplit, hinner, hband, he, hu]

/-- There is an absolute local-count constant such that, outside any prescribed
central window, the displayed arithmetic test is equivalent to RH and simplicity. -/
theorem cofinal_outer_gaussian_iff_global :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ → ℝ, (∀ᶠ T in atTop, 0 ≤ H T) →
      ((∃ᶠ T : ℝ in atTop, OuterGaussianCertificate T (H T)
        (Real.pi*Real.exp ((H T)^2)*(C*(Ncount 0 T : ℝ)*Real.log (T+3)+1/4))) ↔
        RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1) := by
  obtain ⟨C,hC,hlocal⟩ := exists_central_gaussian_band_local_count_bound
  refine ⟨C,hC,?_⟩
  intro H hH
  rw [← cofinal_relative_band_gaussian_iff_global]
  let D (T : ℝ) := Real.pi*Real.exp ((H T)^2)*(C*(Ncount 0 T : ℝ)*Real.log (T+3)+1/4)
  have heq : ∀ᶠ T : ℝ in atTop, OuterGaussianCertificate T (H T) (D T) ↔
      ∃ k : ℕ, let a : ℝ := (k:ℝ)+1
        bandGaussianExcess a T (relativeGaussianCollisionRadius a T) < 1 := by
    filter_upwards [hlocal, eventually_gt_atTop (1 : ℝ), eventually_count_pos, hH]
      with T hbound ht hn hh
    rw [relative_band_gaussian_certificate_iff ht hn]
    apply outer_gaussian_certificate_iff ht hn hh
    intro a ha
    exact (hbound a (H T) ha hh).trans_eq (by dsimp only [D]; ring)
  constructor
  · intro h
    exact (h.and_eventually heq).mono (fun _ hp => hp.2.mp hp.1)
  · intro h
    exact (h.and_eventually heq).mono (fun _ hp => hp.2.mpr hp.1)

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.cofinal_outer_gaussian_iff_global' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_outer_gaussian_iff_global

end RiemannResearch.Analysis.ActualZeroOrdinate
