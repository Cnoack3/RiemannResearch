import RiemannResearch.Analysis.ActualZeroCauchyDensity
import RiemannResearch.Analysis.ActualFixedFrequencyLandau
import RiemannResearch.Analysis.ActualRationalFMZRate
import RiemannResearch.Analysis.ActualZeroHorizontalMomentRate
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-!
# Quantitative horizontal concentration of the actual zeta zeros

Combine the repository's Cauchy density estimate with the total zero count.
The resulting exponential tail has prefactor of order T log T and decay of
order log T / log log T. Reflection then bounds the ordinate-to-Landau
transfer uniformly over a growing band of real frequencies.

The reflection and tail integration follow Ford and Zaharescu,
*On the distribution of imaginary parts of zeros of the Riemann zeta
function*, (3.8), https://arxiv.org/abs/math/0405459.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Height-normalized scale for the Cauchy-density second moment. -/
def horizontalLogRate (T : ℝ) : ℝ :=
  (Real.log (Real.log T)) ^ 2 / Real.log T

/-- Effective exponential decay after using the total count on the central strip. -/
def horizontalTailDecay (T : ℝ) : ℝ :=
  Real.log T / (8 * Real.log (Real.log T))

/-- A single density envelope with the prefactor of the total zero count.
All positive-height zeros are counted with analytic multiplicity. -/
theorem eventually_rightStrictTail_loglog_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ K * T * Real.log T * Real.exp (-(horizontalTailDecay T) * t) := by
  obtain ⟨A,hA,hcount⟩ := exists_count_le_height_log
  obtain ⟨B,hB,htail⟩ := rightTailProfile_of_uniformLogLossDensity _ _
    uniformLogLossDensity_quarter_four
  let K := A * Real.exp 3 + B
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [htail, eventually_ge_atTop (9 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with T hd hT hll
  intro t ht
  let L := Real.log T
  let l := Real.log L
  change 1 ≤ l at hll
  have hL : 0 < L := Real.log_pos (by linarith)
  have hl : 0 < l := by linarith
  have hTp : 0 < T := by linarith
  have hdec : horizontalTailDecay T = L / (8*l) := rfl
  have hdle : horizontalTailDecay T ≤ L/8 := by
    rw [hdec]
    apply div_le_div_of_nonneg_left hL.le (by norm_num) (by linarith)
  have hK1 : A * Real.exp 3 ≤ K := by dsimp [K]; linarith
  have hK2 : B ≤ K := by dsimp [K]; linarith [mul_nonneg hA.le (Real.exp_pos 3).le]
  by_cases hs : L/8*t ≤ 3*l
  · have hdt : horizontalTailDecay T * t ≤ 3 := by
      rw [hdec, div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 8*l)]
      linarith
    have he := Real.exp_le_exp.mpr hdt
    have hN : rightStrictTail T t ≤ A*T*L :=
      (rightStrictTail_le_inclusive T t).trans
        ((rightInclusiveCount_le_count _ _).trans (hcount T hT))
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    calc
      _ ≤ (A*T*L) * Real.exp 3 := mul_le_mul hN he (Real.exp_pos _).le (by positivity)
      _ = (A*Real.exp 3)*T*L := by ring
      _ ≤ _ := by gcongr
  · have hpow : L^4 = L * Real.exp (3*l) := by
      rw [show (3:ℝ)*l = (3:ℕ)*l by norm_num, Real.exp_nat_mul, Real.exp_log hL]
      ring
    have hx : 3*l + -(1/4*L)*t ≤ -(horizontalTailDecay T)*t := by
      nlinarith only [le_of_not_ge hs, mul_le_mul_of_nonneg_right hdle ht.1]
    have hb := hd.2 t ht
    change rightStrictTail T t ≤ B*T*L^(4:ℝ)*Real.exp (-(1/4*L)*t) at hb
    rw [show L^(4:ℝ) = L^4 by norm_cast, hpow] at hb
    calc
      _ ≤ _ := hb
      _ = (B*T*L)*Real.exp (3*l + -(1/4*L)*t) := by rw [Real.exp_add]; ring
      _ ≤ (K*T*L)*Real.exp (-(horizontalTailDecay T)*t) := by
        apply mul_le_mul _ (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (by positivity)
        gcongr

/-- Unconditional second-moment rate. -/
theorem horizontalEnergy_div_height_isBigO_loglog_sq_div_log :
    Asymptotics.IsBigO atTop (fun T : ℝ => horizontalEnergy T / T) horizontalLogRate := by
  obtain ⟨K,hK,htail⟩ := eventually_rightStrictTail_loglog_bound
  refine Asymptotics.IsBigO.of_bound (256*K) ?_
  filter_upwards [htail, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with T ht hT hl
  have hTp : 0 < T := by linarith
  have hL := Real.log_pos hT
  have hD : 0 < horizontalTailDecay T := by unfold horizontalTailDecay; positivity
  have h := horizontalEnergy_le_of_exponential_strictTail T (2*(K*T*Real.log T))
    (horizontalTailDecay T) (by positivity) hD (fun t hmem => by
      rw [strictTail_eq_twice_right T t hmem.1]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (ht t hmem) (by norm_num : (0:ℝ) ≤ 2))
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (horizontalEnergy_nonneg T) hTp.le),
    Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ horizontalLogRate T by unfold horizontalLogRate; positivity)]
  calc
    _ ≤ (2 * (2*(K*T*Real.log T)) / (horizontalTailDecay T)^2) / T :=
      div_le_div_of_nonneg_right h hTp.le
    _ = _ := by unfold horizontalTailDecay horizontalLogRate; field_simp <;> ring

/-- Uniform throughout the indicated band, including moving and negative frequencies. -/
theorem eventually_ordinate_landau_loglog_band :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ,
      |u| ≤ horizontalTailDecay T / 2 →
      ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤ K * u^2 * horizontalLogRate T := by
  obtain ⟨K,hK,htail⟩ := eventually_rightStrictTail_loglog_bound
  refine ⟨(512/3)*K,by positivity,?_⟩
  filter_upwards [htail, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with T ht hT hl
  have hTp : 0 < T := by linarith
  have hL := Real.log_pos hT
  intro u hu
  have hD : 0 < horizontalTailDecay T := by unfold horizontalTailDecay; positivity
  have hb := normalized_ordinate_landau_error_of_right_expTail_band T u (K*T*Real.log T)
    (horizontalTailDecay T) (1/2) hTp (by positivity) hD (by norm_num) (by norm_num)
    (by linarith : |u| ≤ (1/2)*horizontalTailDecay T) ht
  refine hb.trans (le_of_eq ?_)
  unfold horizontalTailDecay horizontalLogRate
  field_simp <;> ring

theorem horizontalLogRate_tendsto_zero :
    Tendsto horizontalLogRate atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
  simp only [horizontalLogRate, Function.comp_def, Real.exp_neg, Real.exp_log hT, div_eq_mul_inv]

/-- A moving frequency needs only its squared frequency times the rate to go
to zero. This condition automatically places it in the transfer band. -/
theorem tendsto_ordinate_landau_of_moving_loglog (u : ℝ → ℝ)
    (hu : Tendsto (fun T => (u T)^2 * horizontalLogRate T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (ordinateSum T (u T) - landauSum T (u T)) / (T : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨K,hK,hband⟩ := eventually_ordinate_landau_loglog_band
  apply squeeze_zero_norm' _ (by simpa using hu.const_mul K)
  filter_upwards [hband, hu.eventually_le_const (by norm_num : (0:ℝ)<1),
    Real.tendsto_log_atTop.eventually_ge_atTop 256,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with T hb hsmall hbig hl
  let L := Real.log T
  let l := Real.log L
  change 256 ≤ L at hbig
  change 0 < l at hl
  have hL : 0 < L := by linarith
  change (u T)^2 * (l^2/L) ≤ 1 at hsmall
  rw [← mul_div_assoc, div_le_iff₀ hL, one_mul] at hsmall
  have hs : (|u T| * (8*l*2))^2 ≤ L^2 := by
    calc
      _ = 256 * ((u T)^2 * l^2) := by rw [mul_pow, sq_abs]; ring
      _ ≤ 256*L := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg hL.le (sub_nonneg.mpr hbig)]
  have hfreq : |u T| ≤ horizontalTailDecay T / 2 := by
    change |u T| ≤ L / (8*l) / 2
    rw [div_div,le_div_iff₀ (by positivity : 0 < 8*l*2)]
    exact (sq_le_sq₀ (by positivity) hL.le).mp hs
  simpa only [mul_assoc] using hb (u T) hfreq

private theorem contourRate_isBigO_horizontalLogRate :
    Asymptotics.IsBigO atTop (fun T : ℝ => (Real.log (T+3))^2 / T) horizontalLogRate := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    (shifted_log_pow_div_self_tendsto_zero 3).eventually_le_const (by norm_num : (0:ℝ)<1)]
    with T hT hl hc
  have hTp : 0 < T := by linarith
  have hL := Real.log_pos hT
  have hlog := Real.log_le_log hTp (by linarith : T ≤ T+3)
  have h3 := (div_le_iff₀ hTp).mp hc
  have hsq : 1 ≤ (Real.log (Real.log T))^2 := one_le_pow₀ (show 1 ≤ Real.log (Real.log T) from hl)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hTp.le),
    Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ horizontalLogRate T by unfold horizontalLogRate; positivity),
    one_mul]
  calc
    _ ≤ 1 / Real.log T := (div_le_div_iff₀ hTp hL).mpr (by
      nlinarith only [h3, mul_le_mul_of_nonneg_left hlog (sq_nonneg (Real.log (T+3)))])
    _ ≤ _ := div_le_div_of_nonneg_right hsq hL.le

/-- Any identified centered fixed-frequency main term has the same main term
for actual ordinates with the unconditional loglog-squared error. -/
theorem fixed_ordinate_remainder_isBigO_horizontalLogRate {u : ℝ} {m : ℂ} (hu : 0 < u)
    (hm : Tendsto (fun T : ℝ => landauSum T u / (T : ℂ)) atTop (𝓝 m)) :
    Asymptotics.IsBigO atTop (fun T : ℝ => ordinateSum T u / (T : ℂ) - m) horizontalLogRate := by
  have href : Asymptotics.IsBigO atTop
      (fun T : ℝ => (ordinateSum T u - landauSum T u) / (T : ℂ))
      (fun T : ℝ => horizontalEnergy T / T) := by
    refine Asymptotics.IsBigO.of_bound (u^2 * Real.exp (|u|/2)) ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (horizontalEnergy_nonneg T) hT.le), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (ordinate_landau_error T u) hT.le
  have h := (href.trans horizontalEnergy_div_height_isBigO_loglog_sq_div_log).add
    ((fixed_landau_remainder_isBigO_log_sq hu hm).trans contourRate_isBigO_horizontalLogRate)
  apply h.congr' _ Filter.EventuallyEq.rfl
  exact Eventually.of_forall fun T => by dsimp; ring

/-- Both error terms are uniform in rational frequencies inside the stated
bands. Numerator size controls the contour and the actual frequency controls
the horizontal displacement. -/
theorem eventually_rational_ordinate_loglog_band :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ, 1 ≤ m → m < n →
      Real.log (n : ℝ) ≤ Real.log T / 8 →
      Real.log ((n : ℝ)/m) ≤ horizontalTailDecay T / 2 →
      ‖ordinateSum T (Real.log ((n : ℝ)/m)) / (T : ℂ) + (rationalLandauMain n m : ℂ)‖ ≤
        K * (1 / Real.log T + (Real.log ((n : ℝ)/m))^2 * horizontalLogRate T) := by
  obtain ⟨A,hA,ha⟩ := eventually_rational_landau_error_le_inv_log
  obtain ⟨B,hB,hb⟩ := eventually_ordinate_landau_loglog_band
  refine ⟨A+B,add_pos hA hB,?_⟩
  filter_upwards [ha,hb,eventually_gt_atTop (1:ℝ)] with T ha hb hT
  intro n m hm hmn hN hband
  let u := Real.log ((n:ℝ)/m)
  have hu : 0 < u := (rational_frequency_bounds hm hmn (le_refl (n:ℝ))).1
  have hTp : 0 < T := by linarith
  have hTc := Complex.ofReal_ne_zero.mpr hTp.ne'
  have hL := Real.log_pos hT
  have hr : 0 ≤ horizontalLogRate T := by unfold horizontalLogRate; positivity
  have h1 := ha n m hm hmn hN
  have h2 := hb u (by rw [abs_of_pos hu]; exact hband)
  have he : ordinateSum T u / (T:ℂ) + (rationalLandauMain n m : ℂ) =
      (ordinateSum T u - landauSum T u)/(T:ℂ) +
      (landauSum T u + ((T*rationalLandauMain n m : ℝ):ℂ))/(T:ℂ) := by
    push_cast
    field_simp
    ring
  change ‖ordinateSum T u / (T:ℂ) + (rationalLandauMain n m : ℂ)‖ ≤ _
  rw [he]
  refine (norm_add_le _ _).trans ((add_le_add h2 h1).trans ?_)
  change B*u^2*horizontalLogRate T + A/Real.log T ≤ (A+B)*(1/Real.log T + u^2*horizontalLogRate T)
  have hn1 : 0 ≤ A * (u^2 * horizontalLogRate T) := by positivity
  have hn2 : 0 ≤ B * (Real.log T)⁻¹ := by positivity
  simp only [div_eq_mul_inv] at *
  nlinarith

/-- The unconditional two-band estimate extends to every rational mode.
Outside the bands, squared logarithmic height already pays for the full
ordinate count and for the signed arithmetic main term. -/
theorem eventually_rational_ordinate_remainder_loglog :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ, 1 ≤ m → m < n →
      ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) +
        (rationalLandauMain n m : ℂ)‖ ≤
        (K * horizontalLogRate T) * (1 + Real.log (n : ℝ)) ^ 2 := by
  obtain ⟨B, hB, hband⟩ := eventually_rational_ordinate_loglog_band
  obtain ⟨C, hC, hcount⟩ := exists_normalized_ordinate_bound
  refine ⟨B + 256 * C + 16, by positivity, ?_⟩
  filter_upwards [hband, eventually_ge_atTop (9 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with T hb hT hℓ
  intro n m hm hmn
  let L := Real.log T
  let ℓ := Real.log L
  let H := Real.log (n : ℝ)
  let u := Real.log ((n : ℝ) / (m : ℝ))
  change 1 ≤ ℓ at hℓ
  have hL : 0 < L := Real.log_pos (by linarith)
  have hℓ₀ : 0 < ℓ := by linarith
  have hu := rational_frequency_bounds hm hmn (le_refl (n : ℝ))
  change 0 < u ∧ u ≤ H ∧ _ at hu
  have hH : 0 ≤ H := hu.1.le.trans hu.2.1
  have hr : 0 ≤ horizontalLogRate T := by unfold horizontalLogRate; positivity
  have hweight : 0 ≤ (1 + H) ^ 2 := sq_nonneg _
  change ‖ordinateSum T u / (T : ℂ) + (rationalLandauMain n m : ℂ)‖ ≤ _
  by_cases hsmall : H ≤ L / 8 ∧ u ≤ horizontalTailDecay T / 2
  · have h1 : 1 / L ≤ horizontalLogRate T := by
      exact div_le_div_of_nonneg_right (one_le_pow₀ hℓ) hL.le
    have hsq : 1 + u ^ 2 ≤ (1 + H) ^ 2 := by
      nlinarith [pow_le_pow_left₀ hu.1.le hu.2.1 2]
    calc
      _ ≤ B * (1 / L + u ^ 2 * horizontalLogRate T) := hb n m hm hmn hsmall.1 hsmall.2
      _ ≤ B * ((1 + u ^ 2) * horizontalLogRate T) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        rw [add_mul, one_mul]
        exact add_le_add h1 le_rfl
      _ ≤ (B * horizontalLogRate T) * (1 + H) ^ 2 := by
        simpa only [mul_left_comm, mul_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hr) hB.le
      _ ≤ _ := by gcongr; linarith
  · have hcut : L / (16 * ℓ) ≤ H := by
      by_contra! h
      apply hsmall
      constructor
      · exact h.le.trans (div_le_div_of_nonneg_left hL.le (by norm_num) (by linarith))
      · have hd : horizontalTailDecay T / 2 = L / (16 * ℓ) := by
          unfold horizontalTailDecay
          dsimp [L, ℓ]
          ring
        rw [hd]
        exact hu.2.1.trans h.le
    have hcross : L ≤ 16 * (ℓ * H) := by
      have hh := (div_le_iff₀ (show 0 < 16 * ℓ by positivity)).mp hcut
      linarith only [hh]
    have hLH : L ^ 2 ≤ 256 * (ℓ * H) ^ 2 := by
      nlinarith only [pow_le_pow_left₀ hL.le hcross 2]
    have hlin : H * L ≤ 16 * (ℓ * H) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hcross hH
      have hi := mul_le_mul_of_nonneg_right hℓ (show 0 ≤ ℓ * H ^ 2 by positivity)
      nlinarith only [hh, hi]
    have hmain : ‖(rationalLandauMain n m : ℂ)‖ ≤ H := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rationalLandauMain_nonneg n m)]
      exact rationalLandauMain_le_log hm hmn
    have hscale : C * L + H ≤ ((256 * C + 16) * horizontalLogRate T) * H ^ 2 := by
      change C * L + H ≤ ((256 * C + 16) * (ℓ ^ 2 / L)) * H ^ 2
      rw [show ((256 * C + 16) * (ℓ ^ 2 / L)) * H ^ 2 =
        (256 * C + 16) * (ℓ * H) ^ 2 / L by ring, le_div_iff₀ hL]
      nlinarith only [mul_le_mul_of_nonneg_left hLH hC.le, hlin]
    calc
      _ ≤ ‖ordinateSum T u / (T : ℂ)‖ + ‖(rationalLandauMain n m : ℂ)‖ := norm_add_le _ _
      _ ≤ C * L + H := add_le_add (hcount T u hT) hmain
      _ ≤ _ := hscale.trans (by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hr)
        · nlinarith
        · positivity
        · positivity)

/-- Exact diagonal centering and conjugation extend the unconditional bound
to all positive numerator and denominator pairs. -/
theorem eventually_centeredRationalOrdinate_remainder_loglog :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      ‖centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m‖ ≤
        (K * horizontalLogRate T) * rationalModeWeight n m ^ 2 := by
  obtain ⟨K, hK, hb⟩ := eventually_rational_ordinate_remainder_loglog
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT₁
  have hscale : 0 ≤ horizontalLogRate T := div_nonneg (sq_nonneg _) (Real.log_pos hT₁).le
  exact centeredRationalOrdinate_remainder_le_of_positive (mul_nonneg hK.le hscale) hT

end RiemannResearch.Analysis.ActualZeroOrdinate
