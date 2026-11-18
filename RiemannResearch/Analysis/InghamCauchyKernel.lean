import RiemannResearch.Analysis.ActualZeroDensityCauchyDetector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Vertical moments in the tilted Cauchy rectangle

The signed identity is `cauchyDetector_rectangle`. The estimates here keep a
single inverse power of the distance to the vertical boundary for every moment
order between one and two. The complementary Poisson kernel has mass at most π.
The target density exponent is Ingham's as stated in Chourasiya and Simonič,
https://arxiv.org/abs/2507.15184.
-/

noncomputable section
open Complex Set MeasureTheory
namespace RiemannResearch.Analysis.InghamMollifier
open MontgomeryPoisson

private theorem poisson_interval_integral (u v γ d : ℝ) (hd : 0 < d) :
    (∫ t in u..v, d / (d ^ 2 + (t - γ) ^ 2)) =
      Real.arctan ((v - γ) / d) - Real.arctan ((u - γ) / d) := by
  have hder (t : ℝ) : HasDerivAt (fun x : ℝ => Real.arctan ((x - γ) / d))
      (d / (d ^ 2 + (t - γ) ^ 2)) t := by
    have h := (Real.hasDerivAt_arctan ((t - γ) / d)).comp t
      (((hasDerivAt_id t).sub_const γ).div_const d)
    convert h using 1 <;> first | rfl | field_simp [hd.ne']
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
    ((continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
      (fun t => by dsimp; positivity)).intervalIntegrable u v)

private theorem split_cauchy_factor {U r d p : ℝ} (hu : 0 ≤ U) (hd : 0 < d)
    (hr : d ≤ r) (hp : 1 ≤ p) (hp' : p ≤ 2) :
    U / r ≤ U ^ p / d + d / r ^ 2 := by
  have hr0 := hd.trans_le hr
  by_cases h : U ≤ d / r
  · have hh := div_le_div_of_nonneg_right h hr0.le
    rw [div_div, ← sq] at hh
    linarith [div_nonneg (Real.rpow_nonneg hu p) hd.le]
  · have hu0 : 0 < U := (div_pos hd hr0).trans (lt_of_not_ge h)
    have he : d / r ≤ U ^ (p - 1) := by
      by_cases hu1 : 1 ≤ U
      · exact (div_le_one_of_le₀ hr hr0.le).trans (Real.one_le_rpow hu1 (by linarith))
      · have he := Real.rpow_le_rpow_of_exponent_ge hu0 (le_of_not_ge hu1)
            (by linarith : p - 1 ≤ 1)
        rw [Real.rpow_one] at he
        exact (le_of_not_ge h).trans he
    have hpow : U * U ^ (p - 1) = U ^ p := by
      conv_lhs => lhs; rw [← Real.rpow_one U]
      rw [← Real.rpow_add hu0, show 1 + (p - 1) = p by ring]
    have hh := mul_le_mul_of_nonneg_left he hu
    rw [hpow] at hh
    have hmain : U / r ≤ U ^ p / d := (le_div_iff₀ hd).mpr (by
      convert hh using 1; ring)
    linarith [div_nonneg hd.le (sq_nonneg r)]

/-- A normalized vertical edge costs one inverse separation for the moment.
The second term integrates exactly to an arctangent difference. -/
theorem tilted_vertical_moment_le {X : ℕ} {ρ : ℂ} {x σ L d p u v : ℝ}
    (huv : u ≤ v) (hd : 0 < d) (hgap : d ≤ |x - ρ.re|)
    (hx : (x - ρ.re) ^ 2 ≤ 1) (hp : 1 ≤ p) (hp' : p ≤ 2)
    (hc : Continuous (fun t : ℝ => ‖mollifiedError X ((x : ℂ) + (t : ℂ) * I)‖)) :
    Real.exp (-(L * (σ - 1 / 2))) * ‖VIntegral (cauchyDetector X L ρ) x u v‖ ≤
      1 / 8 + ∫ t in u..v,
        ((32 * Real.exp 1 * Real.exp (L * (x - σ))) ^ p / d *
          ‖mollifiedError X ((x : ℂ) + (t : ℂ) * I)‖ ^ p) * cauchyWeight (t - ρ.im) := by
  let A (t : ℝ) := ‖mollifiedError X ((x : ℂ) + (t : ℂ) * I)‖
  let w (t : ℝ) := cauchyWeight (t - ρ.im)
  let B := 32 * Real.exp 1 * Real.exp (L * (x - σ))
  let n := Real.exp (-(L * (σ - 1 / 2)))
  let g (t : ℝ) := (B ^ p / d * A t ^ p) * w t
  let P (t : ℝ) := d / (d ^ 2 + (t - ρ.im) ^ 2)
  have hn : 0 < n := Real.exp_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  have hw : Continuous w := continuous_const.div
    (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun t => by dsimp; positivity)
  have hg : Continuous g := (continuous_const.mul
    (hc.rpow_const fun _ => Or.inr (by linarith))).mul hw
  have hP : Continuous P := continuous_const.div
    (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun t => by dsimp; positivity)
  have hpt (t : ℝ) :
      n * ‖cauchyDetector X L ρ ((x : ℂ) + (t : ℂ) * I)‖ ≤ g t + P t / 32 := by
    let s := (x : ℂ) + (t : ℂ) * I
    let r := ‖s - ρ‖
    have hs : s.re = x := by simp [s]
    have ht : s.im = t := by simp [s]
    have hdr : d ≤ r := hgap.trans (by simpa [r, Complex.sub_re, hs] using Complex.abs_re_le_norm (s - ρ))
    have hr := hd.trans_le hdr
    have hdist : d ^ 2 + (t - ρ.im) ^ 2 ≤ r ^ 2 := by
      have h := pow_le_pow_left₀ hd.le hgap 2
      rw [sq_abs] at h
      simp only [r, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hs, ht]
      nlinarith
    have hw0 : 0 ≤ w t := by dsimp [w, cauchyWeight]; positivity
    have hw1 : w t ≤ 1 := by
      dsimp [w, cauchyWeight]
      exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (t - ρ.im)])
    have hA : 0 ≤ A t := norm_nonneg _
    have hraw : n * ‖cauchyDetector X L ρ s‖ ≤ (B * A t / r) * w t / 32 := by
      rw [norm_cauchyDetector, hs, ht]
      have hExp : n * Real.exp (L * (x - 1 / 2) + (x - ρ.re) ^ 2 - (t - ρ.im) ^ 2) =
          Real.exp (L * (x - σ)) * Real.exp ((x - ρ.re) ^ 2) * Real.exp (-(t - ρ.im) ^ 2) := by
        dsimp [n]
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1 <;> ring
      have hh := mul_le_mul (Real.exp_le_exp.mpr hx) (gaussian_le_cauchyWeight (t - ρ.im))
        (Real.exp_pos _).le (Real.exp_pos _).le
      change n * (A t * _ / r) ≤ _
      calc
        _ = (A t / r) * (n * Real.exp (L * (x - 1 / 2) + (x - ρ.re) ^ 2 - (t - ρ.im) ^ 2)) := by ring
        _ ≤ (A t / r) * (Real.exp (L * (x - σ)) * (Real.exp 1 * w t)) := by
          rw [hExp, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le)
            (div_nonneg hA hr.le)
        _ = _ := by dsimp [B]; ring
    have hh := mul_le_mul_of_nonneg_right
      (split_cauchy_factor (mul_nonneg hB.le hA) hd hdr hp hp') hw0
    have hpk : d / r ^ 2 * w t ≤ P t := by
      exact (mul_le_of_le_one_right (div_nonneg hd.le (sq_nonneg _)) hw1).trans
        (div_le_div_of_nonneg_left hd.le (by positivity) hdist)
    rw [add_mul, Real.mul_rpow hB.le hA] at hh
    have hg0 : 0 ≤ g t := by dsimp [g]; positivity
    have h32 : 32 * (n * ‖cauchyDetector X L ρ s‖) ≤ (B * A t / r) * w t := by linarith
    change n * ‖cauchyDetector X L ρ s‖ ≤ _
    have hgeq : B ^ p * A t ^ p / d * w t = g t := by dsimp [g]; ring
    rw [hgeq] at hh
    linarith
  have hnorm : ‖VIntegral (cauchyDetector X L ρ) x u v‖ ≤
      ∫ t in u..v, (g t + P t / 32) / n := by
    rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le huv
      (Filter.Eventually.of_forall fun t _ => (le_div_iff₀ hn).mpr (by simpa [mul_comm n] using hpt t))
      (((hg.add (hP.div_const _)).div_const _).intervalIntegrable _ _)
  rw [intervalIntegral.integral_div, le_div_iff₀ hn, intervalIntegral.integral_add
    (hg.intervalIntegrable _ _) ((hP.div_const _).intervalIntegrable _ _),
    intervalIntegral.integral_div] at hnorm
  have hpMass : (∫ t in u..v, P t) ≤ 4 := by
    rw [show (∫ t in u..v, P t) = _ from poisson_interval_integral u v ρ.im d hd]
    linarith [Real.arctan_lt_pi_div_two ((v - ρ.im) / d),
      Real.neg_pi_div_two_lt_arctan ((u - ρ.im) / d), Real.pi_lt_four]
  change n * _ ≤ 1 / 8 + ∫ t in u..v, g t
  linarith [mul_comm n ‖VIntegral (cauchyDetector X L ρ) x u v‖]

end RiemannResearch.Analysis.InghamMollifier
