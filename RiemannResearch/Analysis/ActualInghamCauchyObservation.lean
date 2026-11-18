import RiemannResearch.Analysis.InghamCauchyKernel
import RiemannResearch.Analysis.ActualZeroDensityCauchyObservation
import Mathlib.Tactic

/-! # The two vertical moments detected at each actual zeta zero

The four signed terms are those of `cauchyDetector_rectangle`. At positive
heights sufficiently far from the two horizontal edges their combined norm
is small. The vertical contributions have respective orders 4/3 and 2.
-/
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.InghamMollifier
open MontgomeryPoisson

theorem vertical_error_continuous (X : ℕ) {x : ℝ} (hx : x ≠ 1) :
    Continuous (fun t : ℝ => ‖mollifiedError X ((x : ℂ) + (t : ℂ) * I)‖) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  let s : ℂ := (x : ℂ) + (t : ℂ) * I
  have hs : s ≠ 1 := fun h => hx (by simpa [s] using congrArg Complex.re h)
  have hf : ContinuousAt (mollifiedError X) s :=
    (((analyticAt_riemannZeta hs).mul (mollifier_analyticAt X s)).sub analyticAt_const).continuousAt
  have hline : ContinuousAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) t := by fun_prop
  exact (hf.comp_of_eq hline rfl).norm

private theorem ingham_horizontal_small {X : ℕ} {ℓ L T : ℝ} {ρ s : ℂ}
    (hℓ : 16 ≤ ℓ) (hT : T = Real.exp ℓ) (hL : 0 ≤ L) (hL' : L ≤ 2 * ℓ)
    (hX : (X : ℝ) ≤ 2 * T) (hρ : 1 / 2 ≤ ρ.re) (hρ' : ρ.re ≤ 1)
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) (hy : 1 ≤ |s.im|)
    (hy' : |s.im| ≤ 2 * T) (hd : 4 * ℓ ≤ |s.im - ρ.im|) :
    ‖cauchyDetector X L ρ s‖ ≤ 1 / 8 := by
  have hbig : ℓ + 1 ≤ T := hT ▸ Real.add_one_le_exp _
  have hm := mollifiedError_norm_le_on_horizontal (by linarith : 1 ≤ T) hX hs hy hy'
  have hsq : (s.re - ρ.re) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - (s.re - ρ.re) by linarith)
      (show 0 ≤ 1 + (s.re - ρ.re) by linarith)]
  have hds := mul_self_le_mul_self (show 0 ≤ 4 * ℓ by linarith) hd
  have hsqr : (4 * ℓ) ^ 2 ≤ (s.im - ρ.im) ^ 2 := by simpa only [← sq, sq_abs] using hds
  have hfac : L * (s.re - 1 / 2) ≤ 2 * ℓ := by
    nlinarith [mul_nonneg hL (show 0 ≤ 3 / 2 - s.re by linarith)]
  have he : Real.exp (L * (s.re - 1 / 2) + (s.re - ρ.re) ^ 2 - (s.im - ρ.im) ^ 2) ≤
      Real.exp (-(4 * ℓ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hsqr, mul_nonneg (show 0 ≤ ℓ by linarith) (show 0 ≤ ℓ - 16 by linarith)]
  have hn : 1 ≤ ‖s - ρ‖ := by
    have hi := Complex.abs_im_le_norm (s - ρ)
    rw [Complex.sub_im] at hi
    linarith
  rw [norm_cauchyDetector]
  refine (div_le_self (by positivity) hn).trans ?_
  refine (mul_le_mul hm he (Real.exp_pos _).le (by positivity)).trans ?_
  have hTpos : 0 < T := by linarith
  have heq : Real.exp (-(4 * ℓ)) = (T ^ 4)⁻¹ := by
    rw [hT, Real.exp_neg]; congr 1; rw [← Real.exp_nat_mul]; norm_num
  rw [heq, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (show 0 ≤ T ^ 2 by positivity)
    (show 0 ≤ T ^ 2 - 160 by nlinarith [sq_nonneg (T - 17)])]

/-- A pointwise observation with the same real-part threshold for every zero
of the counted multiset. The low-height count is kept separately in the sum. -/
theorem ingham_two_edge_observation {X : ℕ} {T ℓ L σ d : ℝ} {ρ : ℂ}
    (hℓ : 16 ≤ ℓ) (hT : T = Real.exp ℓ) (hbig : 1 + 4 * ℓ ≤ T)
    (hL : 0 ≤ L) (hL' : L ≤ 2 * ℓ) (hX : (X : ℝ) ≤ 2 * T)
    (hd : 0 < d) (hd' : d ≤ 1 / 2) (hσ : d ≤ σ - 1 / 2) (hsρ : σ ≤ ρ.re)
    (hρ : ρ.re < 1) (hlo : 1 + 4 * ℓ < ρ.im) (hhi : ρ.im ≤ T) (hz : riemannZeta ρ = 0) :
    1 ≤ ∫ t in (1 : ℝ)..2 * T,
      (2 * (((32 * Real.exp 1 * Real.exp (L * (1 / 2 - σ))) ^ (4 / 3 : ℝ) / d) *
        ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) +
        ((32 * Real.exp 1 * Real.exp (L * (1 + d - σ))) ^ (2 : ℕ) / d) *
        ‖mollifiedError X (((1 + d : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ))) *
        cauchyWeight (t - ρ.im) := by
  let b := 1 + d
  let n := Real.exp (-(L * (σ - 1 / 2)))
  let K := cauchyDetector X L ρ
  let z₀ : ℂ := (1 / 2 : ℂ) + I
  let z₁ : ℂ := (b : ℂ) + ((2 * T : ℝ) : ℂ) * I
  have hb : 1 < b := by dsimp [b]; linarith
  have hb' : b ≤ 3 / 2 := by dsimp [b]; linarith
  have hhalf : 1 / 2 ≤ ρ.re := by linarith
  have hn : 0 < n := Real.exp_pos _
  have hn' : n ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hL (by linarith)))
  have hre : z₀.re ≤ z₁.re := by simp [z₀, z₁]; linarith
  have him : z₀.im ≤ z₁.im := by simp [z₀, z₁]; linarith
  have hint : Rectangle z₀ z₁ ∈ 𝓝 ρ := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him, mem_reProdIm, mem_Ioo]
    simp [z₀, z₁]
    exact ⟨⟨by simpa [one_div] using (show (1 / 2 : ℝ) < ρ.re by linarith), by linarith⟩,
      by linarith, by linarith⟩
  have hres := congrArg norm (cauchyDetector_rectangle X L hre him (by norm_num [z₀]) hint hz)
  rw [norm_neg, Complex.norm_exp] at hres
  have heRe : (((L : ℂ) * (ρ - (1 / 2 : ℂ))).re) = L * (ρ.re - 1 / 2) := by simp [Complex.mul_re]
  rw [heRe] at hres
  have fac : ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num, mul_one, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have hraw : Real.exp (L * (ρ.re - 1 / 2)) ≤ ‖RectangleIntegral K z₀ z₁‖ := by
    calc
      _ = ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ * ‖RectangleIntegral K z₀ z₁‖ := by
        simpa [RectangleIntegral', K, norm_smul] using hres.symm
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) fac
  have hunit : 1 ≤ n * Real.exp (L * (ρ.re - 1 / 2)) := by
    dsimp [n]; rw [← Real.exp_add]; apply Real.one_le_exp
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hsρ)]
  have hH {y : ℝ} (hy : 1 ≤ y) (hy' : y ≤ 2 * T) (hsep : 4 * ℓ ≤ |y - ρ.im|) :
      ‖HIntegral K (1 / 2) b y‖ ≤ 1 / 8 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 / 2 : ℝ)) (b := b) (C := (1 / 8 : ℝ))
      (f := fun x : ℝ => K ((x : ℂ) + (y : ℂ) * I)) (by
        intro x hx
        rw [uIoc_of_le (by linarith)] at hx
        apply ingham_horizontal_small hℓ hT hL hL' hX hhalf hρ.le
        · simpa using hx.1.le
        · simpa using hx.2.trans hb'
        · simpa [abs_of_nonneg (by linarith : 0 ≤ y)] using hy
        · simpa [abs_of_nonneg (by linarith : 0 ≤ y)] using hy'
        · simpa using hsep)
    change ‖∫ x in (1 / 2 : ℝ)..b, K ((x : ℂ) + (y : ℂ) * I)‖ ≤ _
    exact hh.trans (by rw [abs_of_nonneg (by linarith : 0 ≤ b - 1 / 2)]; linarith)
  have hB := hH (y := 1) le_rfl (by linarith) (by rw [abs_of_nonpos (by linarith : 1 - ρ.im ≤ 0)]; linarith)
  have hU := hH (y := 2 * T) (by linarith) le_rfl (by rw [abs_of_nonneg (by linarith : 0 ≤ 2 * T - ρ.im)]; linarith)
  have htri (a b c d : ℂ) : ‖a - b + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    linarith only [norm_sub_le (a - b + c) d, norm_add_le (a - b) c, norm_sub_le a b]
  have hsum := hunit.trans (mul_le_mul_of_nonneg_left (hraw.trans (htri _ _ _ _)) hn.le)
  simp [z₀, z₁, mul_add] at hsum
  have hB' := mul_le_mul hn' hB (norm_nonneg _) (by norm_num : (0: ℝ) ≤ 1)
  have hU' := mul_le_mul hn' hU (norm_nonneg _) (by norm_num : (0: ℝ) ≤ 1)
  have hab : 1 ≤ 2 * T := by linarith
  have sql (x : ℝ) (hx : 1 / 2 ≤ x) (hx' : x ≤ 3 / 2) : (x - ρ.re) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - (x - ρ.re) by linarith) (show 0 ≤ 1 + (x - ρ.re) by linarith)]
  have hleft := tilted_vertical_moment_le (X := X) (σ := σ) (L := L) (ρ := ρ) hab hd
    (show d ≤ |1 / 2 - ρ.re| by rw [abs_of_nonpos (by linarith)]; linarith)
    (sql _ le_rfl (by norm_num)) (by norm_num : (1 : ℝ) ≤ 4 / 3) (by norm_num)
    (vertical_error_continuous X (by norm_num : (1 / 2 : ℝ) ≠ 1))
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hleft
  have hright := tilted_vertical_moment_le (X := X) (σ := σ) (L := L) (ρ := ρ) hab hd
    (show d ≤ |b - ρ.re| by rw [abs_of_nonneg (by linarith)]; dsimp [b]; linarith)
    (sql _ (by linarith) hb') (by norm_num : (1 : ℝ) ≤ 2) le_rfl (vertical_error_continuous X hb.ne')
  simp only [Real.rpow_two] at hright
  let A (t : ℝ) := (32 * Real.exp 1 * Real.exp (L * (1 / 2 - σ))) ^ (4 / 3 : ℝ) / d *
    ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)
  let B (t : ℝ) := (32 * Real.exp 1 * Real.exp (L * (b - σ))) ^ 2 / d *
    ‖mollifiedError X ((b : ℂ) + (t : ℂ) * I)‖ ^ 2
  let w (t : ℝ) := cauchyWeight (t - ρ.im)
  have hw : Continuous w := continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun t => by dsimp; positivity)
  have hA : Continuous A := continuous_const.mul ((critical_error_continuous X).rpow_const (fun _ => Or.inr (by norm_num)))
  have hBc : Continuous B := continuous_const.mul ((vertical_error_continuous X hb.ne').pow 2)
  change n * ‖VIntegral K (1 / 2) 1 (2 * T)‖ ≤ 1 / 8 + ∫ t in (1: ℝ)..2 * T, A t * w t at hleft
  change n * ‖VIntegral K b 1 (2 * T)‖ ≤ 1 / 8 + ∫ t in (1: ℝ)..2 * T, B t * w t at hright
  change 1 ≤ ∫ t in (1: ℝ)..2 * T, (2 * (A t + B t)) * w t
  simp_rw [mul_assoc, add_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (f := fun t => A t * w t) (g := fun t => B t * w t)
    ((hA.mul hw).intervalIntegrable _ _) ((hBc.mul hw).intervalIntegrable _ _)]
  simp only [one_div] at hB' hU' hleft hright
  linarith only [hsum, hB', hU', hleft, hright]

end RiemannResearch.Analysis.InghamMollifier
