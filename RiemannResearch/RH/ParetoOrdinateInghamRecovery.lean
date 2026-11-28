import RiemannResearch.RH.ParetoOrdinateLandauRecovery
import RiemannResearch.Analysis.ActualInghamSlopeFrontier
import Mathlib.Analysis.PSeries

/-! # Ingham at slope two and strong Pareto recovery of the centered Landau traces

The curved density exponent charges a positive intercept at slope two.
Its bound at real part 3/4 controls all the integer coordinates through the
current height. Together with the fixed-frequency Landau theorem this gives
strong recovery of the first Pareto atom. See Chourasiya and Simonič,
https://arxiv.org/abs/2507.15184, for the underlying Ingham exponent.
-/

noncomputable section
open Set Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open RiemannResearch.Analysis ActualZeroOrdinate ZeroDensityRate CoefficientStabilization

/-- The sharp intercept when the affine Ingham slope is two. -/
theorem ingham_slope_two_intercept (b : ℝ) :
    (∀ d ∈ Icc (0 : ℝ) (1/2), 2*d ≤ inghamRate d + b) ↔ 5 - 2*Real.sqrt 6 ≤ b := by
  let r := Real.sqrt 6 / 2
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hlow : (2 : ℝ) ≤ Real.sqrt 6 := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [hs]
    norm_num
  have hhigh : Real.sqrt 6 ≤ 3 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [hs]
    norm_num
  have h := ingham_middle_price (r := r) (b := b)
    (by dsimp [r]; linarith) (by dsimp [r]; linarith)
  have h₁ : (4 / 3 : ℝ) * r ^ 2 = 2 := by dsimp [r]; nlinarith only [hs]
  have h₂ : 2 * (r - 1) ^ 2 = 5 - 2 * Real.sqrt 6 := by dsimp [r]; nlinarith only [hs]
  simpa only [h₁, h₂] using h

/-- The slope-two estimate makes the right tail above 3/4 small enough
even after multiplication by the largest fourth root on the integer head. -/
theorem eventually_ingham_three_quarter_tail :
    ∀ᶠ T : ℝ in atTop,
      Real.exp (Real.log T / 4) * rightInclusiveCount T (3 / 4) ≤ (Ncount 0 T : ℝ) := by
  have hs : (39/16 : ℝ) ≤ Real.sqrt 6 := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have ha := (ingham_slope_two_intercept (1/8)).mpr (by linarith)
  obtain ⟨C,hC,hbound⟩ := exists_ingham_priced_density
  have hg : Tendsto (fun T : ℝ => Real.log T / 8) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num)
  have hm := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hg
  have hsmall : Tendsto (fun T : ℝ => C * (Real.log T)^3 * Real.exp (-Real.log T/8))
      atTop (𝓝 0) := by
    have h := hm.const_mul (512*C)
    simp only [mul_zero] at h
    apply h.congr
    intro T
    dsimp
    rw [show -(Real.log T / 8) = -Real.log T / 8 by ring]
    ring
  filter_upwards [eventually_ge_atTop (max 2 (Real.exp 1)), eventually_count_pos,
    hsmall.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    tendsto_height_div_count.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with T hT hN hsmall hTN
  have ht : 0 < T := by linarith [(le_max_left (2 : ℝ) (Real.exp 1)).trans hT]
  have hN' : (0 : ℝ) < Ncount 0 T := by exact_mod_cast hN
  have hTN' : T ≤ (Ncount 0 T : ℝ) := by simpa using (div_le_iff₀ hN').mp hTN
  have hl : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hT)
  have hll := Real.log_nonneg hl
  have hd := hbound T hT 2 (1/8) ha (1/4) (by constructor <;> norm_num)
  rw [show (1/2 : ℝ)+1/4 = 3/4 by norm_num] at hd
  have he : Real.exp ((Real.log T + Real.log (Real.log T)) * (1/8 - 2*(1/4))) ≤
      Real.exp (-3 * Real.log T / 8) := Real.exp_le_exp.mpr (by linarith)
  have hb := hd.trans (mul_le_mul_of_nonneg_left he (by positivity))
  calc
    _ ≤ Real.exp (Real.log T/4) * (C*T*(Real.log T)^3 * Real.exp (-3*Real.log T/8)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = T * (C*(Real.log T)^3 * Real.exp (-Real.log T/8)) := by
      rw [show -Real.log T/8 = Real.log T/4 + -3*Real.log T/8 by ring, Real.exp_add]
      ring
    _ ≤ T := mul_le_of_le_one_right ht.le hsmall
    _ ≤ _ := hTN'

private theorem landau_normalized_fourth_root {x T : ℝ} (hx : 1 ≤ x) (hxT : x ≤ T)
    (hN : 0 < Ncount 0 T)
    (htail : Real.exp (Real.log T / 4) * rightInclusiveCount T (3 / 4) ≤ (Ncount 0 T : ℝ)) :
    |(landauSum T (Real.log x) / (Ncount 0 T : ℂ)).re| ≤ 2 * Real.exp (Real.log x/4) := by
  let w := Real.exp (Real.log x/4)
  let I (ρ : ℂ) : ℝ := if 3/4 ≤ ρ.re then 1 else 0
  have hw : 0 < w := Real.exp_pos _
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsum : ‖landauSum T (Real.log x)‖ ≤ realSum T (fun ρ => 1*w + I ρ * (w*w)) := by
    apply (ActualZeroOrdinate.norm_sum_le T _).trans
    apply realSum_mono
    intro ρ hρ
    rw [Complex.norm_exp]
    have hr : ((Real.log x : ℂ) * (ρ - 1/2)).re = Real.log x * (ρ.re - 1/2) := by simp
    rw [hr]
    by_cases h : 3/4 ≤ ρ.re
    · have hhi := (mem_cutoff.mp hρ).1.2.2
      have he : Real.exp (Real.log x * (ρ.re - 1/2)) ≤ w*w := by
        dsimp [w]
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left hhi.le hL]
      simp only [I, if_pos h, one_mul]
      linarith
    · simp only [I, if_neg h, zero_mul, one_mul, add_zero]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge h) hL]
  rw [realSum_add, realSum_mul_const, realSum_one, realSum_mul_const] at hsum
  change ‖landauSum T (Real.log x)‖ ≤ (Ncount 0 T : ℝ) * w +
      rightInclusiveCount T (3/4) * (w*w) at hsum
  have hwT : w ≤ Real.exp (Real.log T/4) :=
    Real.exp_le_exp.mpr (by linarith [Real.log_le_log (zero_lt_one.trans_le hx) hxT])
  have hR := (mul_le_mul_of_nonneg_right hwT (rightInclusiveCount_nonneg T (3/4))).trans htail
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (show (0 : ℝ) < Ncount 0 T by exact_mod_cast hN)).mpr
  change ‖landauSum T (Real.log x)‖ ≤ 2*w * _
  nlinarith only [hsum, mul_le_mul_of_nonneg_right hR hw.le]

private theorem pareto_fourth_root_sq_le (i : ℕ) :
    paretoWeight i * Real.exp (Real.log ((i+1 : ℕ) : ℝ)/4)^2 ≤
      ((i+1 : ℕ) : ℝ)^(-3/2 : ℝ) := by
  let x := ((i+1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hw : paretoWeight i = 1/(x*(x+1)) := by dsimp [paretoWeight,x]; push_cast; ring
  have hweight : paretoWeight i ≤ 1/x^2 := by
    rw [hw]
    apply one_div_le_one_div_of_le (sq_pos_of_pos hx)
    nlinarith only [hx.le]
  have he : Real.exp (Real.log x/4)^2 = x^(1/2 : ℝ) := by
    rw [Real.rpow_def_of_pos hx, pow_two, ← Real.exp_add]
    congr 1
    ring
  have h2 : 1/x^2 = x ^ (-(2 : ℝ)) := by rw [Real.rpow_neg hx.le, Real.rpow_two, one_div]
  change paretoWeight i * Real.exp (Real.log x/4)^2 ≤ x^(-3/2:ℝ)
  calc
    _ ≤ (1/x^2) * Real.exp (Real.log x/4)^2 := mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    _ = _ := by rw [h2, he, ← Real.rpow_add hx]; norm_num

/-- The centered Landau estimator on all integers through the height
converges strongly to the first Pareto atom using the proved Ingham bound. -/
theorem landauHead_tendsto_of_ingham :
    Tendsto (fun T : ℝ => landauHead T ⌊T⌋₊) atTop (𝓝 (paretoPointHilbert 0)) := by
  let f (T : ℝ) (i : ℕ) := hilbertGibbsPhysical (landauHead T ⌊T⌋₊) i
  let v (i : ℕ) := if i = 0 then (1 : ℝ) else 0
  have hhead (i : ℕ) : ∀ᶠ T : ℝ in atTop, i < ⌊T⌋₊ := by
    filter_upwards [eventually_ge_atTop ((i+1 : ℕ) : ℝ)] with T hT
    exact Nat.lt_of_succ_le (Nat.le_floor hT)
  have hfix (i : ℕ) : Tendsto (fun T : ℝ => f T i) atTop (𝓝 (v i)) := by
    have hraw : Tendsto (fun T : ℝ => (landauSum T (Real.log ((i+1 : ℕ) : ℝ)) /
        (Ncount 0 T : ℂ)).re) atTop (𝓝 (v i)) := by
      by_cases hi : i = 0
      · subst i
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_count_pos] with T hN
        have hn : (Ncount 0 T : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
        simp [v, landauSum_zero, hn]
      · have hi' : 1 < ((i+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < i+1 by omega)
        have hh := Complex.continuous_re.continuousAt.tendsto.comp
          (tendsto_landau_div_count_of_pos (Real.log_pos hi'))
        simpa [v, hi, Function.comp_def] using hh
    apply hraw.congr'
    filter_upwards [hhead i] with T hi
    dsimp only [f]
    rw [landauHead_physical, if_pos hi]
  have hactual (T : ℝ) (i : ℕ) :
      landauHead T ⌊T⌋₊ i = Real.sqrt (paretoWeight i) * f T i := by
    dsimp only [f, hilbertGibbsPhysical]
    field_simp [(Real.sqrt_pos.mpr (paretoWeight_pos i)).ne']
  have hatom (i : ℕ) : paretoPointHilbert 0 i = Real.sqrt (paretoWeight i) * v i := by
    change Real.sqrt (paretoWeight i) * (if i+1 = 0+1 then 1 else 0) = _
    simp [v]
  have hs : Summable (fun i : ℕ => ((i+1 : ℕ) : ℝ) ^ (-3/2 : ℝ)) := by
    have hseries : Summable (fun n : ℕ => (n : ℝ)^(-3/2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr hseries
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ i : ℕ,
      ‖(landauHead T ⌊T⌋₊ i - paretoPointHilbert 0 i)^2‖ ≤
        9 * ((i+1 : ℕ) : ℝ)^(-3/2 : ℝ) := by
    filter_upwards [eventually_ingham_three_quarter_tail, eventually_count_pos,
      eventually_gt_atTop (0 : ℝ)] with T htail hN hT i
    let x := ((i+1 : ℕ) : ℝ)
    let w := Real.exp (Real.log x/4)
    have hx : 1 ≤ x := by
      dsimp only [x]
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le i))
    have hw : 1 ≤ w := Real.one_le_exp (by dsimp [x]; exact div_nonneg (Real.log_nonneg hx) (by norm_num))
    have hf : |f T i| ≤ 2*w := by
      dsimp only [f]
      rw [landauHead_physical]
      split_ifs with hi
      · apply landau_normalized_fourth_root hx _ hN htail
        have hk : x ≤ (⌊T⌋₊ : ℝ) := by
          dsimp only [x]
          exact_mod_cast Nat.succ_le_of_lt hi
        exact hk.trans (Nat.floor_le hT.le)
      · rw [abs_zero]
        linarith
    have hv : |v i| ≤ w := by by_cases hi : i = 0 <;> simp [v, hi] <;> linarith
    have hr := (abs_sub (f T i) (v i)).trans (show |f T i| + |v i| ≤ 3*w by linarith)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hr 2
    rw [sq_abs] at hsq
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hactual, hatom, ← mul_sub,
      mul_pow, Real.sq_sqrt (paretoWeight_pos i).le]
    have h := pareto_fourth_root_sq_le i
    change paretoWeight i * w^2 ≤ x^(-3/2 : ℝ) at h
    calc
      _ ≤ paretoWeight i * (3*w)^2 := mul_le_mul_of_nonneg_left hsq (paretoWeight_pos i).le
      _ = 9*(paretoWeight i * w^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun (T : ℝ) i => (landauHead T ⌊T⌋₊ i - paretoPointHilbert 0 i)^2)
    (g := fun _ : ℕ => (0 : ℝ)) (hs.mul_left 9)
    (fun i => by
      simp only [hactual, hatom]
      simpa using (((hfix i).const_mul (Real.sqrt (paretoWeight i))).sub_const
        (Real.sqrt (paretoWeight i) * v i)).pow 2)
    hbound
  have hn : Tendsto (fun T : ℝ => ‖landauHead T ⌊T⌋₊ - paretoPointHilbert 0‖^2) atTop (𝓝 0) := by
    simpa only [hilbert_norm_sq, lp.coeFn_sub, Pi.sub_apply, tsum_zero] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hn

theorem landauHead_squaredError_tendsto_of_ingham :
    Tendsto (fun T : ℝ => ‖closedSpaceᗮ.starProjection (landauHead T ⌊T⌋₊)‖^2)
      atTop (𝓝 ((1 - IntegerDPP.limitingKernel 0 0)/2)) := by
  have h := (closedSpaceᗮ.starProjection.continuous.continuousAt.tendsto.comp
    landauHead_tendsto_of_ingham).norm.pow 2
  simpa only [Function.comp_def, first_site_residual_sq] using h

theorem landauHead_squaredError_sub_far_tendsto_of_ingham
    (hS : MontgomeryPositiveGap.SineWindowMoment) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun T : ℝ => ‖closedSpaceᗮ.starProjection (landauHead T ⌊T⌋₊)‖^2 - farError T q)
      atTop (𝓝 0) := by
  simpa only [sub_self] using
    landauHead_squaredError_tendsto_of_ingham.sub (farError_tendsto_of_sine hS hq)

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.landauHead_squaredError_sub_far_tendsto_of_ingham' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms landauHead_squaredError_sub_far_tendsto_of_ingham

end RiemannResearch.RH.Pareto.OrdinateCosine
