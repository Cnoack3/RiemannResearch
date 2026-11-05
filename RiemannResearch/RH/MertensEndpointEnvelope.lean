import RiemannResearch.RH.MertensLeeLeongCriterion

/-!
# First-moment error at the Lee–Leong leading coefficient

A square-root correction in the exponent controls the shift from the
physical site n back to the Möbius cutoff N in the harmonic window bound.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis

private theorem vk_div_log_formula {x : ℝ} (hx : 0 < Real.log x) :
    vkProfile x / Real.log x =
      (Real.log x) ^ (-(2 / 5 : ℝ)) / (Real.log (Real.log x)) ^ (1 / 5 : ℝ) := by
  rw [show -(2 / 5 : ℝ) = (3 / 5 : ℝ) - 1 by norm_num, Real.rpow_sub hx, Real.rpow_one]
  unfold vkProfile
  ring

/-- A relative increment bound uniform in the larger argument. The factor
Φ(y)/log y is retained because the leading exponential coefficients agree. -/
theorem vk_eventual_relative_increment :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      vkProfile y - vkProfile x ≤
        (vkProfile y / Real.log y) * (Real.log y - Real.log x) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1))]
    with x hx hxE y hxy
  have htx : 0 < Real.log x := (Real.exp_pos 1).trans_le hxE
  have ht := Real.log_le_log hx hxy
  have hty := htx.trans_le ht
  have hLx1 := (Real.le_log_iff_exp_le htx).mpr hxE
  have hLx : 0 < Real.log (Real.log x) := by linarith
  have hL := Real.log_le_log htx ht
  have hLy := hLx.trans_le hL
  have hs : vkProfile y / Real.log y ≤ vkProfile x / Real.log x := by
    rw [vk_div_log_formula hty, vk_div_log_formula htx]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hLy _) (Real.rpow_pos_of_pos hLx _)).mpr
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos htx ht (by norm_num))
      (Real.rpow_le_rpow hLx.le hL (by norm_num))
      (Real.rpow_nonneg hLx.le _) (Real.rpow_nonneg htx.le _)
  have hcross := (le_div_iff₀ htx).mp hs
  have hself := div_mul_cancel₀ (vkProfile y) hty.ne'
  linarith only [hcross, hself]

/-- Φ²/log is little-o of √Φ since Φ(t)^(3/2) grows at most like
(log t)^(9/10). The coefficient is arbitrary. -/
theorem vk_sq_div_log_eventual_le_sqrt (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ y : ℝ in atTop, vkProfile y ^ 2 / Real.log y ≤ δ * Real.sqrt (vkProfile y) := by
  have hpow : Tendsto (fun t : ℝ => t ^ (-(1 / 10 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hsmall := (tendsto_order.1 (hpow.comp Real.tendsto_log_atTop)).2 δ hδ
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (Real.exp 1))] with y hy hyE
  change Real.log y ^ (-(1 / 10 : ℝ)) < δ at hy
  have hT : 0 < Real.log y := (Real.exp_pos 1).trans_le hyE
  have hL1 := (Real.le_log_iff_exp_le hT).mpr hyE
  have hL : 0 < Real.log (Real.log y) := by linarith
  have hΦ : 0 < vkProfile y := div_pos (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hL _)
  have hu : vkProfile y ≤ (Real.log y) ^ (3 / 5 : ℝ) :=
    div_le_self (Real.rpow_nonneg hT.le _) (Real.one_le_rpow hL1 (by norm_num))
  have hp : vkProfile y * Real.sqrt (vkProfile y) ≤ (Real.log y) ^ (9 / 10 : ℝ) := by
    calc
      _ = vkProfile y ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, mul_comm, ← Real.rpow_add_one hΦ.ne']
        congr 1 <;> norm_num
      _ ≤ ((Real.log y) ^ (3 / 5 : ℝ)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hΦ.le hu (by norm_num)
      _ = (Real.log y) ^ (9 / 10 : ℝ) := by
        rw [← Real.rpow_mul hT.le]
        norm_num
  have hpowEq : (Real.log y) ^ (9 / 10 : ℝ) / Real.log y =
      (Real.log y) ^ (-(1 / 10 : ℝ)) := by
    rw [show -(1 / 10 : ℝ) = 9 / 10 - 1 by norm_num, Real.rpow_sub hT, Real.rpow_one]
  have hprod : vkProfile y * Real.sqrt (vkProfile y) ≤ δ * Real.log y :=
    hp.trans ((div_le_iff₀ hT).mp (hpowEq.le.trans hy.le))
  apply (div_le_iff₀ hT).mpr
  calc
    vkProfile y ^ 2 = (vkProfile y * Real.sqrt (vkProfile y)) * Real.sqrt (vkProfile y) := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt hΦ.le, pow_two]
    _ ≤ (δ * Real.log y) * Real.sqrt (vkProfile y) :=
      mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Close to the cutoff, the square-root correction pays for the entropy and
harmonic factors while leaving a positive square-root saving. -/
theorem endpoint_near_cost (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ y : ℝ in atTop, ∀ p : ℝ, vkProfile y / 2 ≤ p → p ≤ vkProfile y →
      A * (vkProfile y - p) ≤ Real.sqrt (vkProfile y) / 8 →
      Real.exp (-A * p - Real.sqrt p) * (2 + Real.log y + 5 * (1 + A * p + Real.sqrt p)) ≤
        (13 + 5 * A) * Real.exp (-A * vkProfile y - Real.sqrt (vkProfile y) / 8) := by
  have hloglog : Tendsto (fun y : ℝ => Real.log (Real.log y)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [vkProfile_dominates_logLog_sq (1 / 64) (by norm_num),
    hloglog.eventually (eventually_ge_atTop (1 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))]
    with y hdom hll hly hV p hp1 hp2 hgap
  let V := vkProfile y
  change (Real.log (Real.log y)) ^ 2 ≤ 1 / 64 * V at hdom
  change 1 ≤ Real.log (Real.log y) at hll
  change 0 ≤ V at hV
  change V / 2 ≤ p at hp1
  change p ≤ V at hp2
  change A * (V - p) ≤ Real.sqrt V / 8 at hgap
  have hp : 0 ≤ p := by linarith
  have hly0 : 0 < Real.log y := by linarith
  have hVlog : V ≤ Real.log y := by
    calc
      V ≤ (Real.log y) ^ (3 / 5 : ℝ) := div_le_self
        (Real.rpow_nonneg hly0.le _) (Real.one_le_rpow hll (by norm_num))
      _ ≤ (Real.log y) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hly (by norm_num)
      _ = Real.log y := Real.rpow_one _
  have hpsqrt : Real.sqrt p ≤ Real.log y := by
    calc
      Real.sqrt p ≤ Real.sqrt ((Real.log y) ^ 2) :=
        Real.sqrt_le_sqrt (le_trans (hp2.trans hVlog)
          (by nlinarith only [mul_nonneg (sub_nonneg.mpr hly) hly0.le]))
      _ = _ := Real.sqrt_sq hly0.le
  have hhalf : Real.sqrt V ≤ 2 * Real.sqrt p := by
    calc
      Real.sqrt V ≤ Real.sqrt ((2 * Real.sqrt p) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith only [hp1, Real.sq_sqrt hp])
      _ = _ := Real.sqrt_sq (by positivity)
  have hscaled : (Real.log (Real.log y)) ^ 2 ≤ (Real.sqrt V / 8) ^ 2 := by
    nlinarith only [hdom, Real.sq_sqrt hV]
  have hlinear := Real.sqrt_le_sqrt hscaled
  rw [Real.sqrt_sq (by linarith : 0 ≤ Real.log (Real.log y)),
    Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt V / 8)] at hlinear
  have hlog : Real.log y ≤ Real.exp (Real.sqrt V / 8) := by
    simpa only [Real.exp_log hly0] using Real.exp_le_exp.mpr hlinear
  have hK : 0 ≤ 13 + 5 * A := by positivity
  have hcost : 2 + Real.log y + 5 * (1 + A * p + Real.sqrt p) ≤
      (13 + 5 * A) * Real.exp (Real.sqrt V / 8) := by
    calc
      _ ≤ (13 + 5 * A) * Real.log y := by
        linarith only [hly, hpsqrt, mul_le_mul_of_nonneg_left (hp2.trans hVlog) hA]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hK
  calc
    _ ≤ Real.exp (-A * p - Real.sqrt p) * ((13 + 5 * A) * Real.exp (Real.sqrt V / 8)) :=
      mul_le_mul_of_nonneg_left hcost (Real.exp_pos _).le
    _ = (13 + 5 * A) * Real.exp ((-A * p - Real.sqrt p) + Real.sqrt V / 8) := by
      rw [Real.exp_add]
      ring
    _ ≤ (13 + 5 * A) * Real.exp (-A * V - Real.sqrt V / 8) := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Real.exp_le_exp.mpr
      linarith only [hgap, hhalf, Real.sqrt_nonneg V]

/-- At rate A, a square-root correction in the uniform ordinary Mertens
bound leaves an integrable saving for the absolute first moment. -/
theorem errorEnvelope_eventually_le_vk_endpoint (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n
        (Real.exp (-A * vkProfile (N:ℝ) - Real.sqrt (vkProfile (N:ℝ)))) ≤
        2 + K * ((n:ℝ) * Real.exp (-A * vkProfile (n:ℝ) - Real.sqrt (vkProfile (n:ℝ)) / 8)) := by
  let B := A + 1
  let K := 13 + 5 * A
  have hB : 0 < B := by dsimp [B]; linarith
  have hK3 : 3 ≤ K := by dsimp [K]; linarith
  have hK : 0 ≤ K := by linarith
  let δ := 1 / (8 * B ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcancel : B ^ 2 * δ = 1 / 8 := by
    dsimp [δ]
    field_simp [hB.ne'] <;> ring
  obtain ⟨Y, hY⟩ := eventually_atTop.1
    (((vk_sq_div_log_eventual_le_sqrt δ hδ).and (endpoint_near_cost A hA.le)).and
      (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (1:ℝ))))
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨K, hK, ?_⟩
  filter_upwards [hnat.eventually (eventually_ge_atTop Y),
    hnat.eventually vk_eventual_relative_increment,
    hnat.eventually vkProfile_eventually_mono, eventually_ge_atTop (2:ℕ)]
    with N hNY hinc hmono hN n
  have hpos : 0 ≤ (n:ℝ) *
      Real.exp (-A * vkProfile (n:ℝ) - Real.sqrt (vkProfile (n:ℝ)) / 8) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  rw [errorEnvelope]
  split_ifs with hhead
  · linarith [mul_nonneg hK hpos]
  have hNn : N ≤ n := by omega
  have hxy : (N:ℝ) ≤ n := by exact_mod_cast hNn
  obtain ⟨⟨hslope, hcost⟩, hPone⟩ := hY (n:ℝ) (hNY.trans hxy)
  let P := vkProfile (n:ℝ)
  let p := vkProfile (N:ℝ)
  change 1 ≤ P at hPone
  have hP : 0 ≤ P := by linarith
  have hpxy : p ≤ P := hmono _ hxy
  have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnr : (0:ℝ) < n := by linarith
  have hT := Real.log_pos hn1
  have hS := Real.sqrt_nonneg P
  have hsquare := Real.sq_sqrt hP
  have hSP : Real.sqrt P ≤ P := by
    have h1 := Real.sqrt_le_sqrt hPone
    rw [Real.sqrt_one] at h1
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hS]
  by_cases hcut : (N:ℝ) ≤ (n:ℝ) * Real.exp (-B * P)
  · apply (min_le_left _ _).trans
    have he : Real.exp (-B * P) ≤ Real.exp (-A * P - Real.sqrt P / 8) := by
      apply Real.exp_le_exp.mpr
      dsimp [B]
      nlinarith
    have hx := hcut.trans (mul_le_mul_of_nonneg_left he hnr.le)
    change 3 * (N:ℝ) ≤ 2 + K * ((n:ℝ) * Real.exp (-A * P - Real.sqrt P / 8))
    linarith [mul_le_mul_of_nonneg_right hK3 hpos]
  · apply (min_le_right _ _).trans
    have hl := Real.log_lt_log (mul_pos hnr (Real.exp_pos _)) (lt_of_not_ge hcut)
    rw [Real.log_mul hnr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hspan : Real.log (n:ℝ) - Real.log (N:ℝ) ≤ B * P := by linarith
    have hd₀ : P - p ≤ P / Real.log (n:ℝ) * (B * P) :=
      (hinc _ hxy).trans (mul_le_mul_of_nonneg_left hspan (div_nonneg hP hT.le))
    have hd₁ : B * (P - p) ≤ Real.sqrt P / 8 := by
      calc
        B * (P - p) ≤ B * (P / Real.log (n:ℝ) * (B * P)) :=
          mul_le_mul_of_nonneg_left hd₀ hB.le
        _ = B ^ 2 * (P ^ 2 / Real.log (n:ℝ)) := by ring
        _ ≤ B ^ 2 * (δ * Real.sqrt P) := mul_le_mul_of_nonneg_left hslope (sq_nonneg B)
        _ = Real.sqrt P / 8 := by rw [← mul_assoc, hcancel]; ring
    have hAdiff : A * (P - p) ≤ Real.sqrt P / 8 := by
      have hh : A ≤ B := by dsimp [B]; linarith
      exact (mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hpxy)).trans hd₁
    have hpHalf : P / 2 ≤ p := by
      have hdiff : P - p ≤ Real.sqrt P / 8 := by
        have hB1 : 1 ≤ B := by dsimp [B]; linarith
        have h := mul_le_mul_of_nonneg_right hB1 (sub_nonneg.mpr hpxy)
        rw [one_mul] at h
        exact h.trans hd₁
      linarith [hSP]
    have hterm := hcost p hpHalf hpxy hAdiff
    have hlogcharge : Real.log (1 / Real.exp (-A * p - Real.sqrt p)) = A * p + Real.sqrt p := by
      rw [one_div, Real.log_inv, Real.log_exp]
      ring
    change 2 + (n:ℝ) *
      (Real.exp (-A * p - Real.sqrt p) * (2 + Real.log (n:ℝ)) +
       5 * (Real.exp (-A * p - Real.sqrt p) * (1 + Real.log (1 / Real.exp (-A * p - Real.sqrt p))))) ≤
      2 + K * ((n:ℝ) * Real.exp (-A * P - Real.sqrt P / 8))
    rw [hlogcharge]
    have hout := mul_le_mul_of_nonneg_left hterm hnr.le
    dsimp only [K]
    change (n:ℝ) * (Real.exp (-A * p - Real.sqrt p) *
      (2 + Real.log (n:ℝ) + 5 * (1 + A * p + Real.sqrt p))) ≤
      (n:ℝ) * ((13 + 5 * A) * Real.exp (-A * P - Real.sqrt P / 8)) at hout
    linarith only [hout]

end RiemannResearch.RH.QMertensFirstMoment
