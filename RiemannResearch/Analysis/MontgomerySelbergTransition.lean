import RiemannResearch.Analysis.MontgomeryReflectedDefectRate
import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryHorizontalPairing
import RiemannResearch.Analysis.WeightedSqrtTransfer
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Reflected Selberg transfer for the raw Montgomery form factor

The source complex estimate is BGSTB, corrected equation (3.5),
https://arxiv.org/html/2501.14545v3#S3.E5 . Its individual error and the
reflected horizontal defect both contribute at the scale 1/√log T at the
transition. The source estimate and positive Selberg exponent are explicit
hypotheses. -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open ActualZeroOrdinate MontgomeryHorizontalTransfer MontgomeryFormFactor

/-- Reflection removes the logarithmic loss in the shrinking frequency range:
the condition in phase units is (α log T)^4 = o((log T)^3). -/
theorem sqrt_formFactor_difference_tendsto_zero_of_reflectedSelberg
    {a : ℝ} (ha : 0 < a) (hS : UniformSelbergDensity a) (α : ℝ → ℝ)
    (hsmall : Tendsto (fun T : ℝ => (α T)^4 * Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => |Real.sqrt (sharpFormFactor T (α T)) -
      Real.sqrt (formFactor T (α T))|) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := eventually_horizontalDefect_reflected_selberg ha hS
  have hfirst : Tendsto (fun T : ℝ => (1 / a^2) / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have ht := (hfirst.add (hsmall.div_const (a^4))).const_mul C
  simp only [zero_div, add_zero, mul_zero] at ht
  have hlim := (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp ht
  simp only [Function.comp_def, Real.sqrt_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hlim
  filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hsmall.eventually_le_const (by positivity : (0:ℝ) < (a/8)^4)] with T hbound hL hs
  let L := Real.log T
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hpow : |α T|^4 ≤ (a/8)^4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (α T)^4)]
    exact (le_mul_of_one_le_right (by positivity) hL).trans hs
  have hband : |α T| ≤ a/8 := by
    by_contra! hx
    have h1 := (sq_lt_sq₀ (by positivity : 0 ≤ a/8) (abs_nonneg _)).2 hx
    have h2 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).2 h1
    rw [← pow_mul, ← pow_mul] at h2
    exact (not_lt_of_ge hpow) h2
  have hf : |α T * L| ≤ a * L / 8 := by
    rw [abs_mul, abs_of_pos hLpos]
    calc
      _ ≤ (a/8)*L := mul_le_mul_of_nonneg_right hband hLpos.le
      _ = _ := by ring
  apply (sqrt_horizontal_error T (α T)).trans (Real.sqrt_le_sqrt _)
  apply (hbound (α T) hf).trans_eq
  change C * (1/(a^2*L) + (α T*L)^4/(a^4*L^3)) =
    C * ((1/a^2)/L + (α T)^4*L/a^4)
  field_simp [ha.ne', hLpos.ne']

/-- The corrected complex pair estimate transfers to actual ordinates at
the transition with a constant uniform on every bounded interval of shifts. -/
theorem raw_transition_uniform_rate_of_reflectedSelberg {a : ℝ}
    (ha : 0 < a) (hS : UniformSelbergDensity a)
    (hMT : CorrectedComplexFormFactorEstimate) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |formFactor T (transitionFrequency c T) - Real.exp (-c)| ≤
        K / Real.sqrt (Real.log T) := by
  obtain ⟨C, hC, hcomplex⟩ := hMT
  obtain ⟨D, hD, hdefect⟩ := eventually_horizontalDefect_reflected_selberg ha hS
  let H := C * (Real.exp A + 1)
  let M := Real.sqrt (Real.exp A + 1 + H)
  let B := Real.sqrt (D * (1/a^2 + 1/a^4))
  have hH : 0 ≤ H := mul_nonneg hC (by positivity)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  refine ⟨B^2 + 2*M*B + H + 1, by positivity, ?_⟩
  filter_upwards [hcomplex, hdefect, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 0 A),
    (loglog_pow_div_log_tendsto_zero 2).eventually_le_const zero_lt_one,
    (loglog_pow_div_log_tendsto_zero 1).eventually_le_const
      (by positivity : (0:ℝ) < a/8)] with T hcpl hd hT hL1 hℓb hℓ2 hℓa
  intro c hc
  let L := Real.log T
  let ℓ := Real.log L
  let α := transitionFrequency c T
  let u := (ℓ+c)/2
  let r := 1 / Real.sqrt L
  have hL : 0 < L := Real.log_pos hT
  change max 0 A ≤ ℓ at hℓb
  change ℓ^2/L ≤ 1 at hℓ2
  simp only [pow_one] at hℓa
  change ℓ/L ≤ a/8 at hℓa
  have hℓA := (le_max_right 0 A).trans hℓb
  have hℓ := (le_max_left 0 A).trans hℓb
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [(abs_le.mp hc).1]
  have huℓ : u ≤ ℓ := by dsimp [u]; linarith [(abs_le.mp hc).2]
  have hℓsq : ℓ^2 ≤ L := by simpa using (div_le_iff₀ hL).mp hℓ2
  have hℓroot : ℓ ≤ Real.sqrt L := (sq_le_sq₀ hℓ (Real.sqrt_nonneg _)).mp
    (by simpa only [Real.sq_sqrt hL.le] using hℓsq)
  have hroot := Real.sqrt_pos.2 hL
  have hroot1 : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := (div_le_iff₀ hroot).2 (by simpa using hroot1)
  have hαu : α*L = u := div_mul_cancel₀ _ hL.ne'
  have hα0 : 0 ≤ α := div_nonneg hu0 hL.le
  have hαr : α ≤ r := by
    change u/L ≤ 1/Real.sqrt L
    rw [div_le_div_iff₀ hL hroot]
    calc
      u * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
        mul_le_mul_of_nonneg_right (huℓ.trans hℓroot) hroot.le
      _ = 1*L := by rw [← sq, Real.sq_sqrt hL.le, one_mul]
  have hband : |α*L| ≤ a*L/8 := by
    rw [hαu, abs_of_nonneg hu0]
    have h := (div_le_iff₀ hL).mp hℓa
    linarith
  have hu2 := (sq_le_sq₀ hu0 hℓ).2 huℓ
  have hu4 : u^4 ≤ L^2 := by
    have h := (sq_le_sq₀ (sq_nonneg u) hL.le).2 (hu2.trans hℓsq)
    simpa only [← pow_mul] using h
  have hsum : (1/(a^2*L) + u^4/(a^4*L^3)) ≤ (1/a^2 + 1/a^4)/L := by
    calc
      _ ≤ 1/(a^2*L) + L^2/(a^4*L^3) := add_le_add le_rfl
        (div_le_div_of_nonneg_right hu4 (by positivity : 0 ≤ a^4 * L^3))
      _ = _ := by field_simp [ha.ne', hL.ne']
  have hdef := hd α hband
  change horizontalDefect T α ≤ D * (1/(a^2*L) + (α*L)^4/(a^4*L^3)) at hdef
  rw [hαu] at hdef
  have hBr : 0 ≤ B*r := mul_nonneg hB hr
  have hsq : (B*r)^2 = D*((1/a^2 + 1/a^4)/L) := by
    dsimp only [B,r]
    rw [mul_pow, Real.sq_sqrt (by positivity), div_pow, one_pow, Real.sq_sqrt hL.le]
    ring
  have hdiff : |Real.sqrt (formFactor T α) - Real.sqrt (sharpFormFactor T α)| ≤ B*r := by
    rw [abs_sub_comm, ← Real.sqrt_sq hBr]
    exact (sqrt_horizontal_error T α).trans (Real.sqrt_le_sqrt
      ((hdef.trans (mul_le_mul_of_nonneg_left hsum hD.le)).trans_eq hsq.symm))
  have hsp : Real.exp (-c) ≤ Real.exp A := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hc).1])
  have herror : |sharpFormFactor T α - (Real.exp (-c) + α)| ≤ H*r := by
    have he := hcpl α ⟨hα0, hαr.trans hr1⟩
    dsimp only at he
    rw [transition_spike c T hT] at he
    exact he.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hsp (le_refl (1:ℝ))) hC) hroot.le).trans_eq (by dsimp [H,r]; ring))
  have hpeak : Real.sqrt (sharpFormFactor T α) ≤ M := by
    apply Real.sqrt_le_sqrt
    have hh : H*r ≤ H := by simpa using mul_le_mul_of_nonneg_left hr1 hH
    linarith only [(abs_le.mp herror).2, hsp, hαr, hr1, hh]
  have hpair := WeightedSqrtTransfer.abs_sub_le_of_sqrt (formFactor_nonneg hT α)
    (MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α) (sq_nonneg (B*r))
    (by rwa [Real.sqrt_sq hBr])
  rw [Real.sqrt_sq hBr] at hpair
  have hr2 : r^2 ≤ r := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1)]
  have hraw : |formFactor T α - sharpFormFactor T α| ≤ (B^2+2*M*B)*r := by
    apply hpair.trans
    rw [mul_pow]
    calc
      _ ≤ B^2*r + (2*M)*(B*r) := add_le_add
        (mul_le_mul_of_nonneg_left hr2 (sq_nonneg B))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpeak (by norm_num)) hBr)
      _ = _ := by ring
  have htri := (abs_add_le (formFactor T α - sharpFormFactor T α)
    (sharpFormFactor T α - (Real.exp (-c) + α))).trans (add_le_add hraw herror)
  calc
    _ = |((formFactor T α - sharpFormFactor T α) +
        (sharpFormFactor T α - (Real.exp (-c) + α))) + α| := by congr 1; ring
    _ ≤ ((B^2+2*M*B)*r + H*r) + r := (abs_add_le _ _).trans
      (add_le_add htri (by rwa [abs_of_nonneg hα0]))
    _ = _ := by dsimp only [r]; ring

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
