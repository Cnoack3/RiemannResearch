import RiemannResearch.Analysis.MontgomeryLogMeanSquare
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Signed lower-order term in the archimedean Montgomery signal

The gamma factor at real part −1/2 centers the logarithmic signal at
k = log(2π). Its primitive keeps both endpoints of the positive-height
integral. The first term after (log T)² in its normalized energy is
−2(1+k) log T. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryLogMeanSquare

def centeredLogSquarePrimitive (k y : ℝ) : ℝ :=
  y*((Real.log y-k)^2-2*(Real.log y-k)+2)

/-- The integral endpoints are valid for arbitrary real centers. -/
theorem centered_log_mean_square_eq (k : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (Real.log (t+2)-k)^2) =
      centeredLogSquarePrimitive k (T+2)-centeredLogSquarePrimitive k 2 := by
  have hd (t : ℝ) (ht : t ∈ uIcc 0 T) :
      HasDerivAt (fun s : ℝ => centeredLogSquarePrimitive k (s+2)) ((Real.log (t+2)-k)^2) t := by
    rw [uIcc_of_le hT] at ht
    have h := (shifted_log_hasDerivAt ht.1).sub_const k
    have hp := ((hasDerivAt_id t).add_const 2).mul (((h.pow 2).sub (h.const_mul 2)).add_const 2)
    have hn : t+2 ≠ 0 := by linarith [ht.1]
    convert hp using 1 <;> first | rfl |
      (simp only [Pi.sub_apply, Pi.pow_apply, id_eq]; field_simp [hn]; ring)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((shifted_log_continuousOn hT).sub continuousOn_const).pow 2).intervalIntegrable

/-- Signed first correction to the mean square. In particular setting
k = log(2π) incorporates the constant in the gamma factor. -/
theorem centered_log_mean_square_coefficient (k : ℝ) :
    Tendsto (fun T : ℝ =>
      ((∫ t in (0 : ℝ)..T, (Real.log (t+2)-k)^2)/T - (Real.log T)^2)/Real.log T)
      atTop (𝓝 (-2*(1+k))) := by
  let L := Real.log
  let S := fun T : ℝ => Real.log (T+2)
  have hT0 : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hL0 : Tendsto (fun T : ℝ => (L T)⁻¹) atTop (𝓝 0) :=
    hT0.comp Real.tendsto_log_atTop
  have hδ : Tendsto (fun T : ℝ => S T-L T) atTop (𝓝 0) := by
    have h := ((Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp
      (show Tendsto (fun T : ℝ => 1+2*T⁻¹) atTop (𝓝 1) by
        simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hT0)))
    rw [Real.log_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    change Real.log (1+2*T⁻¹) = Real.log (T+2)-Real.log T
    rw [← Real.log_div (by linarith : T+2 ≠ 0) hT.ne']
    congr 1
    field_simp [hT.ne']
  have hSL : Tendsto (fun T : ℝ => S T / L T) atTop (𝓝 1) := by
    have h := (hδ.mul hL0).add (tendsto_const_nhds (x := (1:ℝ)))
    simp only [zero_mul,zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    change (S T-L T)*(L T)⁻¹+1 = S T/L T
    field_simp [show L T ≠ 0 by exact (Real.log_pos hT).ne']
    ring
  have hLT : Tendsto (fun T : ℝ => L T/T) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp Real.tendsto_log_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    simp only [Function.comp_def,pow_one,Real.exp_neg,Real.exp_log hT,div_eq_mul_inv,L]
  have hST : Tendsto (fun T : ℝ => S T/T) atTop (𝓝 0) := by
    have h := (hδ.mul hT0).add hLT
    simp only [zero_mul,zero_add] at h
    apply h.congr fun T => by change (S T-L T)*T⁻¹+L T/T = S T/T; ring
  let K := k^2+2*k+2
  have h2 : Tendsto (fun T : ℝ => 1+2*T⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hT0)
  have h := (((hδ.mul (hSL.add (tendsto_const_nhds (x := (1:ℝ))))).add
    (((tendsto_const_nhds (x := (2:ℝ))).mul hST).mul hSL)).sub
    (((tendsto_const_nhds (x := (2*(1+k)))).mul h2).mul hSL)).add
    (((tendsto_const_nhds (x := K)).mul h2).mul hL0)
  have hg := h.sub (((tendsto_const_nhds (x := centeredLogSquarePrimitive k 2)).mul hT0).mul hL0)
  simp only [zero_mul,mul_zero,mul_one,sub_zero,zero_sub,add_zero,
    show -(2*(1+k)) = -2*(1+k) by ring] at hg
  apply hg.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have hTp : 0 < T := zero_lt_one.trans hT
  have hLp : 0 < L T := Real.log_pos hT
  rw [centered_log_mean_square_eq k hTp.le]
  change (S T-L T)*(S T/L T+1)+2*(S T/T)*(S T/L T)-2*(1+k)*(1+2*T⁻¹)*(S T/L T)+
    K*(1+2*T⁻¹)*(L T)⁻¹-centeredLogSquarePrimitive k 2*T⁻¹*(L T)⁻¹ =
    ((centeredLogSquarePrimitive k (T+2)-centeredLogSquarePrimitive k 2)/T - (L T)^2)/(L T)
  rw [show centeredLogSquarePrimitive k (T+2) =
    (T+2)*((S T)^2-2*(1+k)*(S T)+K) by dsimp [centeredLogSquarePrimitive,S,K]; ring]
  field_simp [hTp.ne',hLp.ne']
  ring

end RiemannResearch.Analysis.MontgomeryLogMeanSquare
