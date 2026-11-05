/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DelayedContraction
import RiemannResearch.Analysis.StretchedExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Power-log cutoff transfer for a delayed Mertens estimate

For a prime error `exp(-c L^α)`, set `β = α/(1+α)` and let
`L = l * (s log s)^(1-β)`, with `s=T+6` and `l>0`.
Then `L^α=l^α (s log s)^β`.  The normalized profile increment is asymptotically at most `β*l` times `log s`, giving every coefficient strictly below `c^(1/(1+α))` from the finite-cutoff recurrence.
-/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RiemannResearch.Analysis

private theorem scaled_cutoff_small (β q l K : ℝ) (hβ : β < 1) (hq : q < β) :
    ∀ᶠ s : ℝ in atTop,
      ((3 * (l * logProductPower (1 - β) s) + K) / s) * Real.exp (q * Real.log s) ≤ 1 / 8 := by
  have hU := (isLittleO_log_rpow_rpow_atTop (1 - β) (sub_pos.mpr hq)).tendsto_div_nhds_zero
  have hV := tendsto_rpow_neg_atTop (sub_pos.mpr (hq.trans hβ))
  have hsum := (hU.const_mul (3 * l)).add (hV.const_mul K)
  simp only [mul_zero, add_zero] at hsum
  filter_upwards [(tendsto_order.1 hsum).2 (1 / 8 : ℝ) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with s hs hs1
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  have hlog := Real.log_nonneg hs1
  have hpow : s ^ (1 - β) * s ^ q / s = (s ^ (β - q))⁻¹ := by
    rw [← Real.rpow_add hs0, ← Real.rpow_neg hs0.le,
      show -(β - q) = (1 - β + q) - 1 by ring, Real.rpow_sub hs0, Real.rpow_one]
  have hdiv : s ^ q / s = s ^ (-(1 - q)) := by
    rw [show -(1 - q) = q - 1 by ring, Real.rpow_sub hs0, Real.rpow_one]
  have hexp : Real.exp (q * Real.log s) = s ^ q := by rw [Real.rpow_def_of_pos hs0, mul_comm]
  calc
    _ = 3 * l * (Real.log s) ^ (1 - β) * (s ^ (1 - β) * s ^ q / s) + K * (s ^ q / s) := by
      rw [hexp, logProductPower, Real.mul_rpow hs0.le hlog]; ring
    _ = 3 * l * ((Real.log s) ^ (1 - β) / s ^ (β - q)) + K * s ^ (-(1 - q)) := by
      rw [hpow, hdiv]; ring
    _ ≤ _ := hs.le

/-- The tangent-line bound for logarithms, with positive arguments only. -/
private theorem log_sub_le_div_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a - b) / b := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  rwa [sub_div, div_self hb.ne']

/-- Across a cutoff `l (s log s)^(1-β)` the leading logarithmic
increment is at most `β*l`. This uses `1-u ≤ -log u` at the ratio of
successive profiles and two applications of the tangent bound for `log`. -/
private theorem scaled_profile_sharp_shift (β l k : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hl : 0 < l) (hk : β*l < k) :
    ∀ᶠ s : ℝ in atTop,
      logProductPower β s - logProductPower β (s-l*logProductPower (1-β) s-Real.log 2)
        ≤ k * Real.log s := by
  let W := logProductPower (1-β)
  let v := fun s : ℝ => s-l*W s-Real.log 2
  have hWs : Tendsto (fun s : ℝ => W s/s) atTop (𝓝 0) := by
    apply ((isLittleO_log_rpow_rpow_atTop (1-β) hβ).tendsto_div_nhds_zero).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    have hs0 := zero_lt_one.trans hs
    have he : s^(1-β)/s = (s^β)⁻¹ := by
      calc
        s ^ (1-β) / s = s ^ ((1-β)-1) := by
          rw [Real.rpow_sub hs0 (1-β) 1, Real.rpow_one]
        _ = s ^ (-β) := by congr 1; ring
        _ = (s^β)⁻¹ := Real.rpow_neg hs0.le β
    calc
      (Real.log s)^(1-β)/s^β = (Real.log s)^(1-β)*(s^(1-β)/s) := by rw [he]; ring
      _ = W s/s := by
        dsimp [W, logProductPower]
        rw [Real.mul_rpow hs0.le (Real.log_pos hs).le]; ring
  have hinvs : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hconst (a : ℝ) : Tendsto (fun _ : ℝ => a) atTop (𝓝 a) := tendsto_const_nhds
  have hraw : Tendsto (fun s : ℝ => 1 - (l*(W s / s) + Real.log 2 * s⁻¹)) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero,sub_zero] using
      (hconst 1).sub ((hWs.const_mul l).add (hinvs.const_mul (Real.log 2)))
  have hvr : Tendsto (fun s : ℝ => v s/s) atTop (𝓝 1) := by
    apply hraw.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    dsimp [v]; field_simp <;> ring
  have hrv : Tendsto (fun s : ℝ => s/v s) atTop (𝓝 1) := by
    simpa only [inv_div,inv_one] using hvr.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hvtop : Tendsto v atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (2*b),
      (tendsto_order.1 hvr).1 (1/2:ℝ) (by norm_num)] with s hs0 hsb hv
    have h := (lt_div_iff₀ hs0).mp hv
    linarith
  have hWtop : Tendsto W atTop atTop := tendsto_logProductPower_atTop (1-β) (by linarith)
  have hA : Tendsto (fun s : ℝ => l+Real.log 2/W s) atTop (𝓝 l) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero, Function.comp_apply] using
      (hconst l).add ((tendsto_inv_atTop_zero.comp hWtop).const_mul (Real.log 2))
  have hB : Tendsto (fun s : ℝ => 1+1/Real.log (v s)) atTop (𝓝 1) := by
    simpa only [one_div,add_zero,Function.comp_apply] using (hconst 1).add
      (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hvtop))
  have hlim := ((hA.const_mul β).mul hrv).mul hB
  simp only [mul_one] at hlim
  filter_upwards [eventually_gt_atTop (1:ℝ), hvtop.eventually (eventually_gt_atTop (1:ℝ)),
    (tendsto_order.1 hlim).2 k hk] with s hs1 hv1 hclose
  let z := logProductPower β s
  let w := logProductPower β (v s)
  change z-w ≤ k*Real.log s
  change β*(l+Real.log 2/W s)*(s/v s)*(1+1/Real.log (v s)) < k at hclose
  have hs0 := zero_lt_one.trans hs1
  have hv0 := zero_lt_one.trans hv1
  have hls := Real.log_pos hs1
  have hlv := Real.log_pos hv1
  have hz : 0 < z := Real.rpow_pos_of_pos (mul_pos hs0 hls) _
  have hw : 0 < w := Real.rpow_pos_of_pos (mul_pos hv0 hlv) _
  have hW : 0 < W s := Real.rpow_pos_of_pos (mul_pos hs0 hls) _
  have hp : z-w ≤ z*(Real.log z-Real.log w) := by
    have h := (le_div_iff₀ hz).mp (log_sub_le_div_sub hw hz)
    nlinarith only [h]
  have logP {t : ℝ} (ht : 1 < t) : Real.log (logProductPower β t) =
      β*(Real.log t+Real.log (Real.log t)) := by
    have ht0 := zero_lt_one.trans ht
    have hlog := Real.log_pos ht
    rw [logProductPower, Real.log_rpow (mul_pos ht0 hlog), Real.log_mul ht0.ne' hlog.ne']
  have hx := log_sub_le_div_sub hs0 hv0
  have hy := log_sub_le_div_sub hls hlv
  have hlogs : (Real.log s-Real.log (v s))+(Real.log (Real.log s)-Real.log (Real.log (v s))) ≤
      (s-v s)/(v s) * (1 + 1/Real.log (v s)) := by
    calc
      _ ≤ (s-v s)/(v s) + ((s-v s)/(v s))/Real.log (v s) :=
        add_le_add hx (hy.trans (div_le_div_of_nonneg_right hx hlv.le))
      _ = _ := by ring
  have hzW : z*W s = s*Real.log s := by
    dsimp [z,W,logProductPower]
    rw [← Real.rpow_add (mul_pos hs0 hls), show β+(1-β) = 1 by ring, Real.rpow_one]
  have hspread : (s-v s)/(v s) = ((l+Real.log 2/W s)*W s)/(v s) := by
    apply congrArg (fun t : ℝ => t / v s)
    dsimp [v]
    rw [add_mul,div_mul_cancel₀ _ hW.ne']; ring
  calc
    z-w ≤ z*(Real.log z-Real.log w) := hp
    _ = (z*β)*((Real.log s-Real.log (v s))+(Real.log (Real.log s)-Real.log (Real.log (v s)))) := by
      change z*(Real.log (logProductPower β s)-Real.log (logProductPower β (v s))) = _
      rw [logP hs1, logP hv1]; ring
    _ ≤ (z*β)*((s-v s)/(v s) * (1 + 1/Real.log (v s))) :=
      mul_le_mul_of_nonneg_left hlogs (mul_nonneg hz.le hβ.le)
    _ = (β*(l+Real.log 2/W s)/(v s)*(1+1/Real.log (v s)))*(z*W s) := by rw [hspread]; ring
    _ = (β*(l+Real.log 2/W s)*(s/v s)*(1+1/Real.log (v s)))*Real.log s := by rw [hzW]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hclose.le hls.le

private theorem scaled_cutoff_stage (α β c d l k K : ℝ)
    (hβ : 0 < β) (hβ2 : 2 * β < 1) (hα : (1 - β) * α = β)
    (hd : 0 < d) (hl : 0 < l) (hlk : β*l < k) (hdk : d * k < β)
    (hdc : d ≤ c * l ^ α) (hK : 0 ≤ K) :
    ∀ᶠ s : ℝ in atTop,
      let z := logProductPower β s
      let L := l * logProductPower (1 - β) s
      let v := s - L - Real.log 2
      12 ≤ s ∧ 1 ≤ L ∧ 6 ≤ v ∧ d * z ≤ L ∧ d * z ≤ c * L ^ α ∧
      ((3 * L + K) / (s - 6)) * Real.exp (d * (z - logProductPower β v)) ≤ 1 / 2 := by
  have hβ1 : β < 1 := by linarith
  have hW := tendsto_logProductPower_atTop (1 - β) (by linarith)
  have hR := tendsto_logProductPower_atTop (1 - 2 * β) (by linarith)
  filter_upwards [eventually_ge_atTop (12 : ℝ),
    hW.eventually (eventually_ge_atTop (1 / l)),
    scaled_profile_sharp_shift β l k hβ hβ1 hl hlk,
    hR.eventually (eventually_ge_atTop (d / l)),
    scaled_cutoff_small β (d * k) l K hβ1 hdk] with s hs hLW hsharp hRsmall hsmall
  let W := logProductPower (1 - β) s
  let z := logProductPower β s
  let L := l * W
  let v := s - L - Real.log 2
  change 12 ≤ s ∧ 1 ≤ L ∧ 6 ≤ v ∧ d*z ≤ L ∧ d*z ≤ c*L^α ∧
    (3*L+K)/(s-6)*Real.exp (d*(z-logProductPower β v)) ≤ 1/2
  have hs0 : 0 < s := by linarith
  have hslog : 0 < Real.log s := Real.log_pos (by linarith)
  have hbase : 0 < s * Real.log s := mul_pos hs0 hslog
  have hz0 : 0 ≤ z := Real.rpow_nonneg hbase.le _
  have hW0 : 0 ≤ W := Real.rpow_nonneg hbase.le _
  have hL1 : 1 ≤ L := by simpa only [L, W, mul_comm l] using (div_le_iff₀ hl).mp hLW
  have hE1 : 1 ≤ Real.exp ((d*k)*Real.log s) := Real.one_le_exp_iff.mpr
    (mul_nonneg (mul_nonneg hd.le ((mul_pos hβ hl).trans hlk).le) hslog.le)
  have hA : 0 ≤ 3*L+K := by linarith
  change (3*L+K)/s * Real.exp ((d*k)*Real.log s) ≤ 1/8 at hsmall
  have hscaled : (3*L+K)*Real.exp ((d*k)*Real.log s) ≤ s/8 := by
    rw [div_mul_eq_mul_div] at hsmall
    have h := (div_le_iff₀ hs0).mp hsmall
    linarith
  have hLsize := (le_mul_of_one_le_right hA hE1).trans hscaled
  have hl2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have hl2' := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hv6 : 6 ≤ v := by dsimp [v]; linarith
  change z - logProductPower β v ≤ k * Real.log s at hsharp
  have hwei := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsharp hd.le)
  have hforce : d*z ≤ L := by
    have h := (div_le_iff₀ hl).mp hRsmall
    have h' := mul_le_mul_of_nonneg_right h hz0
    have hZW : logProductPower (1-2*β) s * z = W := by
      dsimp [z,W,logProductPower]
      rw [← Real.rpow_add hbase, show 1-2*β+β = 1-β by ring]
    calc
      d*z ≤ (logProductPower (1-2*β) s * l) * z := h'
      _ = l * (logProductPower (1-2*β) s * z) := by ring
      _ = L := by rw [hZW]
  have hLpow : L ^ α = l ^ α * z := by
    dsimp [L,W,z,logProductPower]
    rw [Real.mul_rpow hl.le (Real.rpow_nonneg hbase.le _), ← Real.rpow_mul hbase.le, hα]
  refine ⟨hs,hL1,hv6,hforce,?_,?_⟩
  · rw [hLpow, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hdc hz0
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by linarith : 0 < s-6)).mpr
    rw [← mul_assoc] at hwei
    have h := (mul_le_mul_of_nonneg_left hwei hA).trans hscaled
    linarith

/-- For the power-log choice of cutoff, `d` is admissible whenever
`d ≤ c l^α` and `d l < 1`. The relation `(1-β)α=β` identifies the rate
from the input exponent, and `0 < β < 1/2` covers every `0 < α < 1`. -/
theorem stretched_envelope_bound_scaled (E : ℝ → ℝ) (α β c D K d l : ℝ)
    (hβ : 0 < β) (hβ2 : 2*β < 1) (hα : (1-β)*α = β)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hd : 0 < d) (hl : 0 < l)
    (hdl : d*l < 1) (hdc : d ≤ c*l^α)
    (hE0 : ∀ t : ℝ, 0 ≤ E t) (hE1 : ∀ t : ℝ, E t ≤ 1)
    (hrec : ∀ T L : ℝ, 0 < T → 0 ≤ L → Real.log 2 ≤ T-L →
      E T ≤ ((3*L+K)*E (T-L-Real.log 2) + 3*Real.exp (-L) +
        3*D*Real.exp (-c*L^α))/T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      E T ≤ B * Real.exp (-d * logProductPower β (T+6)) := by
  have hslack := mul_lt_mul_of_pos_left hdl hβ
  have hr : (β*l)*d < β := by nlinarith only [hslack]
  obtain ⟨k, hlk, hk⟩ := exists_between ((lt_div_iff₀ hd).mpr hr)
  have hdk : d*k < β := by simpa only [mul_comm d] using (lt_div_iff₀ hd).mp hk
  obtain ⟨S, hS⟩ := eventually_atTop.mp (scaled_cutoff_stage α β c d l k K hβ hβ2 hα hd hl hlk hdk hdc hK)
  let P := fun t : ℝ => logProductPower β (t+6)
  let L := fun t : ℝ => l*logProductPower (1-β) (t+6)
  let r := fun t : ℝ => t-L t-Real.log 2
  let F := fun t : ℝ => E t * Real.exp (d*P t)
  let T₀ := max S 6
  have hstage (t : ℝ) (ht : T₀ < t) :
      12 ≤ t+6 ∧ 1 ≤ L t ∧ 6 ≤ r t + 6 ∧ d*P t ≤ L t ∧ d*P t ≤ c*(L t)^α ∧
      ((3*L t+K)/t) * Real.exp (d*(P t-P (r t))) ≤ 1/2 := by
    have hSt : S ≤ t := (le_max_left _ _).trans ht.le
    have h := hS (t+6) (by linarith)
    simpa only [P,L,r,sub_add_eq_add_sub,sub_sub,add_sub_cancel_right] using h
  have hdelay (t : ℝ) (ht : T₀ < t) : 0 ≤ r t ∧ r t ≤ t-1 := by
    obtain ⟨_, hL, hr, _⟩ := hstage t ht
    constructor
    · linarith
    · dsimp [r]; linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  have hstep (t : ℝ) (ht : T₀ < t) : F t ≤ (1/2:ℝ)*F (r t)+(3+3*D) := by
    obtain ⟨ht12,hL,hr,h1,h2,hA⟩ := hstage t ht
    have ht0 : 0 < t := by linarith
    have hr' : Real.log 2 ≤ t-L t := by dsimp [r] at hr; linarith
    have hF0 : 0 ≤ F (r t) := mul_nonneg (hE0 _) (Real.exp_pos _).le
    have hsource := mul_le_mul_of_nonneg_right (hrec t (L t) ht0 (by linarith) hr')
      (Real.exp_pos (d*P t)).le
    have hweight : E (r t) * Real.exp (d*P t) = F (r t) * Real.exp (d*(P t-P (r t))) := by
      dsimp only [F]
      rw [mul_assoc, ← Real.exp_add,
        show d * P (r t) + d * (P t - P (r t)) = d * P t by ring]
    have hw1 : Real.exp (-(L t)) * Real.exp (d*P t) ≤ 1 := by
      rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; linarith
    have hw2 : Real.exp (-c*(L t)^α) * Real.exp (d*P t) ≤ 1 := by
      rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; linarith
    calc
      F t ≤ (((3*L t+K)*E (r t)+3*Real.exp (-L t)+3*D*Real.exp (-c*(L t)^α))/t)*Real.exp (d*P t) := hsource
      _ = ((3*L t+K)*(E (r t)*Real.exp (d*P t)) + 3*(Real.exp (-L t)*Real.exp (d*P t)) +
        3*D*(Real.exp (-c*(L t)^α)*Real.exp (d*P t)))/t := by ring
      _ ≤ ((3*L t+K)*(F (r t)*Real.exp (d*(P t-P (r t))))+3+3*D)/t := by
        rw [hweight]
        apply div_le_div_of_nonneg_right _ ht0.le
        have hh := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ 3*D by positivity)
        linarith
      _ = (((3*L t+K)/t)*Real.exp (d*(P t-P (r t)))) * F (r t) + (3+3*D)/t := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hA hF0)
        (div_le_self (by positivity) (by linarith))
  have hbase (t : ℝ) (ht : 0 ≤ t) (hle : t ≤ T₀) : F t ≤ Real.exp (d*P T₀) := by
    calc
      F t ≤ Real.exp (d*P t) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hE1 t) (Real.exp_pos _).le
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (logProductPower_mono β hβ.le (by linarith) (by linarith)) hd.le)
  let B := max (Real.exp (d*P T₀)) (2*(3+3*D))
  refine ⟨B, (Real.exp_pos _).le.trans (le_max_left _ _), fun t ht => ?_⟩
  have h := delayed_contraction_bound F r T₀ _ (3+3*D) hbase hdelay hstep t ht
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-d*P t)).le
  have he : Real.exp (d*P t)*Real.exp (-d*P t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  simpa only [F,mul_assoc,he,mul_one] using h'

/-- The exact algebraic relation between a rate and its scaled cutoff. -/
theorem stretched_rate_gain_iff (α c d : ℝ) (ha : 0 < α) (hc : 0 < c) (hd : 0 < d) :
    d * (d/c) ^ (1/α) < 1 ↔ d < c ^ (1/(1+α)) := by
  have hsum : 0 < 1+α := by linarith
  have hq := div_pos hd hc
  have hbase := mul_pos hd (Real.rpow_pos_of_pos hq (1/α))
  have hroot := Real.rpow_pos_of_pos hc (1/(1+α))
  have hD : d ^ (1+α) = d*d^α := by rw [Real.rpow_add hd, Real.rpow_one]
  have hpow : (d*(d/c)^(1/α))^α = d^(1+α)/c := by
    rw [Real.mul_rpow hd.le (Real.rpow_nonneg hq.le _), ← Real.rpow_mul hq.le,
      one_div_mul_cancel ha.ne', Real.rpow_one, hD]
    ring
  have hright : (c^(1/(1+α)))^(1+α) = c := by
    rw [← Real.rpow_mul hc.le, one_div_mul_cancel hsum.ne', Real.rpow_one]
  calc
    _ ↔ (d*(d/c)^(1/α))^α < (1:ℝ)^α :=
      (Real.rpow_lt_rpow_iff hbase.le zero_le_one ha).symm
    _ ↔ d^(1+α) < c := by rw [hpow, Real.one_rpow, div_lt_one hc]
    _ ↔ _ := by
      simpa only [hright] using (Real.rpow_lt_rpow_iff hd.le hroot.le hsum)

/-- All coefficients strictly below `c^(1/(1+α))` are accessible
by a choice of cutoff multiplier. The condition is written in a form that
also identifies the multiplier used in the proof. -/
theorem stretched_envelope_bound_at_rate (E : ℝ → ℝ) (α β c D K d : ℝ)
    (hβ : 0 < β) (hβ2 : 2*β < 1) (hα : (1-β)*α = β)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hd : 0 < d) (hc : 0 < c)
    (hgain : d < c ^ (1 / (1 + α)))
    (hE0 : ∀ t : ℝ, 0 ≤ E t) (hE1 : ∀ t : ℝ, E t ≤ 1)
    (hrec : ∀ T L : ℝ, 0 < T → 0 ≤ L → Real.log 2 ≤ T-L →
      E T ≤ ((3*L+K)*E (T-L-Real.log 2) + 3*Real.exp (-L) +
        3*D*Real.exp (-c*L^α))/T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      E T ≤ B * Real.exp (-d * logProductPower β (T+6)) := by
  have ha : 0 < α := by
    by_contra! h
    have hbad := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1-β) h
    linarith only [hbad,hα,hβ]
  have hαne := ha.ne'
  let l := (d / c) ^ (1 / α)
  have hdc : c*l^α = d := by
    dsimp [l]
    rw [← Real.rpow_mul (div_nonneg hd.le hc.le), one_div_mul_cancel hαne, Real.rpow_one]
    field_simp
  exact stretched_envelope_bound_scaled E α β c D K d l hβ hβ2 hα hD hK hd
    (Real.rpow_pos_of_pos (div_pos hd hc) _) ((stretched_rate_gain_iff α c d ha hc hd).2 hgain)
    hdc.ge hE0 hE1 hrec

/-- The logarithmic-time profile obtained from the classical square-root prime error. -/
def cubeRootLogProfile (T : ℝ) : ℝ := logProductPower (1 / 3) (T + 6)

/-- Taking a unit cutoff multiplier specializes the power transfer to the cubic
profile. The full family of coefficients follows from `stretched_envelope_bound_at_rate`. -/
theorem sqrt_stretched_envelope_bound_at_rate
    (E : ℝ → ℝ) (c D K d : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hd : 0 < d) (hdc : d ≤ c) (hdsmall : d < 1 / 6)
    (hE0 : ∀ t : ℝ, 0 ≤ E t) (hE1 : ∀ t : ℝ, E t ≤ 1)
    (hrec : ∀ T L : ℝ, 0 < T → 0 ≤ L → Real.log 2 ≤ T - L →
      E T ≤ ((3 * L + K) * E (T - L - Real.log 2) +
        3 * Real.exp (-L) + 3 * D * Real.exp (-c * L ^ (1 / 2 : ℝ))) / T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T → E T ≤ B * Real.exp (-d * cubeRootLogProfile T) :=
  stretched_envelope_bound_scaled E (1 / 2) (1 / 3) c D K d 1
    (by norm_num) (by norm_num) (by norm_num) hD hK hd zero_lt_one
    (by linarith) (by simpa only [Real.one_rpow, mul_one] using hdc) hE0 hE1 hrec

end RiemannResearch.Analysis
