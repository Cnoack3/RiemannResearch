/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalTransition
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A logarithmic layer above the support-one edge

Conditional transfer of the prime mean square, the diagonal, and the sharp
complex-zero pair statistic. The smoothing width is chosen as x/log T.

The intended M is the time integral from 0 to T of the squared prime
Dirichlet series with coefficients Λ(n) min(n/x,x/n) / √n, and D is the
sum of their squares. The three finite analytic estimates are explicit
arguments. The proposed time-smoothing argument uses the averaged sieve in
Languasco–Perelli–Zaccagnini, Lemma 6, https://arxiv.org/pdf/1311.0597 .
The sharp energy comparison uses Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh,
Lemmas 1 and 4, https://arxiv.org/pdf/2306.04799 , with the corrected
expansion at https://arxiv.org/html/2501.14545v3#S3.E4 .
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryHorizontalTransfer

/-- The modulus of the smoothing remainder tends to zero at its left endpoint. -/
theorem edgeSmoothingModulus_tendsto {ι : Type*} {l : Filter ι} {y : ι → ℝ}
    (hy : Tendsto y l (𝓝 0)) :
    Tendsto (fun i => y i * (1 + Real.log (1 / y i))) l (𝓝 0) := by
  have hh := (Real.continuous_mul_log.continuousAt (x := 0)).tendsto.comp hy
  simp only [Function.comp_def, zero_mul] at hh
  simpa only [one_div, Real.log_inv, mul_add, mul_sub, mul_one, mul_neg, ← sub_eq_add_neg, sub_zero]
    using hy.sub hh

/-- The edge modulus increases on the full finite-frequency range. -/
theorem edgeSmoothingModulus_le {y h : ℝ} (hy : 0 < y) (hyh : y ≤ h) (hh1 : h ≤ 1) :
    y * (1 + Real.log (1 / y)) ≤ h * (1 + Real.log (1 / h)) := by
  have hh := hy.trans_le hyh
  have hs := Real.log_le_sub_one_of_pos (div_pos hh hy)
  rw [Real.log_div hh.ne' hy.ne'] at hs
  have hs' := mul_le_mul_of_nonneg_left hs hy.le
  have hdiv : y*(h/y-1)=h-y := by field_simp [hy.ne']
  rw [hdiv] at hs'
  have hlogh : Real.log h ≤ 0 := Real.log_nonpos hh.le hh1
  simp only [one_div,Real.log_inv]
  nlinarith only [hs',mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hyh) hlogh]

/-- Optimized finite estimate for the sharp complex form factor. Each
analytic input is explicit in the statement. -/
theorem sharpFormFactor_edgeLayer_le {T x D M C : ℝ}
    (hT : 3 ≤ T) (hx : T ≤ x) (hxmax : x ≤ T * Real.log T / 8)
    (hC : 0 ≤ C) (hD : |D - Real.log x| ≤ C)
    (hM : ∀ w ∈ Icc (1 : ℝ) (T / 4),
      |M - T * D| ≤ C * (w * D + x * (1 + Real.log (T / w))))
    (hF : |T * Real.log T * sharpFormFactor T (Real.log x / Real.log T) - M| ≤ C * x) :
    let y := x / (T * Real.log T)
    |sharpFormFactor T (Real.log x / Real.log T) - Real.log x / Real.log T| ≤
      (C * (C + 5)) * (y * (1 + Real.log (1 / y))) ∧
    |sharpFormFactor T (Real.log x / Real.log T) - 1| ≤
      (C * (C + 5) + 1) * (y * (1 + Real.log (1 / y))) := by
  let L := Real.log T
  let y := x / (T * L)
  let w := x / L
  let g := Real.log (1/y)
  let F := sharpFormFactor T (Real.log x/L)
  have hT0 : 0 < T := by linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hTL := mul_pos hT0 hL
  have hx0 : 0 < x := hT0.trans_le hx
  have hL8 : 8 ≤ L := by
    by_contra! hh
    have hz := mul_lt_mul_of_pos_left hh hT0
    change x ≤ T*L/8 at hxmax
    linarith only [hx,hxmax,hz]
  have hLT : L ≤ T := by
    have hh := Real.log_le_sub_one_of_pos hT0
    dsimp [L]
    linarith
  have hxx : x ≤ T*T := by
    change x ≤ T*L/8 at hxmax
    have hh := mul_le_mul_of_nonneg_left hLT hT0.le
    linarith only [hxmax,hh,hTL.le]
  have hlogx : Real.log x ≤ 2*L := by
    have hh := Real.log_le_log hx0 hxx
    rw [Real.log_mul hT0.ne' hT0.ne'] at hh
    dsimp [L]
    linarith
  have hw : 0 ≤ w := div_nonneg hx0.le hL.le
  have hbox : w ∈ Icc (1 : ℝ) (T/4) := by
    constructor
    · apply (le_div_iff₀ hL).mpr
      simpa using hLT.trans hx
    · apply (div_le_iff₀ hL).mpr
      change x ≤ T*L/8 at hxmax
      linarith only [hxmax,hTL.le]
  have hy : 0 < y := div_pos hx0 hTL
  have hy1 : y ≤ 1 := by
    apply (div_le_iff₀ hTL).mpr
    change x ≤ T*L/8 at hxmax
    linarith only [hxmax,hTL.le]
  have hg : 0 ≤ g := Real.log_nonneg ((le_div_iff₀ hy).mpr (by simpa using hy1))
  have htw : T/w = 1/y := by dsimp [w,y]; field_simp [hx0.ne',hL.ne',hT0.ne']
  have hwL : w*L=x := by dsimp [w]; field_simp
  have hxy : T*L*y=x := by dsimp [y]; field_simp
  have hDu : D ≤ (2+C)*L := by
    have hh := (abs_le.mp hD).2
    have hz := mul_nonneg hC (show 0 ≤ L-1 by linarith only [hL8])
    nlinarith only [hh,hlogx,hz]
  have hWD : w*D ≤ (2+C)*x := by
    calc
      _ ≤ w*((2+C)*L) := mul_le_mul_of_nonneg_left hDu hw
      _ = (2+C)*(w*L) := by ring
      _ = _ := by rw [hwL]
  have hM' := hM w hbox
  rw [htw] at hM'
  change |M-T*D| ≤ C*(w*D+x*(1+g)) at hM'
  change |T*L*F-M| ≤ C*x at hF
  have htriangle : |T*L*F-T*Real.log x| ≤ C*x+C*(w*D+x*(1+g))+T*C := by
    rw [show T*L*F-T*Real.log x =
      (T*L*F-M)+(M-T*D)+T*(D-Real.log x) by ring]
    apply (abs_add_le _ _).trans
    apply add_le_add ((abs_add_le _ _).trans (add_le_add hF hM'))
    rw [abs_mul,abs_of_pos hT0]
    exact mul_le_mul_of_nonneg_left hD hT0.le
  have hscaled : |T*L*F-T*Real.log x| ≤ T*L*((C*(C+5))*(y*(1+g))) := by
    apply htriangle.trans
    calc
      _ = C*(x+(w*D+x*(1+g))+T) := by ring
      _ ≤ C*(x+((2+C)*x+x*(1+g))+x) :=
        mul_le_mul_of_nonneg_left (by linarith only [hWD,hx]) hC
      _ ≤ C*(C+5)*(x*(1+g)) := by
        have hz := mul_nonneg (mul_nonneg hC (show 0 ≤ C+4 by linarith only [hC]))
          (mul_nonneg hx0.le hg)
        nlinarith only [hz]
      _ = T*L*((C*(C+5))*(y*(1+g))) := by
        calc
          _ = C*(C+5)*((T*L*y)*(1+g)) := by rw [hxy]
          _ = _ := by ring
  have hf : |F-Real.log x/L| ≤ (C*(C+5))*(y*(1+g)) := by
    have he : T*L*(F-Real.log x/L) = T*L*F-T*Real.log x := by field_simp [hL.ne']
    rw [← he,abs_mul,abs_of_pos hTL] at hscaled
    exact (mul_le_mul_iff_right₀ hTL).mp hscaled
  have hs0 : 0 ≤ Real.log x/L-1 := sub_nonneg.mpr ((le_div_iff₀ hL).mpr
    (by simpa [L] using Real.log_le_log hT0 hx))
  have hs : |Real.log x/L-1| ≤ y := by
    rw [abs_of_nonneg hs0]
    have hh := Real.log_le_sub_one_of_pos (div_pos hx0 hT0)
    rw [Real.log_div hx0.ne' hT0.ne'] at hh
    have he : Real.log x/L-1=(Real.log x-L)/L := by field_simp [hL.ne']
    rw [he]
    change (Real.log x-L)/L ≤ x/(T*L)
    rw [← div_div]
    apply div_le_div_of_nonneg_right _ hL.le
    dsimp only [L] at *
    linarith only [hh]
  change |F-Real.log x/L| ≤ _ ∧ |F-1| ≤ _
  refine ⟨hf,?_⟩
  calc
    |F-1| = |(F-Real.log x/L)+(Real.log x/L-1)| := by congr 1; ring
    _ ≤ |F-Real.log x/L|+|Real.log x/L-1| := abs_add_le _ _
    _ ≤ (C*(C+5))*(y*(1+g))+y := add_le_add hf hs
    _ ≤ (C*(C+5)+1)*(y*(1+g)) := by nlinarith only [mul_nonneg hy.le hg]

/-- A moving upper edge x=o(T log T) is admissible. The common
constant and all three analytic estimates remain visible assumptions. -/
theorem sharpFormFactor_edgeLayer_tendsto {ι : Type*} {l : Filter ι}
    (T x D M : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hy : Tendsto (fun i => x i / (T i * Real.log (T i))) l (𝓝 0))
    (hinputs : ∀ᶠ i in l, 3 ≤ T i ∧ T i ≤ x i ∧ x i ≤ T i * Real.log (T i) / 8 ∧
      |D i - Real.log (x i)| ≤ C ∧
      (∀ w ∈ Icc (1 : ℝ) (T i / 4), |M i - T i * D i| ≤
        C * (w * D i + x i * (1 + Real.log (T i / w)))) ∧
      |T i * Real.log (T i) * sharpFormFactor (T i) (Real.log (x i) / Real.log (T i)) - M i| ≤
        C * x i) :
    Tendsto (fun i => sharpFormFactor (T i) (Real.log (x i) / Real.log (T i))) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz := (edgeSmoothingModulus_tendsto hy).const_mul (C*(C+5)+1)
  rw [mul_zero] at hz
  apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hz
  filter_upwards [hinputs] with i h
  obtain ⟨hT,hx,hxmax,hD,hM,hF⟩ := h
  simpa only [Real.norm_eq_abs] using (sharpFormFactor_edgeLayer_le hT hx hxmax hC hD hM hF).2

/-- Uniform convergence throughout a moving band for the actual prime
mean square and diagonal, using a common bound at every retained frequency. -/
theorem sharpFormFactor_edgeLayer_uniform {ι : Type*} {l : Filter ι}
    (T H : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (hT : Tendsto T l atTop)
    (hy : Tendsto (fun i => H i / Real.log (T i)) l (𝓝 0))
    (hinputs : ∀ᶠ i in l, ∀ x ∈ Icc (T i) (T i * H i),
      |MontgomeryHorizontalBessel.primeDiagonal x - Real.log x| ≤ C ∧
      (∀ w ∈ Icc (1 : ℝ) (T i / 4), |MontgomeryHorizontalBessel.primeSignalEnergy (T i) x -
        T i * MontgomeryHorizontalBessel.primeDiagonal x| ≤
        C * (w * MontgomeryHorizontalBessel.primeDiagonal x + x * (1 + Real.log (T i / w)))) ∧
      |T i * Real.log (T i) * sharpFormFactor (T i) (Real.log x / Real.log (T i)) -
        MontgomeryHorizontalBessel.primeSignalEnergy (T i) x| ≤ C * x) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x ∈ Icc (T i) (T i * H i),
      |sharpFormFactor (T i) (Real.log x / Real.log (T i)) - 1| < ε := by
  intro ε hε
  let B := C*(C+5)+1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hz := (edgeSmoothingModulus_tendsto hy).const_mul B
  rw [mul_zero] at hz
  filter_upwards [hinputs, hT.eventually (eventually_ge_atTop (3:ℝ)),
    hy.eventually_lt_const (show (0:ℝ) < 1/8 by norm_num), hz.eventually_lt_const hε]
    with i hi ht hsmall hlim
  intro x hx
  have ht0 : 0 < T i := by linarith
  have hL : 0 < Real.log (T i) := Real.log_pos (by linarith)
  have hTL := mul_pos ht0 hL
  have hh := (div_lt_iff₀ hL).mp hsmall
  have hmax : x ≤ T i * Real.log (T i) / 8 := by
    have h := mul_lt_mul_of_pos_left hh ht0
    linarith only [hx.2, h]
  have hratio : x / (T i * Real.log (T i)) ≤ H i / Real.log (T i) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right ((div_le_iff₀ ht0).mpr (by simpa [mul_comm] using hx.2)) hL.le
  obtain ⟨hd,hm,hf⟩ := hi x hx
  apply ((sharpFormFactor_edgeLayer_le ht hx.1 hmax hC hd hm hf).2.trans _).trans_lt hlim
  exact mul_le_mul_of_nonneg_left (edgeSmoothingModulus_le
    (div_pos (ht0.trans_le hx.1) hTL) hratio (by linarith only [hsmall])) hB

open MontgomeryHorizontalBessel

/-- Finite edge estimate keeping the diagonal, optimized mean-square and transfer constants separate. -/
theorem sharpFormFactor_edge_of_optimized_errors {T x D M a b c : ℝ}
    (hT : 1 < T) (hx : T ≤ x) (he : x ≤ T * Real.log T)
    (hc : 0 ≤ c)
    (hd : |D - Real.log x| ≤ a)
    (hm : |M - T*D| ≤ b*x*(1 + Real.log ((T*Real.log T)/x)))
    (hf : |T*Real.log T*sharpFormFactor T (Real.log x/Real.log T) - M| ≤ c*x) :
    let y := x/(T*Real.log T)
    |sharpFormFactor T (Real.log x/Real.log T) - 1| ≤
      a/Real.log T + (b+c+1)*(y*(1+Real.log (1/y))) := by
  have ht : 0 < T := lt_trans zero_lt_one hT
  have hl : 0 < Real.log T := Real.log_pos hT
  have htl := mul_pos ht hl
  have hxp : 0 < x := ht.trans_le hx
  let F := sharpFormFactor T (Real.log x/Real.log T)
  let g := Real.log ((T*Real.log T)/x)
  have hg : 0 ≤ g := Real.log_nonneg ((one_le_div hxp).2 he)
  have htr : |T*Real.log T*F-T*Real.log x| ≤ c*x+b*x*(1+g)+T*a := by
    rw [show T*Real.log T*F-T*Real.log x =
        (T*Real.log T*F-M)+(M-T*D)+T*(D-Real.log x) by ring]
    apply (abs_add_le _ _).trans
    apply add_le_add ((abs_add_le _ _).trans (add_le_add hf hm))
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hd ht.le
  have hshift : |T*(Real.log x-Real.log T)| ≤ x := by
    rw [abs_mul, abs_of_pos ht, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log ht hx))]
    have h := Real.log_le_sub_one_of_pos (div_pos hxp ht)
    rw [Real.log_div hxp.ne' ht.ne'] at h
    have k := mul_le_mul_of_nonneg_right h ht.le
    simp only [sub_mul, div_mul_cancel₀ _ ht.ne', one_mul] at k
    linarith
  have htarg : |T*Real.log T*(F-1)| ≤ T*a+(b+c+1)*x*(1+g) := by
    rw [show T*Real.log T*(F-1) =
      (T*Real.log T*F-T*Real.log x)+T*(Real.log x-Real.log T) by ring]
    apply (abs_add_le _ _).trans ((add_le_add htr hshift).trans ?_)
    nlinarith only [mul_nonneg (mul_nonneg hc hxp.le) hg, mul_nonneg hxp.le hg]
  change |F-1| ≤ a/Real.log T + (b+c+1)*(x/(T*Real.log T)*(1+Real.log (1/(x/(T*Real.log T)))))
  rw [show 1/(x/(T*Real.log T)) = T*Real.log T/x by field_simp]
  rw [abs_mul, abs_of_pos htl] at htarg
  apply (mul_le_mul_iff_right₀ htl).mp
  change T*Real.log T*|F-1| ≤ T*Real.log T*(a/Real.log T+(b+c+1)*(x/(T*Real.log T)*(1+g)))
  calc
    _ ≤ T*a+(b+c+1)*x*(1+g) := htarg
    _ = _ := by field_simp [ht.ne', hl.ne']

/-- Uniform moving-edge limit from the three optimized bounds at the retained frequencies. -/
theorem sharpFormFactor_edge_uniform_of_optimized_errors {ι : Type*} {l : Filter ι}
    (T H : ι → ℝ) (a b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hT : Tendsto T l atTop) (hH : Tendsto (fun i => H i / Real.log (T i)) l (𝓝 0))
    (h : ∀ᶠ i in l, ∀ x ∈ Icc (T i) (T i * H i),
      |primeDiagonal x - Real.log x| ≤ a ∧
      |primeSignalEnergy (T i) x - T i*primeDiagonal x| ≤
        b*x*(1+Real.log ((T i*Real.log (T i))/x)) ∧
      |T i*Real.log (T i)*sharpFormFactor (T i) (Real.log x/Real.log (T i)) -
        primeSignalEnergy (T i) x| ≤ c*x) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x ∈ Icc (T i) (T i*H i),
      |sharpFormFactor (T i) (Real.log x/Real.log (T i)) - 1| < ε := by
  intro ε hε
  have hlog := Real.tendsto_log_atTop.comp hT
  have ha : Tendsto (fun i => a/Real.log (T i)) l (𝓝 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul a
  have hz := (edgeSmoothingModulus_tendsto hH).const_mul (b+c+1)
  rw [mul_zero] at hz
  have hj := ha.add hz
  rw [zero_add] at hj
  filter_upwards [h, hT.eventually (eventually_gt_atTop (1:ℝ)),
    hH.eventually_lt_const zero_lt_one, hj.eventually_lt_const hε] with i hi ht hh hj'
  intro x hx
  have ht0 := lt_trans zero_lt_one ht
  have hl := Real.log_pos ht
  have hratio : x/(T i * Real.log (T i)) ≤ H i/Real.log (T i) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right ((div_le_iff₀ ht0).2 (by simpa [mul_comm] using hx.2)) hl.le
  have he := (div_le_one (mul_pos ht0 hl)).1 (hratio.trans hh.le)
  obtain ⟨hd, hm, hf⟩ := hi x hx
  apply ((sharpFormFactor_edge_of_optimized_errors ht hx.1 he hc hd hm hf).trans _).trans_lt hj'
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (edgeSmoothingModulus_le (div_pos (ht0.trans_le hx.1)
    (mul_pos ht0 hl)) hratio hh.le) (by linarith)

/-- After subtracting the pole energy, the sharp limit at a moving frequency
is equivalent to a vanishing signed off-diagonal at the same normalization. -/
theorem sharp_tendsto_one_iff_centered_prime_offDiagonal_tendsto_zero
    {ι : Type*} {l : Filter ι} (T x : ι → ℝ)
    (hT : ∀ᶠ i in l, 1 < T i)
    (hD : Tendsto (fun i =>
      MontgomeryHorizontalBessel.primeDiagonal (x i) / Real.log (T i)) l (𝓝 1))
    (htransfer : Tendsto (fun i =>
      (MontgomeryHorizontalBessel.primeSignalEnergy (T i) (x i) -
        T i * Real.log (T i) * sharpFormFactor (T i) (Real.log (x i) / Real.log (T i)) -
        (4 * Real.pi / 3) * x i) / (T i * Real.log (T i))) l (𝓝 0)) :
    Tendsto (fun i => sharpFormFactor (T i) (Real.log (x i) / Real.log (T i))) l (𝓝 1) ↔
    Tendsto (fun i =>
      (MontgomeryHorizontalBessel.primeSignalEnergy (T i) (x i) -
        T i * MontgomeryHorizontalBessel.primeDiagonal (x i) -
        (4 * Real.pi / 3) * x i) / (T i * Real.log (T i))) l (𝓝 0) := by
  let F := fun i => sharpFormFactor (T i) (Real.log (x i) / Real.log (T i))
  let d := fun i => MontgomeryHorizontalBessel.primeDiagonal (x i) / Real.log (T i)
  let M := fun i => MontgomeryHorizontalBessel.primeSignalEnergy (T i) (x i)
  let R := fun i => (M i - T i * Real.log (T i) * F i - (4 * Real.pi / 3) * x i) /
    (T i * Real.log (T i))
  let Q := fun i => (M i - T i * MontgomeryHorizontalBessel.primeDiagonal (x i) -
    (4 * Real.pi / 3) * x i) / (T i * Real.log (T i))
  change Tendsto F l (𝓝 1) ↔ Tendsto Q l (𝓝 0)
  change Tendsto R l (𝓝 0) at htransfer
  change Tendsto d l (𝓝 1) at hD
  have hident : ∀ᶠ i in l, R i + F i - d i = Q i := by
    filter_upwards [hT] with i hi
    have hT' : T i ≠ 0 := (lt_trans zero_lt_one hi).ne'
    have hlog : Real.log (T i) ≠ 0 := (Real.log_pos hi).ne'
    dsimp only [R, d, Q]
    field_simp [hT', hlog] <;> ring
  constructor
  · intro hF
    have h := (htransfer.add hF).sub hD
    rw [show (0 : ℝ) + 1 - 1 = 0 by norm_num] at h
    exact h.congr' hident
  · intro hQ
    have h := (hQ.sub htransfer).add hD
    rw [show (0 : ℝ) - 0 + 1 = 1 by norm_num] at h
    apply h.congr'
    filter_upwards [hident] with i hi
    change Q i - R i + d i = F i
    linarith only [hi]

end RiemannResearch.Analysis.MontgomeryHorizontalTransfer
