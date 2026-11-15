/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMollifierGrowth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
/-!
# Arbitrarily small outward second-moment endpoint error

Source: endpoint-strip obligation in the user-provided Conrey--Baluyot
right-boundary continuation. The proof uses the established actual product
growth bound and finite interval additivity. Both strips occur in the
primary exact identity. A central moment estimate remains an explicit premise.

The width is selected after T, y and a positive tolerance, but before sigma,
the evaluation line, the endpoints or the central moment error.
-/
noncomputable section
open Complex MeasureTheory Set
namespace RiemannResearch.Analysis.ConreyBaluyot

def mollifiedSecondMoment (σ y ε l u v : ℝ) : ℝ :=
  ∫ t in u..v, ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I)‖ ^ 2

theorem continuousOn_mollifiedZeta_vertical (σ y ε l : ℝ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    ContinuousOn (fun t : ℝ => mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I))
      (uIcc u v) := by
  rw [uIcc_of_le huv]
  intro t ht
  have hs : (l : ℂ) + (t : ℂ)*I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    linarith [ht.1]
  exact (ContinuousAt.comp (g := mollifiedZeta σ y ε)
    (f := fun t : ℝ => (l : ℂ) + (t : ℂ)*I)
    (analyticAt_mollifiedZeta σ y ε hs).continuousAt
    (show ContinuousAt (fun t : ℝ => (l : ℂ) + (t : ℂ)*I) t by fun_prop)).continuousWithinAt

theorem mollifiedSecondMoment_add (σ y ε l : ℝ) {u v w : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hvw : v ≤ w) :
    mollifiedSecondMoment σ y ε l u w =
      mollifiedSecondMoment σ y ε l u v + mollifiedSecondMoment σ y ε l v w := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((continuousOn_mollifiedZeta_vertical σ y ε l hu huv).norm.pow 2).intervalIntegrable
    ((continuousOn_mollifiedZeta_vertical σ y ε l
      (hu.trans_le huv) hvw).norm.pow 2).intervalIntegrable).symm

/-- The two outward strips are retained in an exact identity. -/
theorem mollifiedSecondMoment_outward_identity (σ y ε l : ℝ) {T u v : ℝ}
    (hu : 0 < u) (huT : u ≤ T) (hTv : 2 * T ≤ v) :
    mollifiedSecondMoment σ y ε l u v =
      mollifiedSecondMoment σ y ε l u T +
      mollifiedSecondMoment σ y ε l T (2 * T) +
      mollifiedSecondMoment σ y ε l (2 * T) v := by
  have hT : 0 < T := hu.trans_le huT
  rw [mollifiedSecondMoment_add σ y ε l hu (huT.trans (by linarith)) hTv,
    mollifiedSecondMoment_add σ y ε l hu huT (by linarith)]

theorem mollifiedSecondMoment_le_length_mul {σ y ε l u v B : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Icc u v, ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I)‖ ≤ B) :
    mollifiedSecondMoment σ y ε l u v ≤ (v-u)*B^2 := by
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I)‖ ^ 2) huv
    ((continuousOn_mollifiedZeta_vertical σ y ε l hu huv).norm.pow 2).intervalIntegrable
    (intervalIntegrable_const (c := B^2)) (fun t ht => ?_)
  · simpa only [mollifiedSecondMoment, intervalIntegral.integral_const, smul_eq_mul] using h
  · have htB := hb t ht
    nlinarith [norm_nonneg (mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I))]

/-- Uniform endpoint transfer: after fixing T, y and an error tolerance, the
same positive width works for all admissible sigma, evaluation lines and
outward endpoints. The central moment remains a premise. -/
theorem exists_uniform_mollifiedSecondMoment_endpoint_transfer {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y : ℝ, 0 < η ∧ η < 1/4 ∧ 1 < Y ∧
      ∀ T y κ : ℝ, 2 ≤ T → Y ≤ y → 0 < κ →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧
          ∀ σ l u v E : ℝ,
            1/2 + 1 / Real.log y ≤ σ → σ ≤ 1/2 + η → 1/4 ≤ l →
            T-δ ≤ u → u ≤ T → 2 * T ≤ v → v ≤ 2 * T+δ →
            mollifiedSecondMoment σ y ε l T (2 * T) ≤ T+E →
            mollifiedSecondMoment σ y ε l u v ≤ v-u+E+κ := by
  obtain ⟨η, Y, C, hη, hη', hY, hC, hgrowth⟩ := exists_uniform_mollifiedZeta_growth hε
  refine ⟨η, Y, hη, hη', hY, ?_⟩
  intro T y κ hT hy hκ
  let B := C * (2 * T+1) * y^(1+ε)
  have hB : 0 ≤ B := by
    dsimp [B]
    have hy0 : 0 < y := (by linarith : 0 < Y).trans_le hy
    positivity
  let δ := min (1/4 : ℝ) (κ / (2*(B^2+1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hκ (by positivity))
  have hδ' : δ ≤ 1/4 := min_le_left _ _
  have hδcost : 2*δ*B^2 ≤ κ := by
    have hd : δ ≤ κ / (2*(B^2+1)) := min_le_right _ _
    have hc := (le_div_iff₀ (by positivity : 0 < 2*(B^2+1))).mp hd
    nlinarith
  refine ⟨δ, hδ, hδ', ?_⟩
  intro σ l u v E hσ hση hl hu huT hv hv' hm
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have htwo : T ≤ 2 * T := by linarith
  have hbound : ∀ t ∈ Icc u v,
      ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I)‖ ≤ B := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have ht1 : 1 ≤ |(((l : ℂ) + (t : ℂ)*I)).im| := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
      rw [abs_of_nonneg ht0]
      linarith [ht.1]
    have hg := hgrowth y hy σ hσ hση ((l : ℂ) + (t : ℂ)*I)
      (by simpa using hl) ht1
    have him : |(((l : ℂ) + (t : ℂ)*I)).im| = t := by simp [abs_of_nonneg ht0]
    rw [him] at hg
    apply hg.trans
    dsimp [B]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith [ht.2] : t ≤ 2 * T+1) hC.le)
      (Real.rpow_nonneg (by linarith : 0 ≤ y) _)
  have hleft := mollifiedSecondMoment_le_length_mul hu0 huT hB
    (fun t ht => hbound t ⟨ht.1, ht.2.trans (htwo.trans hv)⟩)
  have hright := mollifiedSecondMoment_le_length_mul
    (by linarith : 0 < 2 * T) hv hB
    (fun t ht => hbound t ⟨(huT.trans htwo).trans ht.1, ht.2⟩)
  rw [mollifiedSecondMoment_outward_identity σ y ε l hu0 huT hv]
  have hlen : T ≤ v-u := by linarith
  have hstrips : (T-u)*B^2+(v-2 * T)*B^2 ≤ 2*δ*B^2 := by
    nlinarith [sq_nonneg B]
  linarith
end RiemannResearch.Analysis.ConreyBaluyot
