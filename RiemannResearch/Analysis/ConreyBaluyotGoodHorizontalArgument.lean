/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMollifierGoodHeights

/-!
# Uniform horizontal argument on nearby good heights

The good-height and normalized-argument estimates are assembled using one
fixed mollifier. For every positive power length y = T^theta, the horizontal
argument integral is bounded by a constant times log T at arbitrarily close
zero-free heights.

The proof does not identify the limiting boundary argument or establish the
Littlewood contour passage. The mollified moment, Kloosterman estimates, and
away-line density provider remain separate.
-/

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- At arbitrarily close heights, the fixed actual mollifier has a zero-free
horizontal segment with a normalized continuous argument satisfying the
uniform logarithmic integral bound. This does not pass to the limiting
Littlewood contour or prove the mollified moment. -/
theorem exists_uniform_mollifiedZeta_good_horizontal_argument
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y b C H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 2 ≤ b ∧ 0 < C ∧ b + 2 ≤ H ∧
      (∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ s : ℂ, b ≤ s.re →
          1 / 2 ≤ (mollifiedZeta σ y ε s).re) ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ T : ℝ, H ≤ T →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ t : ℝ, |t - T| < δ ∧
              (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
                mollifiedZeta σ y ε ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
              ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc (1 / 2 : ℝ) b) ∧
                φ b = (mollifiedZeta σ y ε ((b : ℂ) + (t : ℂ) * I)).arg ∧
                (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
                  mollifiedZeta σ y ε ((x : ℂ) + (t : ℂ) * I) =
                    (‖mollifiedZeta σ y ε ((x : ℂ) + (t : ℂ) * I)‖ : ℂ) *
                      Complex.exp ((φ x : ℂ) * I)) ∧
                (∀ α ∈ Set.Icc (1 / 2 : ℝ) b,
                  ‖∫ x in α..b, φ x‖ ≤
                    ((Real.log (2 * (1 + C * (t + (b - 1 / 4)) * y)) /
                      Real.log ((b - 1 / 4) / (b - 1 / 2)) + 3) * Real.pi) *
                        |b - α|) := by
  obtain ⟨η1, Y1, b, C, hη1, hη1', hY1, hb, hC, hanchor, harg⟩ :=
    exists_uniform_mollifiedZeta_normalized_horizontal_argument hε
  obtain ⟨η2, Y2, b2, hη2, hη2', hY2, hb2, hgood⟩ :=
    exists_uniform_mollifiedZeta_zero_free_heights hε
  let η := min η1 η2
  let Y := max Y1 Y2
  let L := max b b2
  let H := L + 2
  refine ⟨η, Y, b, C, H, by dsimp [η]; exact lt_min hη1 hη2,
    by dsimp [η]; exact (min_le_left _ _).trans_lt hη1',
    by dsimp [Y]; exact hY1.trans_le (le_max_left _ _),
    hb, hC, by dsimp [H, L]; linarith [le_max_left b b2], ?_, ?_⟩
  · intro y hy σ hσ hση s hs
    exact hanchor y ((le_max_left _ _).trans hy) σ hσ
      (by dsimp [η] at hση; linarith [min_le_left η1 η2]) s hs
  · intro y hy σ hσ hση T hT δ hδ hδ'
    have hy1 : Y1 ≤ y := (le_max_left _ _).trans hy
    have hy2 : Y2 ≤ y := (le_max_right _ _).trans hy
    have hs1 : σ ≤ 1 / 2 + η1 := by
      dsimp [η] at hση
      linarith [min_le_left η1 η2]
    have hs2 : σ ≤ 1 / 2 + η2 := by
      dsimp [η] at hση
      linarith [min_le_right η1 η2]
    have hbL : b ≤ L := le_max_left _ _
    have hb2L : b2 ≤ L := le_max_right _ _
    have hTL : L + 1 ≤ T := by dsimp [H] at hT; linarith
    obtain ⟨t, ht, hfree⟩ := hgood y hy2 σ hσ hs2 L hb2L T hTL δ hδ hδ'
    have htb : b + 1 ≤ t := by
      have hh := (abs_lt.mp ht).1
      dsimp [H] at hT
      linarith
    have hfree' : ∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
        mollifiedZeta σ y ε ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro x hx
      exact hfree x ⟨hx.1, hx.2.trans hbL⟩
    obtain ⟨φ, hφ, hφb, hrep, hdisp, habs, hint⟩ :=
      harg y hy1 σ hσ hs1 t htb hfree'
    exact ⟨t, ht, hfree', φ, hφ, hφb, hrep, hint⟩

/-- On a power-length mollifier scale y = T^theta, the explicit Jensen
logarithm is bounded by a constant times log T uniformly for nearby heights. -/
theorem jensen_count_power_log_bound
    (b C θ T t : ℝ) (hb : 2 ≤ b) (hC : 0 < C) (hθ : 0 ≤ θ)
    (hT : 3 ≤ T) (htpos : 0 < t) (htup : t ≤ 2 * T + 1) :
    let R := b - 1 / 4
    let r := b - 1 / 2
    let K := 2 * (1 + C * (b + 2))
    Real.log (2 * (1 + C * (t + R) * T ^ θ)) / Real.log (R / r) + 3 ≤
      ((Real.log K + 1 + θ) / Real.log (R / r) + 3) * Real.log T := by
  let R := b - 1 / 4
  let r := b - 1 / 2
  let K := 2 * (1 + C * (b + 2))
  let y := T ^ θ
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hy1 : 1 ≤ y := Real.one_le_rpow hT1 hθ
  have hy0 : 0 < y := by linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hR : 0 < R := by dsimp [R]; linarith
  have hratio : 1 < R / r := (one_lt_div hr).mpr (by dsimp [R, r]; linarith)
  have hd : 0 < Real.log (R / r) := Real.log_pos hratio
  have hK1 : 1 ≤ K := by dsimp [K]; nlinarith [mul_nonneg hC.le (show 0 ≤ b + 2 by linarith)]
  have hK : 0 < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have hh := Real.exp_one_lt_d9
    linarith
  have hTy : 1 ≤ T * y := one_le_mul_of_one_le_of_one_le hT1 hy1
  have hlarge : t + R ≤ (b + 2) * T := by
    dsimp [R]
    have hh := mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ T - 2 by linarith)
    nlinarith
  have hprod : C * (t + R) * y ≤ C * ((b + 2) * T) * y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlarge hC.le) hy0.le
  have hN : 2 * (1 + C * (t + R) * y) ≤ K * T * y := by
    dsimp [K]
    nlinarith [hprod, hTy]
  have hN0 : 0 < 2 * (1 + C * (t + R) * y) := by positivity
  have hlog := Real.log_le_log hN0 hN
  have hlogprod : Real.log (K * T * y) = Real.log K + Real.log T + Real.log y := by
    rw [Real.log_mul (by positivity : K * T ≠ 0) (ne_of_gt hy0),
      Real.log_mul (ne_of_gt hK) (ne_of_gt hT0)]
  have hylog : Real.log y = θ * Real.log T := by
    dsimp [y]
    exact Real.log_rpow hT0 θ
  rw [hlogprod, hylog] at hlog
  have hnum : Real.log (2 * (1 + C * (t + R) * y)) ≤
      (Real.log K + 1 + θ) * Real.log T := by
    have hh := mul_nonneg hlogK (sub_nonneg.mpr hlogT)
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hnum hd.le
  change Real.log (2 * (1 + C * (t + R) * y)) / Real.log (R / r) + 3 ≤
    ((Real.log K + 1 + θ) / Real.log (R / r) + 3) * Real.log T
  calc
    _ ≤ ((Real.log K + 1 + θ) * Real.log T) / Real.log (R / r) + 3 := by linarith
    _ = ((Real.log K + 1 + θ) / Real.log (R / r)) * Real.log T + 3 := by ring
    _ ≤ _ := by nlinarith

/-- For every positive power length, arbitrarily close zero-free heights
support a normalized horizontal argument whose integrals are uniformly
O(log T). The mollifier length is T^theta and remains fixed as the height
moves. No Littlewood boundary-limit passage is asserted. -/
theorem exists_uniform_mollifiedZeta_power_good_horizontal_argument
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b D H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ 0 < D ∧ b + 2 ≤ H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ t : ℝ, |t - T| < δ ∧
              (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
                mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
              ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc (1 / 2 : ℝ) b) ∧
                φ b = (mollifiedZeta σ (T ^ θ) ε ((b : ℂ) + (t : ℂ) * I)).arg ∧
                (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
                  mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t : ℂ) * I) =
                    (‖mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t : ℂ) * I)‖ : ℂ) *
                      Complex.exp ((φ x : ℂ) * I)) ∧
                (∀ α ∈ Set.Icc (1 / 2 : ℝ) b,
                  ‖∫ x in α..b, φ x‖ ≤ D * Real.log T) := by
  obtain ⟨η, Y, b, C, H, hη, hη', hY, hb, hC, hH, _, hgood⟩ :=
    exists_uniform_mollifiedZeta_good_horizontal_argument hε
  let d := Real.log ((b - 1 / 4) / (b - 1 / 2))
  let K := 2 * (1 + C * (b + 2))
  let Q := (Real.log K + 1 + θ) / d + 3
  let D := Q * Real.pi * (b - 1 / 2)
  let H' := max H (Y ^ θ⁻¹)
  have hr : 0 < b - 1 / 2 := by linarith
  have hratio : 1 < (b - 1 / 4) / (b - 1 / 2) :=
    (one_lt_div hr).mpr (by linarith)
  have hd : 0 < d := Real.log_pos hratio
  have hK1 : 1 ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg hC.le (show 0 ≤ b + 2 by linarith)]
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨η, b, D, H', hη, hη', hb, hD,
    by dsimp [H']; exact hH.trans (le_max_left _ _), ?_⟩
  intro T hT σ hσ hση δ hδ hδ'
  have hTH : H ≤ T := (le_max_left _ _).trans hT
  have hTY : Y ^ θ⁻¹ ≤ T := (le_max_right _ _).trans hT
  have hT3 : 3 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hYpow : Y ≤ T ^ θ := by
    calc
      Y = (Y ^ θ⁻¹) ^ θ :=
        (Real.rpow_inv_rpow (by linarith : 0 ≤ Y) (ne_of_gt hθ)).symm
      _ ≤ T ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hTY hθ.le
  obtain ⟨t, ht, hfree, φ, hφ, hφb, hrep, hint⟩ :=
    hgood (T ^ θ) hYpow σ hσ hση T hTH δ hδ hδ'
  have ht14 : |t - T| ≤ 1 / 4 := ht.le.trans hδ'
  have hJ :
      Real.log (2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ)) / d + 3 ≤
        Q * Real.log T := by
    simpa only [d, Q, K] using
      jensen_count_power_log_bound b C θ T t hb hC hθ.le hT3
        (by have hh := (abs_le.mp ht14).1; linarith)
        (by have hh := (abs_le.mp ht14).2; linarith)
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ Q * Real.log T * Real.pi := by positivity
  refine ⟨t, ht, hfree, φ, hφ, hφb, hrep, ?_⟩
  intro α hα
  have hlen : |b - α| ≤ b - 1 / 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hα.2)]
    linarith [hα.1]
  calc
    ‖∫ x in α..b, φ x‖ ≤
        ((Real.log (2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ)) / d + 3) *
          Real.pi) * |b - α| := hint α hα
    _ ≤ (Q * Real.log T * Real.pi) * |b - α| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hJ Real.pi_pos.le) (abs_nonneg _)
    _ ≤ (Q * Real.log T * Real.pi) * (b - 1 / 2) :=
      mul_le_mul_of_nonneg_left hlen hcoef
    _ = D * Real.log T := by dsimp [D]; ring

end RiemannResearch.Analysis.ConreyBaluyot
