/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergTruncatedNearLine
import RiemannResearch.Analysis.ActualInghamDensityBound
import RiemannResearch.Analysis.ConreyBaluyotMomentExcess
import RiemannResearch.Analysis.ConreyBaluyotGaussianMoment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform Conrey–Baluyot density from the actual Gaussian moment

The Gaussian window error, weighted-excess bound and dyadic summation
preserve the exponent 2*theta. A cofinal family of mollifier lengths
below 4/7 suffices. The actual Ingham density theorem supplies the
away-line input. The uniform near-line moment is the remaining premise.

Source for the proof strategy: S. A. C. Baluyot, *On the Zeros of
Riemann's Zeta-function* (2017), Chapter 3,
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .
See Section 3.6 for the moment and counting assembly.
-/

noncomputable section
open Set

namespace RiemannResearch.Analysis.ConreyBaluyot

open ActualZeroOrdinate

/-- Baluyot's uniform upper second moment on his coupled evaluation line,
with the actual mollifier length and the exact finite cutoff. -/
def UniformDyadicMollifiedMoment (θ ε : ℝ) : Prop :=
  ∃ η C H : ℝ, 0 < η ∧ 0 ≤ C ∧ 1 < H ∧
    ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
      1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
      mollifiedSecondMoment σ (T ^ θ) ε σ T (2 * T) ≤
        T + C * T ^ (1 - (2 * θ) * (σ - 1 / 2))

/-- The actual upper dyadic moment and Ingham's estimate suffice for the
uniform inclusive count at the full exponent 2*theta. -/
theorem uniformSelbergDensity_of_dyadicMollifiedMoment_and_ingham
    {θ ε : ℝ} (hθ : 0 < θ) (hθhi : θ ≤ 2 / 3) (hε : 0 ≤ ε)
    (hm : UniformDyadicMollifiedMoment θ ε) (hI : InghamDensityBound) :
    UniformSelbergDensity (2 * θ) := by
  obtain ⟨η₀, B, H₀, hη₀, hη₀', hB, hH₀, hW⟩ :=
    exists_uniform_dyadic_logExcess_of_prescribed_line_moment hε hθ
  obtain ⟨η₁, C, H₁, hη₁, hC, hH₁, hm⟩ := hm
  let η := min η₀ η₁
  have hη : 0 < η := lt_min hη₀ hη₁
  have hη' : η < 1 / 4 := (min_le_left _ _).trans_lt hη₀'
  have hp : 0 < 1 - (2 * θ) * η := by
    have hprod := mul_le_mul_of_nonneg_left hη'.le
      (show 0 ≤ 2 * θ by positivity)
    linarith
  apply uniformSelbergDensity_of_truncated_near_excess_and_ingham
    (A := 2 / θ) (by positivity : 0 < 2 * θ) (by linarith) hη hp hI
  refine ⟨C / (4 * Real.pi), B, 2 * max H₀ H₁, by positivity, hB,
    by linarith [le_max_left H₀ H₁], ?_⟩
  intro T hT σ hσ
  let S := T / 2
  have hS₀ : H₀ ≤ S := by dsimp [S]; linarith [le_max_left H₀ H₁]
  have hS₁ : H₁ ≤ S := by dsimp [S]; linarith [le_max_right H₀ H₁]
  have hS2 : 2 ≤ S := hH₀.trans hS₀
  have hSpos : 0 < S := by linarith
  have hST : S ≤ T := by dsimp [S] at hS2 ⊢; linarith
  have h2S : 2 * S = T := by dsimp [S]; ring
  have hTpos : 0 < T := hSpos.trans_le hST
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hleft : 1 / Real.log (S ^ θ) ≤ (2 / θ) / Real.log T := by
    have hlogs : Real.log T ≤ 2 * Real.log S := by
      rw [← h2S, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hSpos.ne']
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hS2]
    rw [Real.log_rpow hSpos]
    apply (div_le_div_iff₀ (mul_pos hθ hlogS) hlogT).2
    calc
      _ = Real.log T := one_mul _
      _ ≤ 2 * Real.log S := hlogs
      _ = (2 / θ) * (θ * Real.log S) := by field_simp [hθ.ne']
  have hσlo : 1 / 2 + 1 / Real.log (S ^ θ) ≤ σ := by linarith [hσ.1]
  have hσ₀ : σ ≤ 1 / 2 + η₀ := by linarith [hσ.2, min_le_left η₀ η₁]
  have hσ₁ : σ ≤ 1 / 2 + η₁ := by linarith [hσ.2, min_le_right η₀ η₁]
  let p := 1 - (2 * θ) * (σ - 1 / 2)
  have hp₀ : 0 ≤ p := by
    dsimp [p]
    linarith [mul_le_mul_of_nonneg_left (show σ - 1 / 2 ≤ η by linarith [hσ.2])
      (show 0 ≤ 2 * θ by positivity)]
  have hmoment := hm S hS₁ σ hσlo hσ₁
  have hweighted := hW S σ hS₀ hσlo hσ₀ (C * S ^ p) hmoment
  rw [h2S] at hweighted
  have hpower : T ^ p = T * Real.exp (-((2 * θ) * Real.log T) * (σ - 1 / 2)) := by
    dsimp [p]
    rw [show 1 - (2 * θ) * (σ - 1 / 2) = 1 + (-(2 * θ) * (σ - 1 / 2)) by ring,
      Real.rpow_add hTpos, Real.rpow_one, Real.rpow_def_of_pos hTpos]
    congr 2
    ring
  calc
    _ ≤ (C * S ^ p) / (4 * Real.pi) + B * Real.log S := hweighted
    _ ≤ (C * T ^ p) / (4 * Real.pi) + B * Real.log T :=
      add_le_add (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSpos.le hST hp₀) hC) (by positivity))
        (mul_le_mul_of_nonneg_left (Real.log_le_log hSpos hST) hB)
    _ = _ := by rw [hpower]; ring

/-- A cofinal family of estimates for actual mollifier lengths below 4/7
suffices for every density exponent strictly below 8/7. -/
theorem conreyBaluyotDensity_of_cofinal_dyadicMollifiedMoments
    (hm : ∀ a : ℝ, 0 < a → a < 8 / 7 →
      ∃ θ ε : ℝ, a ≤ 2 * θ ∧ θ < 4 / 7 ∧ 0 ≤ ε ∧ UniformDyadicMollifiedMoment θ ε) :
    ConreyBaluyotDensityHypothesis := by
  intro a ha ha'
  obtain ⟨θ, ε, hθa, hθhi, hε, hp⟩ := hm a ha ha'
  have hstrong := uniformSelbergDensity_of_dyadicMollifiedMoment_and_ingham
    (show 0 < θ by linarith) (show θ ≤ 2 / 3 by linarith) hε hp inghamDensityBound
  obtain ⟨C, H, hC, hH, hd⟩ := hstrong
  refine ⟨C, H, hC, hH, ?_⟩
  intro T hT σ hσ
  have hT1 : 1 ≤ T := hH.le.trans hT
  have hle : 1 - (2 * θ) * (σ - 1 / 2) ≤ 1 - a * (σ - 1 / 2) := by
    linarith [mul_le_mul_of_nonneg_right hθa (sub_nonneg.mpr hσ.1)]
  exact (hd T hT σ hσ).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hle) hC)
    (Real.log_nonneg hT1))

/-- The actual normalized Gaussian estimate on the padded source interval. -/
def UniformGaussianMollifiedMoment (θ ε δ : ℝ) : Prop :=
  ∃ η C H : ℝ, 0 < η ∧ 0 ≤ C ∧ 1 < H ∧
    ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
      1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
      ∀ u ∈ Icc (T - T ^ (1 - δ) * Real.log T) (2 * T + T ^ (1 - δ) * Real.log T),
        mollifiedGaussianMoment σ (T ^ θ) ε σ (T ^ (1 - δ)) u ≤
          1 + C * T ^ (-(2 * θ) * (σ - 1 / 2))

private theorem log_le_rpow_div {T q : ℝ} (hT : 0 < T) (hq : 0 < q) :
    Real.log T ≤ T ^ q / q := by
  apply (le_div_iff₀ hq).2
  rw [Real.rpow_def_of_pos hT]
  linarith only [Real.add_one_le_exp (Real.log T * q)]

/-- The explicit Gaussian window loss has the same power as the central
moment. All constants precede the height, line and Gaussian center. -/
theorem uniformDyadicMollifiedMoment_of_gaussian
    {θ ε δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hδhi : δ ≤ 1)
    (hm : UniformGaussianMollifiedMoment θ ε δ) :
    UniformDyadicMollifiedMoment θ ε := by
  obtain ⟨η, C, H, hη, hC, hH, hm⟩ := hm
  let η' := min η (min (1 / 4) (δ / (4 * θ)))
  let K := 2 * (2 * (1 + C) / (δ / 2) + C + 2)
  refine ⟨η', K, max H (Real.exp 4),
    lt_min hη (lt_min (by norm_num) (by positivity)), by dsimp [K]; positivity,
    hH.trans_le (le_max_left _ _), ?_⟩
  intro T hT σ hσ hση
  have hTH : H ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 < T := hH.trans_le hTH
  have hT0 : 0 < T := by linarith
  have hlog : 4 ≤ Real.log T := by
    rw [← Real.log_exp 4]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hT)
  have hT2 : 2 ≤ T := by linarith [Real.log_le_sub_one_of_pos hT0]
  have hσlo : 1 / 2 ≤ σ := by
    have hlt : 0 < Real.log (T ^ θ) := Real.log_pos (Real.one_lt_rpow hT1 hθ)
    linarith [one_div_pos.mpr hlt]
  have hσhi : σ ≤ 1 / 2 + η := by linarith [min_le_left η (min (1/4) (δ / (4*θ)))]
  have hσ1 : σ < 1 := by
    have hη'' : η' ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hηgap : η' ≤ δ / (4 * θ) := (min_le_right _ _).trans (min_le_right _ _)
  let w := (2 * θ) * (σ - 1 / 2)
  have hw0 : 0 ≤ w := mul_nonneg (by positivity) (sub_nonneg.mpr hσlo)
  have hwδ : w ≤ δ / 2 := by
    have hh : σ - 1 / 2 ≤ δ / (4 * θ) := by linarith
    have hprod := (le_div_iff₀ (show 0 < 4 * θ by positivity)).mp hh
    dsimp [w]
    linarith
  let Δ := T ^ (1 - δ)
  let pad := Δ * Real.log T
  let L := Real.sqrt 2 * Real.exp (-(Real.log T) ^ 2 / 2)
  let r := C * T ^ (-w)
  let P := T ^ (1 - w)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT0 _
  have hpad0 : 0 ≤ pad := mul_nonneg hΔ.le (by linarith)
  have hP : 0 ≤ P := Real.rpow_nonneg hT0.le _
  have hr0 : 0 ≤ r := mul_nonneg hC (Real.rpow_nonneg hT0.le _)
  have hrC : r ≤ C := by
    dsimp [r]
    apply mul_le_of_le_one_right hC
    simpa using (Real.rpow_le_rpow_of_exponent_le hT1.le
      (neg_nonpos.mpr hw0) : T ^ (-w) ≤ T ^ (0:ℝ))
  have hrT : T * r = C * P := by
    dsimp [r, P]
    rw [show (1 : ℝ) - w = 1 + (-w) by ring, Real.rpow_add hT0, Real.rpow_one]
    ring
  have hpad : pad ≤ P / (δ / 2) := by
    calc
      _ ≤ Δ * (T ^ (δ / 2) / (δ / 2)) :=
        mul_le_mul_of_nonneg_left (log_le_rpow_div hT0 (by positivity)) hΔ.le
      _ = T ^ (1 - δ / 2) / (δ / 2) := by
        dsimp [Δ]
        rw [← mul_div_assoc, ← Real.rpow_add hT0]
        congr 2
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith)) (by positivity)
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hLs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hLpow : L ≤ 2 * T ^ (-2 : ℝ) :=
    mul_le_mul hLs (Real.exp_neg_log_sq_le_rpow hT0 (by norm_num) (by linarith))
      (Real.exp_nonneg _) (by norm_num)
  have hLhalf : L ≤ 1 / 2 := by
    calc
      _ ≤ 2 * T ^ (-2 : ℝ) := hLpow
      _ ≤ 2 * (2 : ℝ) ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by norm_num) hT2 (by norm_num)) (by norm_num)
      _ = 1 / 2 := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num [Real.rpow_two]
  have hLT : L * T ≤ 2 * P := by
    calc
      _ ≤ (2 * T ^ (-2 : ℝ)) * T := mul_le_mul_of_nonneg_right hLpow hT0.le
      _ = 2 * T ^ (1 + (-2) : ℝ) := by
        rw [Real.rpow_add hT0, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1.le
        (by linarith)) (by norm_num)
  have hExcess : gaussianMomentExcess T pad r L ≤ K * P := by
    unfold gaussianMomentExcess
    apply (div_le_iff₀ (show 0 < 1 - L by linarith)).2
    have hsum : 2 * pad + (T + 2 * pad) * r + L * T ≤ (K * P) / 2 := by
      have hpads := mul_le_mul_of_nonneg_left hpad
        (show 0 ≤ 2 * (1 + C) by positivity)
      have hprod := mul_le_mul_of_nonneg_left hrC (show 0 ≤ 2 * pad by positivity)
      calc
        _ ≤ 2 * (1 + C) * pad + C * P + 2 * P := by
          nlinarith only [hrT, hLT, hprod]
        _ ≤ 2 * (1 + C) * (P / (δ / 2)) + C * P + 2 * P :=
          add_le_add (add_le_add hpads (le_refl _)) (le_refl _)
        _ = _ := by dsimp [K]; ring
    exact hsum.trans (by
      linarith only [mul_le_mul_of_nonneg_left (show 1/2 ≤ 1-L by linarith)
        (show 0 ≤ K * P by dsimp [K]; positivity)])
  have hcentral := mollifiedSecondMoment_le_of_log_padded_gaussianMoment σ (T ^ θ) ε
    (l := σ) (Δ := Δ) (r := r) (by linarith) hσ1.ne hT0 hΔ (by linarith)
    (by simpa only [r, w, Δ, neg_mul] using hm T hTH σ hσ hσhi)
  exact hcentral.trans (add_le_add (le_refl T) hExcess)


/-- A cofinal family of actual smoothed moment estimates gives every published
density exponent strictly below 8/7. -/
theorem conreyBaluyotDensity_of_cofinal_gaussianMollifiedMoments
    (hm : ∀ a : ℝ, 0 < a → a < 8 / 7 →
      ∃ θ ε δ : ℝ, a ≤ 2 * θ ∧ θ < 4 / 7 ∧ 0 ≤ ε ∧ 0 < δ ∧ δ ≤ 1 ∧
        UniformGaussianMollifiedMoment θ ε δ) :
    ActualZeroOrdinate.ConreyBaluyotDensityHypothesis := by
  apply conreyBaluyotDensity_of_cofinal_dyadicMollifiedMoments
  intro a ha ha'
  obtain ⟨θ, ε, δ, hθa, hθhi, hε, hδ, hδ', hmoment⟩ := hm a ha ha'
  exact ⟨θ, ε, hθa, hθhi, hε,
    uniformDyadicMollifiedMoment_of_gaussian (by linarith) hδ hδ' hmoment⟩

end RiemannResearch.Analysis.ConreyBaluyot

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Absorb every finite initial height into one constant. The same bound
then holds for every T >= 2 and every sigma >= 1/2, including sigma >= 1. -/
theorem UniformSelbergDensity.all_heights_ge_two {a : ℝ} (h : UniformSelbergDensity a)
    (ha : 0 ≤ a) (ha' : a ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ≥ 2, ∀ σ ≥ 1 / 2,
      rightInclusiveCount T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  obtain ⟨C₀, H, hC₀, hH, hd⟩ := h
  let A := (Zeta23.Ncount 0 H : ℝ) / Real.log 2
  let C := max C₀ A
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := hC₀.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  by_cases hσ1 : σ ≤ 1
  · by_cases hTH : H ≤ T
    · exact (hd T hTH σ ⟨hσ, hσ1⟩).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_max_left _ _) (Real.rpow_nonneg hTpos.le _)) hlogT)
    · have hp : 0 ≤ 1 - a * (σ - 1 / 2) := by
        linarith [mul_le_mul_of_nonneg_left
          (show σ - 1 / 2 ≤ 1 / 2 by linarith) ha]
      calc
        _ ≤ rightInclusiveCount H σ := rightInclusiveCount_monotone_height σ (le_of_not_ge hTH)
        _ ≤ (Zeta23.Ncount 0 H : ℝ) := rightInclusiveCount_le_count _ _
        _ = A * Real.log 2 := (div_mul_cancel₀ _ hlog₂.ne').symm
        _ ≤ C * Real.log T := mul_le_mul (le_max_right _ _)
          (Real.log_le_log (by norm_num) hT) hlog₂.le hC
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right hC (Real.one_le_rpow hT1 hp)) hlogT
  · have hz : rightInclusiveCount T σ = 0 := by
      unfold rightInclusiveCount realSum
      apply Finset.sum_eq_zero
      intro ρ hρ
      have hρ' := (mem_cutoff.mp hρ).1.2.2
      have hnot : ¬ σ ≤ ρ.re := by linarith [lt_of_not_ge hσ1]
      simp [hnot]
    rw [hz]
    positivity


end RiemannResearch.Analysis.ActualZeroOrdinate
