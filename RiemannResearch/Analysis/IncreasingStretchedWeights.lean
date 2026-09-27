/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.IncreasingAbelConvergence
import RiemannResearch.Analysis.StretchedExponentialBounds

/-!
# Full-profile increasing Abel estimates and moving bands

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis

private theorem exp_sub_le_gap_mul_exp (a b : ℝ) :
    Real.exp b - Real.exp a ≤ (b - a) * Real.exp b := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a - b))
    (Real.exp_pos b).le
  have he : Real.exp b * Real.exp (a - b) = Real.exp a := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  nlinarith only [h]

private theorem shifted_reciprocal_step (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) / (6 + b) ^ 2 ≤ (6 + a)⁻¹ - (6 + b)⁻¹ := by
  have hA : 0 < 6 + a := by linarith
  have hB : 0 < 6 + b := by linarith
  have he : (6 + a)⁻¹ - (6 + b)⁻¹ =
      (b - a) / ((6 + a) * (6 + b)) := by
    field_simp [hA.ne', hB.ne']
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos hB) (mul_pos hA hB)).mpr
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
  nlinarith

/-- Increasing exponential weights cost at most delta*B/6 when their
weighted residual profile has an inverse-square bound in logarithmic
coordinates. The exact reciprocal telescope avoids an integral. -/
theorem increasing_exp_grid_profile_sum_le
    (s R : ℕ → ℝ) (hs : Monotone s) (hs0 : s 0 = 0)
    (hR : ∀ n, 0 ≤ R n) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (N : ℕ)
    (hprofile : ∀ n, n ≤ N →
      Real.exp (δ * s n) * R n ≤ B / (6 + s n) ^ 2) :
    (∑ n ∈ Finset.range N,
      (Real.exp (δ * s (n + 1)) - Real.exp (δ * s n)) * R (n + 1)) ≤
      δ * B / 6 := by
  have hsn (n : ℕ) : 0 ≤ s n := by simpa only [hs0] using hs (Nat.zero_le n)
  have hstep (n : ℕ) (hn : n < N) :
      (Real.exp (δ * s (n + 1)) - Real.exp (δ * s n)) * R (n + 1) ≤
        δ * B * ((6 + s n)⁻¹ - (6 + s (n + 1))⁻¹) := by
    have hdiff : 0 ≤ s (n + 1) - s n := sub_nonneg.mpr (hs (Nat.le_succ n))
    calc
      _ ≤ ((δ * s (n + 1) - δ * s n) * Real.exp (δ * s (n + 1))) * R (n + 1) :=
        mul_le_mul_of_nonneg_right (exp_sub_le_gap_mul_exp _ _) (hR _)
      _ = (δ * (s (n + 1) - s n)) *
          (Real.exp (δ * s (n + 1)) * R (n + 1)) := by ring
      _ ≤ (δ * (s (n + 1) - s n)) * (B / (6 + s (n + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_left (hprofile (n + 1) (Nat.succ_le_of_lt hn))
          (mul_nonneg hδ hdiff)
      _ = δ * B * ((s (n + 1) - s n) / (6 + s (n + 1)) ^ 2) := by ring
      _ ≤ δ * B * ((6 + s n)⁻¹ - (6 + s (n + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left
          (shifted_reciprocal_step _ _ (hsn n) (hs (Nat.le_succ n)))
          (mul_nonneg hδ hB)
  have htel : (∑ n ∈ Finset.range N,
      ((6 + s n)⁻¹ - (6 + s (n + 1))⁻¹)) =
        (6 + s 0)⁻¹ - (6 + s N)⁻¹ := by
    have h := Finset.sum_range_sub (fun n => -(6 + s n)⁻¹) N
    convert h using 1
    · apply Finset.sum_congr rfl
      intro n hn
      ring
    · ring
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        δ * B * ((6 + s n)⁻¹ - (6 + s (n + 1))⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hstep n (Finset.mem_range.mp hn)
    _ = δ * B * ((6 + s 0)⁻¹ - (6 + s N)⁻¹) := by
      rw [← Finset.mul_sum, htel]
    _ ≤ δ * B / 6 := by
      rw [hs0]
      have hp : 0 ≤ δ * B * (6 + s N)⁻¹ :=
        mul_nonneg (mul_nonneg hδ hB) (inv_nonneg.mpr (by linarith [hsn N]))
      norm_num
      nlinarith only [hp]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Centered Abel transfer retaining a summable profile in logarithmic
coordinates. This is about complete signed prefix errors. -/
theorem signedVector_increasing_exp_grid_bound
    (u : ℕ → E) (f : E) (s R : ℕ → ℝ)
    (hs : Monotone s) (hs0 : s 0 = 0) (hR : ∀ n, 0 ≤ R n)
    (herror : ∀ n, ‖signedVectorPrefix u (n + 1) - f‖ ≤ R (n + 1))
    (δ B A : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (N : ℕ)
    (hprofile : ∀ n, n ≤ N →
      Real.exp (δ * s n) * R n ≤ B / (6 + s n) ^ 2)
    (hterminal : Real.exp (δ * s N) * R (N + 1) ≤ A) :
    ‖(∑ n ∈ Finset.range (N + 1), Real.exp (δ * s n) • u n) - f‖ ≤
      A + δ * B / 6 := by
  have hw : Monotone (fun n => Real.exp (δ * s n)) := by
    intro i j hij
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hs hij) hδ)
  have h := signedVector_increasing_weight_residual_le u
    (fun n => Real.exp (δ * s n)) f R hw (fun n => (Real.exp_pos _).le) herror N
  have hw0 : Real.exp (δ * s 0) = 1 := by rw [hs0, mul_zero, Real.exp_zero]
  rw [hw0, one_smul] at h
  have hsum := increasing_exp_grid_profile_sum_le s R hs hs0 hR δ B hδ hB N hprofile
  linarith only [h, hsum, hterminal]

/-- A decreasing profile-to-scale ratio lets a terminal band control all
earlier Abel increments. The resulting bound retains the full endpoint
profile, with an additional error proportional to the damping shift. -/
theorem signedVector_profile_band_bound
    (u : ℕ → E) (f : E) (g : ℝ → ℝ) (C d c : ℝ)
    (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hratio : ∀ s T : ℝ, 6 ≤ s → s ≤ T → g T / T ≤ g s / s)
    (hdom : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 6 ≤ s →
      Real.exp (-(d - c) * g s) ≤ B / s ^ 2)
    (herror : ∀ n : ℕ, ‖signedVectorPrefix u n - f‖ ≤
      C * Real.exp (-d * g (6 + Real.log ((n + 1 : ℕ) : ℝ)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, ∀ δ : ℝ, 0 ≤ δ →
      δ * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ≤
        c * g (6 + Real.log ((M + 1 : ℕ) : ℝ)) →
      ‖(∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℝ) ^ δ • u n) - f‖ ≤
        C * Real.exp (-(d - c) * g (6 + Real.log ((M + 1 : ℕ) : ℝ))) + B * δ := by
  obtain ⟨B, hB, hdom⟩ := hdom
  refine ⟨C * B / 6, by positivity, fun M δ hδ hband => ?_⟩
  let s : ℕ → ℝ := fun n => Real.log ((n + 1 : ℕ) : ℝ)
  let R : ℕ → ℝ := fun n => C * Real.exp (-d * g (6 + s n))
  have hs : Monotone s := by
    intro i j hij
    exact Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hs0 : s 0 = 0 := by simp [s]
  have hsn (n : ℕ) : 0 ≤ s n := by simpa only [hs0] using hs (Nat.zero_le n)
  have hR (n : ℕ) : 0 ≤ R n := mul_nonneg hC (Real.exp_pos _).le
  have hweight (n : ℕ) (hn : n ≤ M) :
      Real.exp (δ * s n) * R n ≤ C * Real.exp (-(d - c) * g (6 + s n)) := by
    have hLn : 0 < 6 + s n := by linarith [hsn n]
    have hLM : 0 < 6 + s M := by linarith [hsn M]
    have hr := hratio (6 + s n) (6 + s M) (by linarith [hsn n])
      (by linarith [hs hn])
    have hdM : δ ≤ c * (g (6 + s M) / (6 + s M)) := by
      simpa only [mul_div_assoc] using (le_div_iff₀ hLM).mpr hband
    have hdn : δ ≤ c * (g (6 + s n) / (6 + s n)) :=
      hdM.trans (mul_le_mul_of_nonneg_left hr hc)
    have hsmall : δ * (6 + s n) ≤ c * g (6 + s n) := by
      apply (le_div_iff₀ hLn).mp
      simpa only [mul_div_assoc] using hdn
    have harg : δ * s n - d * g (6 + s n) ≤ -(d - c) * g (6 + s n) := by
      nlinarith only [hsmall, hδ]
    calc
      _ = C * Real.exp (δ * s n - d * g (6 + s n)) := by
        dsimp [R]
        rw [← mul_assoc, mul_comm (Real.exp _) C, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hC
  have hp (n : ℕ) (hn : n ≤ M) :
      Real.exp (δ * s n) * R n ≤ (C * B) / (6 + s n) ^ 2 := by
    apply (hweight n hn).trans
    have h := mul_le_mul_of_nonneg_left (hdom (6 + s n) (by linarith [hsn n])) hC
    simpa only [mul_div_assoc] using h
  have hw (n : ℕ) : ((n + 1 : ℕ) : ℝ) ^ δ = Real.exp (δ * s n) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    dsimp [s]
    congr 1
    ring
  cases M with
  | zero =>
      have he := herror 0
      have hw0 := hweight 0 le_rfl
      rw [hs0, mul_zero, Real.exp_zero, one_mul] at hw0
      have hn : 0 ≤ (C * B / 6) * δ := by positivity
      have ht := he.trans hw0
      simpa only [signedVectorPrefix, Finset.range_zero, Finset.sum_empty,
        Nat.zero_add, Nat.cast_one, Real.log_one, add_zero] using
        (le_trans ht (le_add_of_nonneg_right hn))
  | succ N =>
      have ht : Real.exp (δ * s N) * R (N + 1) ≤
          C * Real.exp (-(d - c) * g (6 + s (N + 1))) := by
        apply le_trans _ (hweight (N + 1) le_rfl)
        apply mul_le_mul_of_nonneg_right _ (hR _)
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hs (Nat.le_succ N)) hδ)
      have he (n : ℕ) : ‖signedVectorPrefix u (n + 1) - f‖ ≤ R (n + 1) := herror (n + 1)
      have h := signedVector_increasing_exp_grid_bound u f s R hs hs0 hR he δ (C * B)
        (C * Real.exp (-(d - c) * g (6 + s (N + 1)))) hδ (mul_nonneg hC hB) N
        (fun n hn => hp n (hn.trans (Nat.le_succ N))) ht
      simp_rw [hw]
      convert h using 1 <;> dsimp [s] <;> ring

/-- The optimized logarithmic-product profile loses no exponent in Abel
transfer. Any fixed coefficient below the endpoint decay constant is
admissible. -/
theorem signedVector_logProductPower_band_bound
    (u : ℕ → E) (f : E) (C d c β : ℝ)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hcd : c < d)
    (hβ : 0 < β) (hβ2 : 2 * β ≤ 1)
    (herror : ∀ n : ℕ, ‖signedVectorPrefix u n - f‖ ≤
      C * Real.exp (-d * logProductPower β (6 + Real.log ((n + 1 : ℕ) : ℝ)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, ∀ δ : ℝ, 0 ≤ δ →
      δ * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ≤
        c * logProductPower β (6 + Real.log ((M + 1 : ℕ) : ℝ)) →
      ‖(∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℝ) ^ δ • u n) - f‖ ≤
        C * Real.exp (-(d - c) * logProductPower β
          (6 + Real.log ((M + 1 : ℕ) : ℝ))) + B * δ := by
  apply signedVector_profile_band_bound u f (logProductPower β) C d c hC hc
    (fun s T hs hsT => logProductPower_div_antitone β hβ.le hβ2 hs hsT) _ herror
  obtain ⟨B, hB, hdom⟩ := stretchedExp_le_inverse_square (d - c) β (by linarith) hβ
  refine ⟨B, hB, fun s hs => ?_⟩
  apply le_trans _ (hdom s (by linarith))
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (logProductPower_lower β hβ.le hs) (by linarith)

/-- The full optimized moving band converges. Damping convergence is
deduced from its band condition; no separate damping-limit premise is
needed. -/
theorem signedVector_logProductPower_band_tendsto
    (u : ℕ → E) (f : E) (C d c β : ℝ)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hcd : c < d)
    (hβ : 0 < β) (hβ2 : 2 * β < 1)
    (herror : ∀ n : ℕ, ‖signedVectorPrefix u n - f‖ ≤
      C * Real.exp (-d * logProductPower β (6 + Real.log ((n + 1 : ℕ) : ℝ))))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 ≤ δ j)
    (hband : ∀ᶠ j in atTop,
      δ j * (6 + Real.log ((M j + 1 : ℕ) : ℝ)) ≤
        c * logProductPower β (6 + Real.log ((M j + 1 : ℕ) : ℝ))) :
    Tendsto (fun j => ∑ n ∈ Finset.range (M j), ((n + 1 : ℕ) : ℝ) ^ (δ j) • u n)
      atTop (𝓝 f) := by
  let L : ℕ → ℝ := fun j => 6 + Real.log ((M j + 1 : ℕ) : ℝ)
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hM)))
  have hd := logProductPower_band_shift_tendsto_zero L δ hL hδ β c hβ.le hβ2 hband
  obtain ⟨B, hB, hb⟩ := signedVector_logProductPower_band_bound u f C d c β hC hc hcd
    hβ hβ2.le herror
  have hexp : Tendsto (fun j => Real.exp (-(d - c) * logProductPower β (L j)))
      atTop (𝓝 0) := by
    apply Real.tendsto_exp_comp_nhds_zero.mpr
    exact ((tendsto_logProductPower_atTop β hβ).comp hL).const_mul_atTop_of_neg (by linarith)
  have hbudget : Tendsto (fun j =>
      C * Real.exp (-(d - c) * logProductPower β (L j)) + B * δ j) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hexp.const_mul C).add (hd.const_mul B)
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hbudget η hη
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hband
  refine ⟨max J K, fun j hj => ?_⟩
  rw [dist_eq_norm]
  apply (hb (M j) (δ j) (hδ j) (hK j ((le_max_right _ _).trans hj))).trans_lt
  have h := hJ j ((le_max_left _ _).trans hj)
  rw [dist_zero_right, Real.norm_eq_abs] at h
  exact lt_of_le_of_lt (le_abs_self _) h

end RiemannResearch.Analysis
