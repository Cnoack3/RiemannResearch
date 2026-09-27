/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MonotoneAbelConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vector Kronecker lemma from complete signed prefixes

For a naturally convergent vector series and positive increasing weights
w tending to infinity, the weighted partial sum divided by w(M) tends
to zero in norm. The power specialization supplies inverse-damping
estimates for the arithmetic residue vectors.

This is the classical Kronecker argument, proved here by the exact
finite Abel identity from `SignedPowerDampingAbel`. Shifted signed
prefixes give a uniform tail bound, and normalization kills each fixed
finite head. No absolute summability or completeness assumption is used.
No mathematical novelty is claimed for this analytic lemma.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Increasing weights have signed-prefix norm cost at most twice their
terminal value. -/
theorem signedVector_increasing_weight_norm_le
    (u : ℕ → E) (w : ℕ → ℝ) (hw : Monotone w)
    (hwn : ∀ n, 0 ≤ w n) {C : ℝ} (hC : 0 ≤ C)
    (hprefix : ∀ n, ‖signedVectorPrefix u n‖ ≤ C) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n • u n‖ ≤ 2 * w N * C := by
  cases N with
  | zero => simpa using mul_nonneg (mul_nonneg (by norm_num) (hwn 0)) hC
  | succ N =>
    rw [signedVector_power_weight_identity]
    calc
      _ ≤ ‖w N • signedVectorPrefix u (N + 1)‖ +
          ∑ n ∈ Finset.range N, ‖(w n - w (n + 1)) • signedVectorPrefix u (n + 1)‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ w N * C + ∑ n ∈ Finset.range N, (w (n + 1) - w n) * C := by
        apply add_le_add
        · rw [norm_smul, Real.norm_of_nonneg (hwn N)]
          exact mul_le_mul_of_nonneg_left (hprefix _) (hwn N)
        · apply Finset.sum_le_sum
          intro n hn
          have hdiff : 0 ≤ w (n + 1) - w n := sub_nonneg.mpr (hw (Nat.le_succ n))
          rw [norm_smul, Real.norm_eq_abs, abs_sub_comm,
            abs_of_nonneg hdiff]
          exact mul_le_mul_of_nonneg_left (hprefix _) hdiff
      _ = (2 * w N - w 0) * C := by
        rw [← Finset.sum_mul, Finset.sum_range_sub]
        ring
      _ ≤ 2 * w (N + 1) * C := by
        apply mul_le_mul_of_nonneg_right _ hC
        linarith [hw (Nat.le_succ N), hwn 0]

/-- The same estimate applies to complete signed tails after any cutoff. -/
theorem signedVector_increasing_weight_tail_le
    (u : ℕ → E) (w : ℕ → ℝ) (hw : Monotone w)
    (hwn : ∀ n, 0 ≤ w n) {C : ℝ} (hC : 0 ≤ C)
    {K M : ℕ} (hKM : K ≤ M)
    (htail : ∀ n, ‖signedVectorPrefix u (K + n) - signedVectorPrefix u K‖ ≤ C) :
    ‖(∑ n ∈ Finset.range M, w n • u n) -
      ∑ n ∈ Finset.range K, w n • u n‖ ≤ 2 * w M * C := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hKM
  rw [Finset.sum_range_add, add_sub_cancel_left]
  exact signedVector_increasing_weight_norm_le (fun n => u (K + n))
    (fun n => w (K + n)) (fun i j hij => hw (Nat.add_le_add_left hij K))
    (fun n => hwn (K + n)) hC
    (fun n => by rw [signedVectorPrefix_shift]; exact htail n) m

/-- Vector Kronecker lemma for arbitrary positive increasing unbounded weights. -/
theorem signedVector_kronecker_tendsto
    (u : ℕ → E) {f : E} (hf : Tendsto (signedVectorPrefix u) atTop (𝓝 f))
    (w : ℕ → ℝ) (hw : Monotone w) (hwp : ∀ n, 0 < w n)
    (hwlim : Tendsto w atTop atTop) :
    Tendsto (fun M => (w M)⁻¹ • ∑ n ∈ Finset.range M, w n • u n)
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hf.cauchySeq (η / 4) (by positivity)
  have htail (n : ℕ) :
      ‖signedVectorPrefix u (K + n) - signedVectorPrefix u K‖ ≤ η / 4 := by
    simpa only [dist_eq_norm] using (hK (K + n) (by omega) K le_rfl).le
  have hhead : Tendsto (fun M => (w M)⁻¹ •
      ∑ n ∈ Finset.range K, w n • u n) atTop (𝓝 0) := by
    simpa only [zero_smul, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hwlim).smul_const
        (∑ n ∈ Finset.range K, w n • u n)
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hhead (η / 2) (by positivity)
  refine ⟨max K J, fun M hM => ?_⟩
  have hKM : K ≤ M := (le_max_left _ _).trans hM
  have hJM : J ≤ M := (le_max_right _ _).trans hM
  have ht := signedVector_increasing_weight_tail_le u w hw
    (fun n => (hwp n).le) (by positivity : 0 ≤ η / 4) hKM htail
  have ht' : ‖(w M)⁻¹ • ((∑ n ∈ Finset.range M, w n • u n) -
      ∑ n ∈ Finset.range K, w n • u n)‖ ≤ η / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hwp M).le)]
    calc
      _ ≤ (w M)⁻¹ * (2 * w M * (η / 4)) :=
        mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (hwp M).le)
      _ = _ := by field_simp [(hwp M).ne']; ring
  have hh : ‖(w M)⁻¹ • ∑ n ∈ Finset.range K, w n • u n‖ < η / 2 := by
    simpa only [dist_zero_right] using hJ M hJM
  rw [dist_zero_right]
  have htri := norm_add_le
    ((w M)⁻¹ • ((∑ n ∈ Finset.range M, w n • u n) -
      ∑ n ∈ Finset.range K, w n • u n))
    ((w M)⁻¹ • ∑ n ∈ Finset.range K, w n • u n)
  rw [← smul_add, sub_add_cancel] at htri
  linarith

/-- Power normalization in the vector Kronecker lemma. -/
theorem signedVector_power_undamping_tendsto
    (u : ℕ → E) {f : E} (hf : Tendsto (signedVectorPrefix u) atTop (𝓝 f))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun M => ((M + 1 : ℕ) : ℝ) ^ (-δ) •
      ∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℝ) ^ δ • u n) atTop (𝓝 0) := by
  have hw : Monotone (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ δ) := by
    intro i j hij
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1) hδ.le
  have hlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have h := signedVector_kronecker_tendsto u hf _ hw (fun n => by positivity) hlim
  simpa only [Real.rpow_neg (by positivity : 0 ≤ (( _ + 1 : ℕ) : ℝ))] using h

end RiemannResearch.Analysis
