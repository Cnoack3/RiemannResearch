/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SignedPowerDampingAbel

/-!
# Uniform Abel convergence for monotone vector weights

Positive decreasing weights with initial mass at most one preserve a
bound on complete signed prefixes and their tails. Hence a convergent
vector series has one Cauchy modulus for every such weighted series,
and one approximation modulus for all of their existing limits.
Weights tending coordinatewise to one may vary together with an
arbitrarily diverging cutoff.

The proof is finite summation by parts through
`signedVector_power_weight_identity`, followed by the norm triangle
inequality and telescoping of the nonnegative coefficient masses.
These are standard Abel arguments; no mathematical novelty is claimed.
No absolute summability or completeness assumption is needed when the
relevant naturally ordered limits are supplied.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive decreasing weights preserve a common signed-prefix norm bound. -/
theorem signedVector_monotone_weight_norm_le
    (u : ℕ → E) (w : ℕ → ℝ) (hw : Antitone w)
    (hwn : ∀ n, 0 ≤ w n) {C : ℝ} (hC : 0 ≤ C)
    (hprefix : ∀ n, ‖signedVectorPrefix u n‖ ≤ C) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n • u n‖ ≤ w 0 * C := by
  cases N with
  | zero => simpa using mul_nonneg (hwn 0) hC
  | succ N =>
    rw [signedVector_power_weight_identity]
    calc
      _ ≤ ‖w N • signedVectorPrefix u (N + 1)‖ +
          ∑ n ∈ Finset.range N, ‖(w n - w (n + 1)) • signedVectorPrefix u (n + 1)‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ w N * C + ∑ n ∈ Finset.range N, (w n - w (n + 1)) * C := by
        apply add_le_add
        · rw [norm_smul, Real.norm_of_nonneg (hwn N)]
          exact mul_le_mul_of_nonneg_left (hprefix _) (hwn N)
        · apply Finset.sum_le_sum
          intro n hn
          have hdiff : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hw (Nat.le_succ n))
          rw [norm_smul, Real.norm_of_nonneg hdiff]
          exact mul_le_mul_of_nonneg_left (hprefix _) hdiff
      _ = w 0 * C := by
        rw [← Finset.sum_mul, Finset.sum_range_sub']
        ring

omit [NormedSpace ℝ E] in
/-- A shifted signed prefix is an exact difference of the original prefixes. -/
theorem signedVectorPrefix_shift (u : ℕ → E) (K n : ℕ) :
    signedVectorPrefix (fun m => u (K + m)) n =
      signedVectorPrefix u (K + n) - signedVectorPrefix u K := by
  unfold signedVectorPrefix
  rw [Finset.sum_range_add]
  simp


/-- Positive decreasing weights cannot enlarge a common signed tail bound. -/
theorem signedVector_monotone_weight_tail_le
    (u : ℕ → E) (w : ℕ → ℝ) (hw : Antitone w)
    (hwn : ∀ n, 0 ≤ w n) (hw0 : w 0 ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) {K M : ℕ} (hKM : K ≤ M)
    (htail : ∀ n, ‖signedVectorPrefix u (K + n) - signedVectorPrefix u K‖ ≤ C) :
    ‖(∑ n ∈ Finset.range M, w n • u n) -
      ∑ n ∈ Finset.range K, w n • u n‖ ≤ C := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hKM
  rw [Finset.sum_range_add, add_sub_cancel_left]
  have h := signedVector_monotone_weight_norm_le (fun n => u (K + n))
    (fun n => w (K + n)) (fun i j hij => hw (Nat.add_le_add_left hij K))
    (fun n => hwn (K + n)) hC
    (fun n => by rw [signedVectorPrefix_shift]; exact htail n) m
  apply h.trans
  apply mul_le_of_le_one_left hC
  exact (hw (Nat.zero_le _)).trans hw0

/-- One tail modulus works for every positive decreasing normalized weight. -/
theorem signedVector_monotone_weights_uniform_cauchy
    (u : ℕ → E) {f : E} (hf : Tendsto (signedVectorPrefix u) atTop (𝓝 f)) :
    ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ w : ℕ → ℝ,
      Antitone w → (∀ n, 0 ≤ w n) → w 0 ≤ 1 →
      ∀ M : ℕ, K ≤ M →
        ‖(∑ n ∈ Finset.range M, w n • u n) -
          ∑ n ∈ Finset.range K, w n • u n‖ ≤ η := by
  intro η hη
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hf.cauchySeq η hη
  refine ⟨K, fun w hw hwn hw0 M hKM => ?_⟩
  apply signedVector_monotone_weight_tail_le u w hw hwn hw0 hη.le hKM
  intro n
  simpa only [dist_eq_norm] using (hK (K + n) (by omega) K le_rfl).le

/-- Joint Abel regularity: the cutoff may grow at any rate while all fixed
weights tend to one. No absolute summability of the vectors is required. -/
theorem signedVector_monotone_weights_joint_tendsto
    (u : ℕ → E) {f : E} (hf : Tendsto (signedVectorPrefix u) atTop (𝓝 f))
    (w : ℕ → ℕ → ℝ) (hw : ∀ j, Antitone (w j))
    (hwn : ∀ j n, 0 ≤ w j n) (hw0 : ∀ j, w j 0 ≤ 1)
    (hlim : ∀ n, Tendsto (fun j => w j n) atTop (𝓝 1))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun j => ∑ n ∈ Finset.range (M j), w j n • u n) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hf (η / 4) (by positivity)
  have hKf : ‖signedVectorPrefix u K - f‖ < η / 4 := by
    simpa only [dist_eq_norm] using hK K le_rfl
  have htail (n : ℕ) :
      ‖signedVectorPrefix u (K + n) - signedVectorPrefix u K‖ ≤ η / 2 := by
    have hn : ‖signedVectorPrefix u (K + n) - f‖ < η / 4 := by
      simpa only [dist_eq_norm] using hK (K + n) (by omega)
    have ht := dist_triangle (signedVectorPrefix u (K + n)) f (signedVectorPrefix u K)
    simp only [dist_eq_norm] at ht
    rw [norm_sub_rev f] at ht
    linarith
  have hhead : Tendsto (fun j => ∑ n ∈ Finset.range K, w j n • u n)
      atTop (𝓝 (signedVectorPrefix u K)) := by
    simpa only [one_smul, signedVectorPrefix] using
      tendsto_finsetSum (Finset.range K) (fun n _ => (hlim n).smul_const (u n))
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hhead (η / 4) (by positivity)
  obtain ⟨J', hJ'⟩ := eventually_atTop.mp (hM.eventually (eventually_ge_atTop K))
  refine ⟨max J J', fun j hj => ?_⟩
  have hj1 : J ≤ j := (le_max_left _ _).trans hj
  have hj2 : J' ≤ j := (le_max_right _ _).trans hj
  have ht := signedVector_monotone_weight_tail_le u (w j) (hw j)
    (hwn j) (hw0 j) (by positivity : 0 ≤ η / 2) (hJ' j hj2) htail
  have hh : ‖(∑ n ∈ Finset.range K, w j n • u n) - signedVectorPrefix u K‖ < η / 4 := by
    simpa only [dist_eq_norm] using hJ j hj1
  rw [dist_eq_norm]
  have h1 := dist_triangle (∑ n ∈ Finset.range (M j), w j n • u n)
    (∑ n ∈ Finset.range K, w j n • u n) f
  have h2 := dist_triangle (∑ n ∈ Finset.range K, w j n • u n)
    (signedVectorPrefix u K) f
  simp only [dist_eq_norm] at h1 h2
  linarith

/-- A common tail modulus also controls distance to every weighted limit. -/
theorem signedVector_monotone_weights_uniform_error
    (u : ℕ → E) {f : E} (hf : Tendsto (signedVectorPrefix u) atTop (𝓝 f)) :
    ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ w : ℕ → ℝ,
      Antitone w → (∀ n, 0 ≤ w n) → w 0 ≤ 1 →
      ∀ g : E, Tendsto (fun M => ∑ n ∈ Finset.range M, w n • u n) atTop (𝓝 g) →
      ∀ M : ℕ, K ≤ M → ‖(∑ n ∈ Finset.range M, w n • u n) - g‖ ≤ η := by
  intro η hη
  obtain ⟨K, hK⟩ := signedVector_monotone_weights_uniform_cauchy u hf (η / 2) (by positivity)
  refine ⟨K, fun w hw hwn hw0 g hg M hM => ?_⟩
  have ht := hK w hw hwn hw0
  have hlim : ‖g - ∑ n ∈ Finset.range K, w n • u n‖ ≤ η / 2 := by
    apply le_of_tendsto ((hg.sub_const _).norm)
    filter_upwards [eventually_ge_atTop K] with m hm
    exact ht m hm
  have htri := dist_triangle (∑ n ∈ Finset.range M, w n • u n)
    (∑ n ∈ Finset.range K, w n • u n) g
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev g] at hlim
  linarith [ht M hM]

end RiemannResearch.Analysis
