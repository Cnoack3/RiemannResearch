import RiemannResearch.RH.ThresholdDilationAlgebra
import RiemannResearch.RH.ParetoResidueMean

/-!
# Exact finite-budget interpolation by the two actual residue seeds

Source: `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`, Section 7,
especially finite composite completion and exact mean correction. This module
uses a direct triangular interpolation proof of the head-surjectivity claim.
All dilations are genuine integer dilations and every displayed mean is the
complete infinite Pareto mean. No assertion of vanishing approximation error
or Riemann hypothesis is made.

-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion

noncomputable section

/-- The actual two-seed space with dilation budget `M`. -/
def budgetSpan (M : ℕ) : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ {f | ∃ a : ℕ, (a = 2 ∨ a = 3) ∧
    ∃ n : ℕ, 0 < n ∧ n ≤ M ∧ f = dilation n (residue a)}

theorem generator_mem (M a n : ℕ) (ha : a = 2 ∨ a = 3)
    (hn : 0 < n) (hnM : n ≤ M) :
    dilation n (residue a) ∈ budgetSpan M :=
  Submodule.subset_span ⟨a, ha, n, hn, hnM, rfl⟩

theorem budgetSpan_mono {M N : ℕ} (hMN : M ≤ N) : budgetSpan M ≤ budgetSpan N := by
  apply Submodule.span_mono
  rintro f ⟨a, ha, n, hn, hnM, rfl⟩
  exact ⟨a, ha, n, hn, hnM.trans hMN, rfl⟩

theorem budgetSpan_le_legal (M : ℕ) : budgetSpan M ≤ legalSeedSpan ({2, 3} : Set ℕ) := by
  apply Submodule.span_le.mpr
  rintro f ⟨a, ha, n, hn, hnM, rfl⟩
  apply dilation_generator_mem ({2, 3} : Set ℕ) _ hn
  rcases ha with rfl | rfl <;> simp

theorem budgetSpan_bounded {M : ℕ} {f : ℕ → ℝ} (hf : f ∈ budgetSpan M) :
    ∃ C : ℝ, ∀ k, |f k| ≤ C := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, n, hn, hnM, rfl⟩ := hf
    have ha0 : 0 < a := by rcases ha with rfl | rfl <;> norm_num
    exact ⟨(n : ℝ) * a, dilation_abs_le (fun k => residue_abs_le a k ha0) n⟩
  | zero => exact ⟨0, by intro k; simp⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨C, hC⟩ := ihf
    obtain ⟨D, hD⟩ := ihg
    exact ⟨C + D, fun k => (abs_add_le (f k) (g k)).trans (add_le_add (hC k) (hD k))⟩
  | smul c f hf ih =>
    obtain ⟨C, hC⟩ := ih
    exact ⟨|c| * C, bounded_const_mul hC c⟩

/-- Every finite-budget mean is absolutely summable. -/
theorem budgetSpan_weighted_summable {M : ℕ} {f : ℕ → ℝ} (hf : f ∈ budgetSpan M) :
    Summable (fun k => positiveWeight k * f k) := by
  obtain ⟨C, hC⟩ := budgetSpan_bounded hf
  exact weighted_summable_of_bounded hC

theorem binary_generator_before (n k : ℕ) (hk : k < n) :
    dilation n (residue 2) k = 0 := by
  simp [dilation, residue, Nat.div_eq_of_lt hk]

theorem binary_generator_at (n : ℕ) (hn : 0 < n) :
    dilation n (residue 2) n = (n : ℝ) := by
  simp [dilation, residue, Nat.div_self hn]

/-- Recursive triangular interpolation using only the seed 2. -/
def headLift (f : ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => 0
  | N + 1 => headLift f N +
      ((f (N + 1) - headLift f N (N + 1)) / ((N + 1 : ℕ) : ℝ)) •
        dilation (N + 1) (residue 2)

theorem headLift_mem (f : ℕ → ℝ) (N : ℕ) : headLift f N ∈ budgetSpan N := by
  induction N with
  | zero => exact (budgetSpan 0).zero_mem
  | succ N ih =>
    apply (budgetSpan (N + 1)).add_mem
    · exact budgetSpan_mono (Nat.le_succ N) ih
    · apply (budgetSpan (N + 1)).smul_mem
      exact generator_mem (N + 1) 2 (N + 1) (Or.inl rfl) (by omega) le_rfl

/-- Every positive coordinate through the full composite head is prescribed. -/
theorem headLift_eq (f : ℕ → ℝ) (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    headLift f N k = f k := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [headLift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases he : k = N + 1
    · subst k
      rw [binary_generator_at (N + 1) (by omega)]
      have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hN] <;> ring
    · have hkN' : k ≤ N := by omega
      rw [binary_generator_before (N + 1) k (by omega), mul_zero, add_zero]
      exact ih hkN'

/-- All finite head data are attained with the same dilation budget. -/
theorem exists_head (f : ℕ → ℝ) (H : ℕ) :
    ∃ F ∈ budgetSpan H, ∀ k, 0 < k → k ≤ H → F k = f k :=
  ⟨headLift f H, headLift_mem f H, headLift_eq f H⟩

/-- A legal mean-changing direction, with no change anywhere in the head. -/
def meanDirection (H : ℕ) : ℕ → ℝ :=
  dilation H (residue 3) - dilation H (residue 2)

theorem meanDirection_mem (H : ℕ) (hH : 0 < H) : meanDirection H ∈ budgetSpan H :=
  (budgetSpan H).sub_mem
    (generator_mem H 3 H (Or.inr rfl) hH le_rfl)
    (generator_mem H 2 H (Or.inl rfl) hH le_rfl)

theorem meanDirection_residues (H k : ℕ) :
    meanDirection H k = residue (3 * H) k - residue (2 * H) k := by
  simp only [meanDirection, Pi.sub_apply, residue_mul_floor]
  rw [Nat.mul_comm H 3, Nat.mul_comm H 2]
  ring

theorem meanDirection_head_zero (H k : ℕ) (hH : 0 < H) (hk : k ≤ H) :
    meanDirection H k = 0 := by
  rw [meanDirection_residues]
  have h2 : k < 2 * H := by omega
  have h3 : k < 3 * H := by omega
  simp [residue, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]

theorem meanDirection_mean (H : ℕ) (hH : 0 < H) :
    paretoMean (meanDirection H) = Real.log 3 - Real.log 2 := by
  change paretoMean (fun k => dilation H (residue 3) k - dilation H (residue 2) k) = _
  rw [paretoMean_sub
    (dilation_abs_le (fun k => residue_abs_le 3 k (by norm_num)) H)
    (dilation_abs_le (fun k => residue_abs_le 2 k (by norm_num)) H)]
  rw [paretoMean_dilation (fun k => residue_abs_le 3 k (by norm_num))
      (by simp [residue]) H hH,
    paretoMean_dilation (fun k => residue_abs_le 2 k (by norm_num))
      (by simp [residue]) H hH,
    paretoMean_residue 3 (by norm_num), paretoMean_residue 2 (by norm_num)]
  norm_num

theorem logarithmic_gap_pos : 0 < Real.log 3 - Real.log 2 := by
  exact sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))

theorem mean_add_smul {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) (c : ℝ) :
    paretoMean (f + c • g) = paretoMean f + c * paretoMean g := by
  unfold paretoMean
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
  rw [(weighted_summable_of_bounded hf).tsum_add
    (weighted_summable_of_bounded (bounded_const_mul hg c))]
  congr 1
  calc
    (∑' k, positiveWeight k * (c * g k)) =
        ∑' k, c * (positiveWeight k * g k) := by
      apply tsum_congr
      intro k
      ring
    _ = c * ∑' k, positiveWeight k * g k :=
      (weighted_summable_of_bounded hg).tsum_mul_left c

/-- A completely explicit simultaneous head-and-mean interpolant. -/
def headMeanLift (f : ℕ → ℝ) (m : ℝ) (H : ℕ) : ℕ → ℝ :=
  headLift f H +
    ((m - paretoMean (headLift f H)) / (Real.log 3 - Real.log 2)) • meanDirection H

theorem headMeanLift_mem (f : ℕ → ℝ) (m : ℝ) (H : ℕ) (hH : 0 < H) :
    headMeanLift f m H ∈ budgetSpan H :=
  (budgetSpan H).add_mem (headLift_mem f H)
    ((budgetSpan H).smul_mem _ (meanDirection_mem H hH))

theorem headMeanLift_head (f : ℕ → ℝ) (m : ℝ) (H : ℕ) (hH : 0 < H)
    (k : ℕ) (hk : 0 < k) (hkH : k ≤ H) : headMeanLift f m H k = f k := by
  simp [headMeanLift, meanDirection_head_zero H k hH hkH, headLift_eq f H k hk hkH]

theorem headMeanLift_mean (f : ℕ → ℝ) (m : ℝ) (H : ℕ) (hH : 0 < H) :
    paretoMean (headMeanLift f m H) = m := by
  obtain ⟨C, hC⟩ := budgetSpan_bounded (headLift_mem f H)
  obtain ⟨D, hD⟩ := budgetSpan_bounded (meanDirection_mem H hH)
  rw [headMeanLift, mean_add_smul hC hD, meanDirection_mean H hH]
  have hgap : Real.log 3 - Real.log 2 ≠ 0 := ne_of_gt logarithmic_gap_pos
  field_simp [hgap] <;> ring

/-- Full finite composite-head completion and arbitrary prescribed Pareto mean. -/
theorem exists_head_mean (f : ℕ → ℝ) (m : ℝ) (H : ℕ) (hH : 0 < H) :
    ∃ F ∈ budgetSpan H,
      (∀ k, 0 < k → k ≤ H → F k = f k) ∧ paretoMean F = m :=
  ⟨headMeanLift f m H, headMeanLift_mem f m H hH,
    headMeanLift_head f m H hH, headMeanLift_mean f m H hH⟩

/-- The increasing finite budgets exhaust exactly the algebraic two-seed span. -/
theorem mem_legal_iff_exists_budget (f : ℕ → ℝ) :
    f ∈ legalSeedSpan ({2, 3} : Set ℕ) ↔ ∃ M, f ∈ budgetSpan M := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, ha, n, hn, rfl⟩ := hf
      have ha' : a = 2 ∨ a = 3 := by simpa using ha
      exact ⟨n, generator_mem n a n ha' hn le_rfl⟩
    | zero => exact ⟨0, (budgetSpan 0).zero_mem⟩
    | add f g hf hg ihf ihg =>
      obtain ⟨M, hM⟩ := ihf
      obtain ⟨N, hN⟩ := ihg
      exact ⟨max M N, (budgetSpan (max M N)).add_mem
        (budgetSpan_mono (le_max_left M N) hM)
        (budgetSpan_mono (le_max_right M N) hN)⟩
    | smul c f hf ih =>
      obtain ⟨M, hM⟩ := ih
      exact ⟨M, (budgetSpan M).smul_mem c hM⟩
  · rintro ⟨M, hM⟩
    exact budgetSpan_le_legal M hM

/-- The same head and mean constraints remain feasible as the budget grows. -/
theorem exists_head_mean_of_le (f : ℕ → ℝ) (m : ℝ) (H M : ℕ)
    (hH : 0 < H) (hHM : H ≤ M) :
    ∃ F ∈ budgetSpan M,
      (∀ k, 0 < k → k ≤ H → F k = f k) ∧ paretoMean F = m := by
  obtain ⟨F, hF, hh, hm⟩ := exists_head_mean f m H hH
  exact ⟨F, budgetSpan_mono hHM hF, hh, hm⟩

/-- Simultaneous interpolation is linear in the prescribed head data. -/
theorem headLift_add (f g : ℕ → ℝ) (N : ℕ) :
    headLift (f + g) N = headLift f N + headLift g N := by
  induction N with
  | zero => simp [headLift]
  | succ N ih =>
    ext k
    simp only [headLift, ih, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Simultaneous interpolation is homogeneous in the prescribed head data. -/
theorem headLift_smul (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    headLift (c • f) N = c • headLift f N := by
  induction N with
  | zero => simp [headLift]
  | succ N ih =>
    ext k
    simp only [headLift, ih, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

end
end RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
