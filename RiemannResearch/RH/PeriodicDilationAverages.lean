import RiemannResearch.Analysis.BoundedPrimitiveAbel
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ThresholdHilbertAdjoint

/-!
# Scaled adjoints of dilations on periodic physical coordinates

The Pareto adjoint averages one complete dilation block with decreasing
weights. A bounded primitive of the centered periodic profile controls
the whole block by its first weight, uniformly over its starting site.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PeriodicDilation
open RiemannResearch.Analysis CoefficientStabilization

private theorem block_bound (v : ℕ → ℝ) (μ : ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ C) (hd : ∀ n, b (n + 1) - b n = v n - μ)
    (s m : ℕ) (hs : 0 < s) :
    |∑ n ∈ Finset.Ico s (s + m), positiveWeight n * (v n - μ)| ≤ C * positiveWeight s := by
  let f (i : ℕ) := positiveWeight (s + i)
  have hmono : Antitone f := by
    intro i j hij
    change 1 / _ ≤ 1 / _
    apply one_div_le_one_div_of_le (by positivity)
    have hle : ((s + i : ℕ) : ℝ) ≤ ((s + j : ℕ) : ℝ) := by
      exact_mod_cast (Nat.add_le_add_left hij s)
    exact mul_le_mul hle (by linarith) (by positivity) (by positivity)
  have h := boundedPrimitive_weighted_interval_bound (fun i => b (s + i)) f C m
    (fun i => hb _) (fun i => positiveWeight_nonneg _) hmono
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  simpa only [← Nat.add_assoc, hd, f, Nat.add_zero, mul_comm] using h

/-- If the centered physical sequence has a primitive ranging over an interval
of length C, the entire dilation adjoint is within 2C/m of the scalar mean. -/
theorem adjoint_norm_bound_of_primitive (v : ThresholdHilbert) (μ C : ℝ) (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ C)
    (hd : ∀ n, b (n + 1) - b n = hilbertSequence v n - μ)
    (m : ℕ) (hm : 0 < m) :
    ‖hilbertDilationAdjoint m hm v - μ • hilbertOne‖ ≤ 2 * C / (m : ℝ) := by
  have hC := (hb 0).1.trans (hb 0).2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs (k : ℕ) (hk : 0 < k) :
      |hilbertSequence (hilbertDilationAdjoint m hm v - μ • hilbertOne) k| ≤ 2 * C / (m : ℝ) := by
    have hw : 0 < positiveWeight k := by unfold positiveWeight; positivity
    have hsum := positiveWeight_block m k hm hk
    have he : hilbertSequence (hilbertDilationAdjoint m hm v - μ • hilbertOne) k =
        (m : ℝ) / positiveWeight k * ∑ n ∈ Finset.Ico (m * k) (m * (k + 1)),
          positiveWeight n * (hilbertSequence v n - μ) := by
      rw [← anchoredEvaluationCLM_apply, map_sub, map_smul]
      simp only [anchoredEvaluationCLM_apply, hilbertDilationAdjoint_coordinate m k hm hk,
        hilbertOne_sequence, zeroAnchor, if_neg hk.ne', smul_eq_mul, mul_one]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
      field_simp [hw.ne', hmR.ne']
    rw [he, abs_mul, abs_of_nonneg (div_nonneg hmR.le hw.le), Nat.mul_succ]
    have h := block_bound (hilbertSequence v) μ b C hb hd (m * k) m (Nat.mul_pos hm hk)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hrat : (m : ℝ) / positiveWeight k * positiveWeight (m * k) ≤ 2 / (m : ℝ) := by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have heq : (m : ℝ) / positiveWeight k * positiveWeight (m * k) =
          ((k : ℝ)+1)/((m : ℝ)*k + 1) := by
        unfold positiveWeight
        push_cast
        field_simp [hmR.ne', hkR.ne']
      rw [heq]
      apply (div_le_div_iff₀ (by positivity) hmR).mpr
      nlinarith only [mul_nonneg hmR.le (sub_nonneg.mpr hk1)]
    calc
      _ ≤ (m : ℝ) / positiveWeight k * (C * positiveWeight (m * k)) :=
        mul_le_mul_of_nonneg_left h (div_nonneg hmR.le hw.le)
      _ = C * ((m : ℝ) / positiveWeight k * positiveWeight (m * k)) := by ring
      _ ≤ C * (2 / (m : ℝ)) := mul_le_mul_of_nonneg_left hrat hC
      _ = _ := by ring
  let y := hilbertDilationAdjoint m hm v - μ • hilbertOne
  have hK : 0 ≤ 2 * C / (m : ℝ) := by positivity
  have hy (k : ℕ) : |hilbertSequence y k| ≤ 2 * C / (m : ℝ) := by
    cases k with
    | zero => simpa using hK
    | succ k => exact hs _ (by omega)
  have hsq : ‖y‖ ^ 2 ≤ (2 * C / (m : ℝ))^2 := by
    calc
      _ = ∑' k, positiveWeight k * hilbertSequence y k ^ 2 := hilbert_norm_weighted_sq _
      _ ≤ ∑' k, positiveWeight k * (2 * C / (m : ℝ))^2 := by
        apply Summable.tsum_le_tsum _ (hilbertSequence_square_summable y)
          (positiveWeight_summable.mul_right _)
        intro k
        apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hy k)
      _ = _ := by rw [tsum_mul_right, positiveWeight_tsum, one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) hK).mp hsq

/-- The ordinary periodic mean of the normalized residue at conductor d. -/
def residueMean (d : ℕ) : ℝ := ((d : ℝ) - 1) / (2 * d)

/-- For one residue the range of the quadratic primitive is at most d/8. -/
theorem residue_adjoint_bound (d : ℕ) (hd : 0 < d) (m : ℕ) (hm : 0 < m) :
    ‖hilbertDilationAdjoint m hm (normalizedResidueHilbert d hd) - residueMean d • hilbertOne‖
      ≤ (d : ℝ) / (4 * m) := by
  let b (k : ℕ) := (2 * ((k % d : ℕ) : ℝ) - d)^2 / (8 * d)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hb (k : ℕ) : 0 ≤ b k ∧ b k ≤ (d : ℝ)/8 := by
    have hr : ((k % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt k hd).le
    constructor
    · dsimp [b]; positivity
    · dsimp [b]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [mul_nonneg (Nat.cast_nonneg (k % d) (α := ℝ)) (sub_nonneg.mpr hr)]
  have hdif (k : ℕ) : b (k + 1) - b k =
      hilbertSequence (normalizedResidueHilbert d hd) k - residueMean d := by
    rw [normalizedResidueHilbert_sequence]
    dsimp [b, ArithmeticCumulative.residueFraction, residueMean]
    rw [show (k + 1) % d = (k % d + 1) % d by simp]
    by_cases hw : k % d + 1 = d
    · have he : ((k % d : ℕ) : ℝ) + 1 = d := by exact_mod_cast hw
      rw [hw, Nat.mod_self, Nat.cast_zero]
      field_simp [hdR.ne']
      rw [← he]
      ring
    · have hw' : k % d + 1 < d := by have := Nat.mod_lt k hd; omega
      rw [Nat.mod_eq_of_lt hw', Nat.cast_add, Nat.cast_one]
      field_simp [hdR.ne']
      ring
  calc
    _ ≤ 2 * ((d : ℝ)/8) / (m : ℝ) :=
      adjoint_norm_bound_of_primitive _ _ _ b hb hdif m hm
    _ = _ := by ring

/-- The finite fit's explicit bound is a weighted sum of its residue
coefficients, independent of their least common period. -/
theorem residue_expansion_adjoint_bound {n : ℕ} (a : Fin n → ℝ) (m : ℕ) (hm : 0 < m) :
    ‖hilbertDilationAdjoint m hm (∑ i, a i • residueAtom i.val) -
        (∑ i, a i * residueMean (i.val + 2)) • hilbertOne‖ ≤
      (∑ i, |a i| * ((i.val : ℝ) + 2)) / (4 * m) := by
  have he : hilbertDilationAdjoint m hm (∑ i, a i • residueAtom i.val) -
      (∑ i, a i * residueMean (i.val + 2)) • hilbertOne =
      ∑ i, a i • (hilbertDilationAdjoint m hm (residueAtom i.val) -
        residueMean (i.val + 2) • hilbertOne) := by
    rw [map_sum, Finset.sum_smul]
    simp only [map_smul, smul_sub, smul_smul, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, ‖a i • (hilbertDilationAdjoint m hm (residueAtom i.val) -
        residueMean (i.val + 2) • hilbertOne)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (|a i| * ((i.val : ℝ) + 2)) / (4 * m) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact_mod_cast residue_adjoint_bound (i.val + 2) (by omega) m hm
    _ = _ := (Finset.sum_div ..).symm

/-- Every finite legal packet fit has an adjoint limit at all integer scales
with error bounded by a single constant divided by the scale. -/
theorem finiteSpace_adjoint_bound (n : ℕ) {v : ThresholdHilbert} (hv : v ∈ finiteSpace n) :
    ∃ μ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (hm : 0 < m),
      ‖hilbertDilationAdjoint m hm v - μ • hilbertOne‖ ≤ K / (m : ℝ) := by
  obtain ⟨a, rfl⟩ := finiteSpace_expansion n v hv
  let W := ∑ i, |a i| * ((i.val : ℝ) + 2)
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by positivity)
  refine ⟨∑ i, a i * residueMean (i.val + 2), W / 4, by positivity, fun m hm => ?_⟩
  calc
    _ ≤ W / (4 * m) := residue_expansion_adjoint_bound a m hm
    _ = W / 4 / m := by ring

end RiemannResearch.RH.Pareto.PeriodicDilation
