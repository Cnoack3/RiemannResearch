import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ThresholdDilationAlgebra

/-!
# The legal head-preserving mean correction

Source: user-provided legal-sequence conversation, September 11, 2026.
This constructs the exact correction R_(3K)-R_(2K), evaluates its full mean,
and retains its mixed term and exact dilation norm cost. No small-tail estimate
is supplied by these identities.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

def legalMobiusHeadCorrection (K : ℕ) : ℕ → ℝ :=
  dilation K (fun n => residue 3 n - residue 2 n)

theorem legalMobiusHeadCorrection_eq (K n : ℕ) :
    legalMobiusHeadCorrection K n = residue (3*K) n - residue (2*K) n := by
  have he : legalMobiusHeadCorrection K n =
      dilation K (residue 3) n - dilation K (residue 2) n := by
    simp only [legalMobiusHeadCorrection, dilation, mul_sub]
  rw [he, residue_mul_floor, residue_mul_floor]
  simp only [Nat.mul_comm K]
  ring

theorem legalMobiusHeadCorrection_mem (K : ℕ) (hK : 0 < K) :
    legalMobiusHeadCorrection K ∈ legalSeedSpan ({2,3} : Set ℕ) := by
  have h := (legalSeedSpan ({2,3} : Set ℕ)).sub_mem
    (dilation_generator_mem ({2,3} : Set ℕ) (a := 3) (m := K) (by simp) hK)
    (dilation_generator_mem ({2,3} : Set ℕ) (a := 2) (m := K) (by simp) hK)
  have he : legalMobiusHeadCorrection K =
      dilation K (residue 3) - dilation K (residue 2) := by
    funext n
    simp [legalMobiusHeadCorrection, dilation, mul_sub]
  rw [he]
  exact h

theorem legalMobiusHeadCorrection_head_zero (K n : ℕ) (hn : n < 2*K) :
    legalMobiusHeadCorrection K n = 0 := by
  rw [legalMobiusHeadCorrection_eq]
  have hn3 : n < 3*K := by omega
  simp [residue, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn3]

private theorem legalMobiusHeadBase_bound :
    ∀ n, |residue 3 n - residue 2 n| ≤ (5 : ℝ) := by
  convert bounded_sub (fun n => residue_abs_le 3 n (by decide))
    (fun n => residue_abs_le 2 n (by decide))
    using 1 <;> norm_num

theorem legalMobiusHeadCorrection_bound (K n : ℕ) :
    |legalMobiusHeadCorrection K n| ≤ (K : ℝ) * 5 :=
  dilation_abs_le legalMobiusHeadBase_bound K n

/-- Its signal is independent of how far the head is protected. -/
theorem legalMobiusHeadCorrection_mean (K : ℕ) (hK : 0 < K) :
    paretoMean (legalMobiusHeadCorrection K) = Real.log 3 - Real.log 2 := by
  rw [legalMobiusHeadCorrection,
    paretoMean_dilation legalMobiusHeadBase_bound (by simp [residue]) K hK,
    paretoMean_sub (fun n => residue_abs_le 3 n (by decide))
      (fun n => residue_abs_le 2 n (by decide)),
    paretoMean_residue 3 (by decide), paretoMean_residue 2 (by decide)]
  norm_num

/-- Its complete squared norm grows exactly linearly with K. -/
theorem legalMobiusHeadCorrection_norm (K : ℕ) (hK : 0 < K) :
    paretoInner (legalMobiusHeadCorrection K) (legalMobiusHeadCorrection K) =
      (K : ℝ) * paretoInner (legalMobiusHeadCorrection 1) (legalMobiusHeadCorrection 1) := by
  unfold legalMobiusHeadCorrection
  rw [paretoInner_dilation legalMobiusHeadBase_bound legalMobiusHeadBase_bound
    (by simp [residue]) K hK, dilation_one]

/-- Adding this correction retains the original head values exactly. -/
theorem legalMobiusHeadCorrection_preserves (K : ℕ) (hK : 0 < K)
    (f : ℕ → ℝ) (a : ℝ) (n : ℕ) (hn : n ≤ K) :
    f n + a * legalMobiusHeadCorrection K n = f n := by
  rw [legalMobiusHeadCorrection_head_zero K n (by omega)]
  ring

/-- The exact full energy includes the mixed term, even after mean normalization. -/
theorem legalMobiusHeadCorrection_energy (K : ℕ) (hK : 0 < K)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C) (a : ℝ) :
    paretoInner (fun n => f n + a * legalMobiusHeadCorrection K n)
      (fun n => f n + a * legalMobiusHeadCorrection K n) =
      paretoInner f f + 2*a*paretoInner f (legalMobiusHeadCorrection K) +
        a^2*(K : ℝ)*paretoInner (legalMobiusHeadCorrection 1) (legalMobiusHeadCorrection 1) := by
  have h := paretoInner_residual_polynomial hf (legalMobiusHeadCorrection_bound K) (-a)
  simp only [neg_mul, sub_neg_eq_add, neg_sq] at h
  rw [h, legalMobiusHeadCorrection_norm K hK]
  ring

end
end RiemannResearch.RH.Pareto
