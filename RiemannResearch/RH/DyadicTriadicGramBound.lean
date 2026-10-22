import RiemannResearch.Analysis.TriadicMantissaSeparation
import RiemannResearch.Analysis.RotationLogarithmicPrefix
import RiemannResearch.RH.DyadicStepGramCutoff
import Mathlib.Data.Nat.Log

/-!
# The actual off-diagonal triadic Gram majorant

Source: user-provided continuation and
`RH/Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`, Sections 2--4.
Arithmetic nearest-integer separation and actual boundary coefficient locality
are combined here. The Gram majorant is a proved provider, with no assumed
off-diagonal estimate and no unproved tent representation.
-/

namespace RiemannResearch.Analysis
noncomputable section

/-- A dyadic separation radius can be chosen within one of its real
logarithmic value. -/
theorem exists_dyadic_inverse_cutoff {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∃ R : ℕ, 1 / (2 : ℝ) ^ R ≤ δ ∧
      (R : ℝ) ≤ 1 + Real.log (1 / δ) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδinv : 1 ≤ 1 / δ := (le_div_iff₀ hδ).2 (by simpa using hδone)
  let x : ℝ := Real.log (1 / δ) / Real.log 2
  have hx : 0 ≤ x := div_nonneg (Real.log_nonneg hδinv) hlog2.le
  let R : ℕ := Nat.ceil x
  have hxR : x ≤ (R : ℝ) := Nat.le_ceil x
  have hRx : (R : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have hlog : Real.log (1 / δ) ≤ (R : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp hxR
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (one_div_pos.mpr hδ), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  refine ⟨R, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ R)).2
    have h := (div_le_iff₀ hδ).mp hexp
    nlinarith
  · dsimp [x] at hRx
    linarith

end
end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

/-- The explicit logarithmic majorant bounds the complete actual raw Gram
pairing of distinct triadic steps. -/
theorem dyadicProjectedStep_triadic_off_diagonal (j k : ℕ) (hjk : j < k) :
    |inner ℝ (dyadicProjectedStep (3 ^ (j+1)) (by positivity))
      (dyadicProjectedStep (3 ^ (k+1)) (by positivity))| ≤
        triadicLogGramMajorant (k-j) := by
  let m : ℕ := 3 ^ (j+1)
  let n : ℕ := 3 ^ (k+1)
  let M : ℕ := Nat.log 2 m
  let N : ℕ := Nat.log 2 n
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hmlo : 2 ^ M ≤ m := Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
  have hnlo : 2 ^ N ≤ n := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  have hmhi : m ≤ 2 ^ (M+1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m).le
  have hnhi : n ≤ 2 ^ (N+1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le
  have hjmantissa : 1 ≤ triadicDyadicMantissa j M := by
    unfold triadicDyadicMantissa
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)).2
    simp only [one_mul]
    exact_mod_cast hmlo
  have hkmantissa : 1 ≤ triadicDyadicMantissa k N := by
    unfold triadicDyadicMantissa
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)).2
    simp only [one_mul]
    exact_mod_cast hnlo
  let d : ℝ := rotationNearestDistance triadicRotation (k-j)
  have hd : 0 < d := triadicRotation_distance_pos (Nat.sub_pos_of_lt hjk)
  have hdhalf : d ≤ 1/2 := rotationNearestDistance_le_half triadicRotation (k-j)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hδ : 0 < Real.log 2 * d := mul_pos hlog2 hd
  have hδone : Real.log 2 * d ≤ 1 := by nlinarith
  obtain ⟨R, hcut, hR⟩ := exists_dyadic_inverse_cutoff hδ hδone
  have hmantissa := triadicDyadicMantissa_separation (Nat.le_of_lt hjk)
    hjmantissa hkmantissa
  have hsep : 1 / (2 : ℝ) ^ R ≤ |(m : ℝ) / (2 : ℝ) ^ M -
      (n : ℝ) / (2 : ℝ) ^ N| := by
    have h := hcut.trans hmantissa
    simpa [m, n, d, triadicDyadicMantissa] using h
  have hgram := dyadicProjectedStep_inner_le_of_mantissa_separation
    M N m n R hm hn hmlo hmhi hnlo hnhi hsep
  have hnonneg : 0 ≤ inner ℝ (dyadicProjectedStep m hm) (dyadicProjectedStep n hn) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (dyadicProjectedStep_inner_ge_one m n hm hn)
  have hsplit : Real.log (1 / (Real.log 2 * d)) =
      Real.log (1 / Real.log 2) + Real.log (1 / d) := by
    rw [← one_div_mul_one_div, Real.log_mul
      (ne_of_gt (one_div_pos.mpr hlog2)) (ne_of_gt (one_div_pos.mpr hd))]
  rw [hsplit] at hR
  have hmajorant : triadicLogGramMajorant (k-j) =
      5/4 + (Real.log (1 / Real.log 2) + Real.log (1 / d)) / (4 * Real.log 2) := by
    have hdiff : 0 < k-j := Nat.sub_pos_of_lt hjk
    cases he : k-j with
    | zero => omega
    | succ h => simp only [he, triadicLogGramMajorant, d]
  have hscalar : 1 + (R : ℝ) / 4 ≤ triadicLogGramMajorant (k-j) := by
    rw [hmajorant]
    calc
      1 + (R : ℝ) / 4 ≤
          1 + (1 + (Real.log (1 / Real.log 2) + Real.log (1 / d)) / Real.log 2) / 4 := by
        linarith
      _ = _ := by ring
  change |inner ℝ (dyadicProjectedStep m hm) (dyadicProjectedStep n hn)| ≤ _
  rw [abs_of_nonneg hnonneg]
  exact hgram.trans hscalar

end
end RiemannResearch.RH.Pareto
