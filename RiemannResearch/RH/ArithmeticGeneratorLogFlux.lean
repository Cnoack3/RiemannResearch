import RiemannResearch.RH.ArithmeticFluxResearchTargets
import RiemannResearch.RH.OptimizedResidueHarmonic
/-!
# Exact arbitrary-cutoff arithmetic generator flux

Source: equation (23) of the user-provided contracting-evolution research report.
This module discharges ArithmeticGeneratorLogFluxTarget. The finite formula
retains both harmonic cutoffs; the limit uses the full Pareto mean and the
vanishing Abel boundary term, without subtracting divergent infinite sums.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
theorem arithmeticGeneratorCutoffFlux_eq_harmonic (a m N : ℕ) (ha : 0 < a) (hm : 0 < m) :
 arithmeticGeneratorCutoffFlux a m N =
 (harmonic (N/m) : ℝ) - (harmonic (N/(a*m)) : ℝ) := by
  have hsum : arithmeticGeneratorCutoffFlux a m N =
      ∑ k ∈ Finset.range N, arithmeticGeneratorJump a m (k+1) / ((k : ℝ)+1) := by
    unfold arithmeticGeneratorCutoffFlux
    have hset : Finset.Icc 1 N = Finset.Ico 1 (N+1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset]
    simpa [add_comm] using (Finset.sum_Ico_eq_sum_range (f := fun n => arithmeticGeneratorJump a m n / (n : ℝ)) (m := 1) (n := N+1))
  rw [hsum]
  have hj (k : ℕ) : arithmeticGeneratorJump a m (k+1) / ((k : ℝ)+1) =
      (if m ∣ k+1 then (m : ℝ)/((k : ℝ)+1) else 0) -
      (if a*m ∣ k+1 then ((a*m : ℕ) : ℝ)/((k : ℝ)+1) else 0) := by
    unfold arithmeticGeneratorJump
    have h1 := residue_difference (a*m) (k+1) (by omega)
    have h2 := residue_difference m (k+1) (by omega)
    have he : (residue (a*m) (k+1) - residue m (k+1)) -
      (residue (a*m) (k+1-1) - residue m (k+1-1)) =
      (residue (a*m) (k+1) - residue (a*m) (k+1-1)) -
      (residue m (k+1) - residue m (k+1-1)) := by ring
    rw [he, h1, h2]
    split_ifs <;> ring
  simp_rw [hj]
  rw [Finset.sum_sub_distrib, harmonic_divisibility_sum m N hm,
    harmonic_divisibility_sum (a*m) N (Nat.mul_pos ha hm)]

theorem arithmeticGeneratorCutoffFlux_tendsto_log (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    Tendsto (arithmeticGeneratorCutoffFlux a m) atTop (nhds (Real.log a)) := by
  let f : ℕ → ℝ := fun k => residue (a*m) k - residue m k
  have hb (b : ℕ) (hb : 0 < b) : ∀ k, |residue b k| ≤ (b : ℝ) := by
    intro k
    unfold residue
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.mod_lt k hb).le
  have hf : ∀ k, |f k| ≤ ((a*m : ℕ) : ℝ) + m := by
    intro k
    exact (abs_sub _ _).trans (add_le_add (hb (a*m) (Nat.mul_pos ha hm) k) (hb m hm k))
  have hmean : paretoMean f = Real.log a := by
    unfold paretoMean
    simp only [f, mul_sub]
    rw [((weighted_summable_of_bounded (hb (a*m) (Nat.mul_pos ha hm))).tsum_sub
      (weighted_summable_of_bounded (hb m hm)))]
    change paretoMean (residue (a*m)) - paretoMean (residue m) = _
    rw [paretoMean_residue (a*m) (Nat.mul_pos ha hm), paretoMean_residue m hm]
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    ring
  have hbnd : Tendsto (fun N : ℕ => f N / ((N : ℝ)+1)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
      (show Tendsto (fun N : ℕ => (((a*m : ℕ) : ℝ)+m) / ((N : ℝ)+1)) atTop (nhds 0) from
        by simpa only [mul_zero, mul_one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (((a*m : ℕ) : ℝ)+m))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ)+1)]
    exact div_le_div_of_nonneg_right (hf N) (by positivity)
  have hidx : Tendsto (fun N : ℕ => N+1) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id
  have hs := (weighted_summable_of_bounded hf).hasSum.tendsto_sum_nat.comp hidx
  have hlim := hs.add hbnd
  change Tendsto (fun N => (∑ k ∈ Finset.range (N+1), positiveWeight k * f k) +
    f N / ((N : ℝ)+1)) atTop (nhds (paretoMean f + 0)) at hlim
  rw [hmean, add_zero] at hlim
  apply hlim.congr
  intro N
  have he := pareto_partial_abel f (by simp [f, residue]) N
  have hj : arithmeticGeneratorCutoffFlux a m N =
      ∑ k ∈ Finset.range N, (f (k+1)-f k) / ((k : ℝ)+1) := by
    unfold arithmeticGeneratorCutoffFlux
    have hset : Finset.Icc 1 N = Finset.Ico 1 (N+1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp [arithmeticGeneratorJump, f, add_comm]
  rw [hj, he]
  ring
theorem arithmeticGeneratorLogFlux_proved : ArithmeticGeneratorLogFluxTarget := by
  intro a m ha hm
  exact ⟨fun N => arithmeticGeneratorCutoffFlux_eq_harmonic a m N ha hm, arithmeticGeneratorCutoffFlux_tendsto_log a m ha hm⟩
end RiemannResearch.RH.Pareto
