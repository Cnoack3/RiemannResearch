import RiemannResearch.RH.MultiRangeFiniteMinimum
import RiemannResearch.RH.MultiRangeOptimizerConvergence

/-! Finite-horizon positivity for the actual anchored arithmetic dictionary.
Source: Section 7 of RH_Multi_Range_Divisor_Corrections_2026-09-18.md.
Möbius charge extraction proves nondegeneracy once the horizon reaches every
non-anchor divisor. No asymptotic conditioning estimate is used. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro ArithmeticCumulative
open Analysis.FiniteSignedQuadratic

theorem prefixMeanGram_quadratic {D : ℕ} (U : Fin D → ℕ → ℝ)
    (x : Fin D → ℝ) (N : ℕ) :
    quadratic (prefixMeanGram U N) x =
      conditionalMeanPrefix (fun n => ∑ i, x i * U i n) N := by
  unfold quadratic prefixMeanGram conditionalMeanPrefixInner conditionalMeanPrefix
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [cesaro_finsetCombination, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Zero prefix energy forces each positive conditional mean in that prefix to vanish. -/
theorem conditionalMeanPrefix_eq_zero_means (F : ℕ → ℝ) (N : ℕ)
    (hz : conditionalMeanPrefix F N = 0) (t : ℕ) (ht : 0 < t) (htN : t ≤ N) :
    cesaro F t = 0 := by
  have hterm : conditionalWeight (t-1) * (cesaro F (t-1+1))^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.range N) =>
        mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))).mp hz
      (t-1) (Finset.mem_range.mpr (by omega))
  rw [Nat.sub_add_cancel ht] at hterm
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (conditionalWeight_pos _)))

theorem anchor_prefix_energy_pos {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (N : ℕ) (hN : ∀ i, d i ≤ N) (x : Fin D → ℝ) (hx : x ≠ 0) :
    0 < conditionalMeanPrefix (anchorSynthesis A d x) N := by
  have hn : 0 ≤ conditionalMeanPrefix (anchorSynthesis A d x) N :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (conditionalWeight_pos _).le (sq_nonneg _))
  by_contra hp
  have hz : conditionalMeanPrefix (anchorSynthesis A d x) N = 0 := le_antisymm (le_of_not_gt hp) hn
  have hmean (t : ℕ) (htN : t ≤ N) : cesaro (anchorSynthesis A d x) t = 0 := by
    by_cases ht : t = 0
    · simp [ht, cesaro]
    · exact conditionalMeanPrefix_eq_zero_means _ N hz t (by omega) htN
  have hseq (t : ℕ) (htN : t ≤ N) : anchorSynthesis A d x t = 0 := by
    cases t with
    | zero => simp [anchorSynthesis,divisorAnchorDirection,residueFraction]
    | succ t => rw [cesaro_recover (anchorSynthesis A d x) t, hmean (t+1) htN, hmean t (by omega)]; ring
  apply hx
  funext i
  have he := anchorSynthesis_charge A d x hd hinj i
  have hm : mobiusDifference (d i) (anchorSynthesis A d x) = 0 := by
    unfold mobiusDifference
    apply Finset.sum_eq_zero
    intro k hk
    have hkN := (Nat.le_of_dvd (by have := (hd i).1; omega)
      (Nat.dvd_of_mem_divisors hk)).trans (hN i)
    rw [hseq k hkN, hseq (k-1) (by omega)]
    ring
  exact he.symm.trans hm

/-- The explicit finite horizon suffices for true positive definiteness. -/
theorem anchor_prefixGram_posDef {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (N : ℕ) (hN : ∀ i, d i ≤ N) :
    (prefixMeanGram (fun i => divisorAnchorDirection A (d i)) N).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,prefixMeanGram,conditionalMeanPrefixInner]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · intro x hx
    have he := prefixMeanGram_quadratic (fun i => divisorAnchorDirection A (d i)) x N
    rw [quadratic_mulVec] at he
    change 0 < ∑ i, x i * (prefixMeanGram (fun i => divisorAnchorDirection A (d i)) N).mulVec x i
    rw [he]
    exact anchor_prefix_energy_pos A d hd hinj N hN x hx

end RiemannResearch.RH.Pareto
