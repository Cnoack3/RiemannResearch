import RiemannResearch.Analysis.MontgomeryWeightedHilbertBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Infinite Montgomery–Vaughan mean squares on integer log frequencies

The repository proves the finite Montgomery–Vaughan inequality. Absolute
summability and a weighted coefficient square sum extend it to the infinite
Dirichlet series, with an error independent of the interval length. -/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.DirichletMeanSquare
open ZeroOrdinate

/-- Positive integer log frequencies start with n+1. The uniform-in-T
error retains the convergent weighted coefficient sum on the right. -/
theorem infinite_log_mean_square_le_midpoint {K : ℝ} (hK : Zeta23.MVDiag K)
    (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖)
    (hw : Summable fun n => (((n+1 : ℕ) : ℝ)+1/2)*‖a n‖^2) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t in (0 : ℝ)..T, ‖∑' n : ℕ, a n*phase (Real.log (n+1 : ℕ)) t‖^2) -
      T*∑' n : ℕ, ‖a n‖^2| ≤ (2*K)*∑' n : ℕ, (((n+1 : ℕ):ℝ)+1/2)*‖a n‖^2 := by
  classical
  let term := fun (n : ℕ) (t : ℝ) => a n*phase (Real.log (n+1 : ℕ)) t
  let P := fun (N : ℕ) (t : ℝ) => ∑ n ∈ Finset.range N, term n t
  have hnrm (n : ℕ) (t : ℝ) : ‖term n t‖ = ‖a n‖ := by simp [term,phase_norm]
  have hPS (t : ℝ) : Summable (fun n => term n t) := summable_norm_iff.mp
    (ha.congr fun n => (hnrm n t).symm)
  have hp (N : ℕ) (t : ℝ) : ‖P N t‖ ≤ ∑' n : ℕ, ‖a n‖ := by
    apply (norm_sum_le _ _).trans
    simp only [hnrm]
    exact ha.sum_le_tsum _ fun n _ => norm_nonneg _
  have hdiag : Summable (fun n => ‖a n‖^2) := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ hw
    intro n
    exact le_mul_of_one_le_left (sq_nonneg _) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hcont (N : ℕ) : Continuous (fun t => ‖P N t‖^2) := by
    apply Continuous.pow
    apply Continuous.norm
    dsimp [P,term,phase]
    fun_prop
  have hI : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..T, ‖P N t‖^2) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ‖∑' n : ℕ, term n t‖^2)) := by
    simp only [intervalIntegral.integral_of_le hT]
    have hi : IntegrableOn (fun _ : ℝ => (∑' n : ℕ, ‖a n‖)^2) (Ioc 0 T) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp intervalIntegrable_const
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (∑' n : ℕ, ‖a n‖)^2)
      (fun N => (hcont N).aestronglyMeasurable) hi
    · intro N
      exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hp N t) 2
    · exact Filter.Eventually.of_forall fun t => (hPS t).hasSum.tendsto_sum_nat.norm.pow 2
  have hfinite (N : ℕ) :
      |(∫ t in (0 : ℝ)..T, ‖P N t‖^2) - T*∑ n ∈ Finset.range N, ‖a n‖^2| ≤
        (2*K)*∑ n ∈ Finset.range N, (((n+1 : ℕ):ℝ)+1/2)*‖a n‖^2 := by
    let n := fun i : Fin N => i.val+1
    have hn (i : Fin N) : 1 ≤ n i := Nat.succ_pos _
    have hni : Function.Injective n := fun i j hij => Fin.ext (Nat.add_right_cancel hij)
    have hnr (i : Fin N) : (0 : ℝ) < n i := by exact_mod_cast hn i
    have hw' : Function.Injective (fun i : Fin N => Real.log (n i : ℝ)) := by
      intro i j hij
      apply hni
      exact_mod_cast Real.log_injOn_pos (mem_Ioi.mpr (hnr i)) (mem_Ioi.mpr (hnr j)) hij
    have he := abs_integral_norm_sq_sub_le_of_weightedHilbert hK (fun i : Fin N => a i.val)
      (fun i : Fin N => Real.log (n i : ℝ)) (fun i : Fin N => 1/((n i : ℝ)+1/2)) hw'
      (fun i => by have h := hnr i; positivity)
      (fun i j hij => midpoint_inv_le_abs_log_sub (hn i) (hn j)
        (fun eq => hij (hni eq))) 0 T
    simp only [sub_zero,div_div_eq_mul_div,div_one,polynomial,n] at he
    have hs (t : ℝ) : (∑ i : Fin N, a i.val*phase (Real.log (i.val+1 : ℕ)) t) = P N t :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => term i t) N
    have hd := Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖a i‖^2) N
    have hwm := Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖a i‖^2*(((i+1:ℕ):ℝ)+1/2)) N
    simp_rw [hs] at he
    rw [hd,hwm] at he
    apply he.trans_eq
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  apply le_of_tendsto_of_tendsto'
    ((hI.sub ((tendsto_const_nhds (x := T)).mul hdiag.hasSum.tendsto_sum_nat)).abs)
    ((tendsto_const_nhds (x := 2*K)).mul hw.hasSum.tendsto_sum_nat) hfinite

/-- Unconditional repository version, combining its checked Hilbert
constant 13 with the stronger midpoint spacing. -/
theorem infinite_log_mean_square_le (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖)
    (hw : Summable fun n => ((n + 1 : ℕ) : ℝ) * ‖a n‖ ^ 2) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t in (0 : ℝ)..T, ‖∑' n : ℕ, a n*phase (Real.log (n+1 : ℕ)) t‖^2) -
      T*∑' n : ℕ, ‖a n‖^2| ≤ 39*∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖a n‖ ^ 2 := by
  let w := fun n : ℕ => (((n+1 : ℕ):ℝ)+1/2)*‖a n‖^2
  have hm (n : ℕ) : w n ≤ (3/2)*(((n + 1 : ℕ) : ℝ) * ‖a n‖ ^ 2) := by
    dsimp only [w]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hwm : Summable w := Summable.of_nonneg_of_le
    (fun n => by dsimp [w]; positivity) hm (hw.mul_left (3/2))
  have hbound := infinite_log_mean_square_le_midpoint Zeta23.MV.mvDiag_thirteen a ha hwm hT
  have ht := hwm.tsum_le_tsum hm (hw.mul_left (3/2))
  rw [tsum_mul_left] at ht
  exact hbound.trans ((mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 2*13)).trans_eq
    (by ring))

end RiemannResearch.Analysis.DirichletMeanSquare
