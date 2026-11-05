import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.ZetaTwoResolvent
import RiemannResearch.RH.QParityBasis
import RiemannResearch.RH.QConductorEstimates
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Continuation of shifted tests paired with the squarefree Schur witness

Bagchi (2006), proof of Theorem 2 and Remark 4, motivates continuation of
a damped squarefree expansion. The analytic estimates below are hypotheses:
normal convergence is local in the open domain; the separate Perron bound is
needed only on a sequence approaching the boundary. The physical coordinate
zero has weight zero.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.RH.MertensShiftedPairing

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeDisplacementRigidity

/-- Physical complex measure of the real Schur witness. -/
def witnessCharge (n : ℕ) : ℂ :=
  ((positiveQWeight n * qSequence witness n : ℝ) : ℂ)

/-- Orthogonality of the actual witness kills each column in the open
half-plane where the damped squarefree series can be rearranged. -/
theorem witnessCharge_atom (i : ℕ) :
    ∑' n, witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ) = 0 := by
  have hi : squarefreeAtom i ∈ ZetaTwoOptimizerStage.closure := by
    change squarefreeAtom i ∈ (Submodule.span ℝ (Set.range squarefreeAtom)).topologicalClosure
    apply Submodule.le_topologicalClosure
    exact Submodule.subset_span (Set.mem_range_self i)
  have hh : inner ℝ (squarefreeAtom i) witness = 0 :=
    Submodule.inner_right_of_mem_orthogonal hi witness_mem_orthogonal
  rw [qInner_weighted] at hh
  calc
    _ = ((∑' n, positiveQWeight n * qSequence (squarefreeAtom i) n * qSequence witness n : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro n
      simp only [witnessCharge, Complex.ofReal_mul]
      ring
    _ = 0 := by rw [hh]; simp

/-- Every absolutely summable coefficient row can be paired in either order
with the actual witness: its physical mass is finite and all residue atoms
are bounded by one, including the zero columns. -/
theorem witnessCharge_product_summable (c : ℕ → ℂ) (hc : Summable (fun i => ‖c i‖)) :
    Summable (Function.uncurry (fun i n : ℕ =>
      c i * (witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ)))) := by
  have hb : Summable (fun n => ‖witnessCharge n‖) := by
    simpa only [witnessCharge, Complex.norm_real, Real.norm_eq_abs] using
      (qWeighted_summable witness).abs
  have ha (i n : ℕ) : ‖(qSequence (squarefreeAtom i) n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hi : Squarefree (i + 2)
    · simpa only [squarefreeAtom, if_pos hi] using qResidue_physical_abs_le_one (i + 2) n
    · simp only [squarefreeAtom, if_neg hi]
      change |qSequenceLinear (0 : QHilbert) n| ≤ 1
      simp
  have hprod : Summable (fun p : ℕ × ℕ => ‖c p.1‖ * ‖witnessCharge p.2‖) :=
    hc.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hprod
  rintro ⟨i, n⟩
  change ‖c i * (witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ))‖ ≤ _
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right (norm_nonneg _) (ha i n)) (norm_nonneg _)

/-- Absolute product summability on the seed region justifies the
interchange of physical sites and squarefree conductors. -/
theorem witnessCharge_series_zero (F c : ℕ → ℂ)
    (hexp : ∀ n, F n = ∑' i, c i * (qSequence (squarefreeAtom i) n : ℂ))
    (hc : Summable (fun i => ‖c i‖)) :
    ∑' n, witnessCharge n * F n = 0 := by
  calc
    _ = ∑' n, ∑' i, c i * (witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ)) := by
      apply tsum_congr
      intro n
      rw [hexp n, ← tsum_mul_left]
      apply tsum_congr
      intro i
      ring
    _ = ∑' i, ∑' n, c i * (witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ)) :=
      (witnessCharge_product_summable c hc).tsum_comm
    _ = 0 := by simp_rw [tsum_mul_left, witnessCharge_atom, mul_zero]; simp

/-- A real boundary estimate suffices for the final dominated-convergence
step. Normal convergence on the complex interior can use unrelated local
majorants. The seed is an actual legal expansion with absolutely summable coefficients. -/
theorem riemannHypothesis_of_shifted_witness_tests
    (U : Set ℂ) (z₀ : ℂ) (x : ℕ → ℂ) (F : ℕ → ℂ → ℂ)
    (hconn : IsPreconnected U) (hz₀ : z₀ ∈ U) (hx : ∀ j, x j ∈ U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hlocal : ∀ z ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∃ B : ℕ → ℝ, Summable B ∧ ∀ n w, w ∈ V → ‖witnessCharge n * F n w‖ ≤ B n)
    (hseed : ∀ᶠ z in 𝓝 z₀, ∃ c : ℕ → ℂ,
      (∀ n, F n z = ∑' i, c i * (qSequence (squarefreeAtom i) n : ℂ)) ∧
      Summable (fun i => ‖c i‖))
    (hterm : ∀ n, Tendsto (fun j => witnessCharge n * F n (x j)) atTop (𝓝 (witnessCharge n)))
    (G : ℕ → ℝ) (hG : Summable G)
    (hboundary : ∀ᶠ j in atTop, ∀ n, ‖witnessCharge n * F n (x j)‖ ≤ G n) :
    RiemannHypothesis := by
  let L (z : ℂ) := ∑' n, witnessCharge n * F n z
  have hA : AnalyticOnNhd ℂ L U := by
    intro z hz
    obtain ⟨V, hV, hzV, hVU, B, hB, hb⟩ := hlocal z hz
    have hd (n : ℕ) : DifferentiableOn ℂ (fun w => witnessCharge n * F n w) V := by
      apply DifferentiableOn.mul _ ((hF n).mono hVU)
      fun_prop
    exact ((Complex.differentiableOn_tsum_of_summable_norm hB hd hV hb).analyticOnNhd hV) z hzV
  have hvan : L =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hseed] with z hz
    obtain ⟨c, he, hs⟩ := hz
    exact witnessCharge_series_zero (fun n => F n z) c he hs
  have hzU := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ hvan
  have hT := tendsto_tsum_of_dominated_convergence hG hterm hboundary
  have he : (fun j => ∑' n, witnessCharge n * F n (x j)) =ᶠ[atTop] (fun _ => (0:ℂ)) :=
    Eventually.of_forall (fun j => hzU (hx j))
  have hzero : ∑' n, witnessCharge n = 0 := tendsto_nhds_unique (hT.congr' he) tendsto_const_nhds
  have hcomplex : ((∑' n, positiveQWeight n * qSequence witness n : ℝ) : ℂ) = 0 := by
    simpa only [Complex.ofReal_tsum, witnessCharge] using hzero
  have hreal : (∑' n, positiveQWeight n * qSequence witness n) = 0 := by exact_mod_cast hcomplex
  rw [ZetaTwoResolvent.targetCharge_tsum, real_inner_comm] at hreal
  have hr := residual_eq_zero_of_witness_mean_zero hreal
  have hmem : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hmem)

end RiemannResearch.RH.MertensShiftedPairing
