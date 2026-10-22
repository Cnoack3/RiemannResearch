import RiemannResearch.RH.IntegerDPPGramDeterminant
import RiemannResearch.RH.IntegerDPPTrace
import RiemannResearch.RH.ExactHeadResidualTail
import Mathlib.Topology.Instances.Matrix

/-!
# Distribution of the rightmost arithmetic DPP point

Source: the user-provided DPP/Fredholm conversation, 20 September 2026.
The event that every occupied physical site is at most M is the absence of
occupied Lean coordinates i ≥ M. Its probability is the determinant of the
complete Gram contribution from the first M coordinates divided by the full
Pareto Gram determinant. The proof uses continuity from above of the actual
probability law and convergence of complete scalar inner-product sums.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Classical Topology

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

theorem windowFeatures_apply (N m : ℕ) (e : Fin m → ℕ) (i : Fin m) (j : Fin N) :
    windowFeatures N m e i j = residueAtom j.val (e i) := by
  change inner ℝ (residueAtom j.val) (countingBasis (e i)) = _
  rw [real_inner_comm, countingBasis_inner_vector]

theorem windowGram_apply (N m : ℕ) (e : Fin m → ℕ) (i j : Fin N) :
    windowGram N m e i j =
      ∑ k : Fin m, residueAtom i.val (e k) * residueAtom j.val (e k) := by
  simp only [windowGram, Matrix.mul_apply, Matrix.transpose_apply, windowFeatures_apply]

theorem windowGram_tail_tendsto (N M : ℕ) :
    Tendsto (fun m => windowGram N m (fun i : Fin m => i.val + M)) atTop
      (𝓝 (fullGram N - windowGram N M (fun i : Fin M => i.val))) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  let f : ℕ → ℝ := fun k => residueAtom i.val k * residueAtom j.val k
  have hs : Summable f := hilbert_coordinate_mul_summable _ _
  have hshift : Summable (fun k => f (k + M)) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have htotal : (∑' k, f k) = fullGram N i j := by
    simp only [fullGram, gramMatrix, lp.inner_eq_tsum, RCLike.inner_apply,
      conj_trivial, f, mul_comm]
  have hprefix : (∑ k ∈ Finset.range M, f k) =
      windowGram N M (fun i : Fin M => i.val) i j := by
    rw [windowGram_apply]
    exact (Fin.sum_univ_eq_sum_range f M).symm
  have hsum : (∑' k, f (k + M)) =
      (fullGram N - windowGram N M (fun i : Fin M => i.val)) i j := by
    have h := hs.sum_add_tsum_nat_add M
    rw [htotal, hprefix] at h
    simp only [Matrix.sub_apply]
    linarith
  have h := hshift.hasSum.tendsto_sum_nat
  rw [hsum] at h
  convert h using 1
  funext m
  rw [windowGram_apply]
  exact Fin.sum_univ_eq_sum_range (fun k => f (k + M)) m

/-- Probability that the maximum physical site is at most M. This event also
handles the empty rank-zero process without choosing a maximum of the empty set. -/
theorem integerLaw_maximum_gram_determinant (N M : ℕ) :
    (integerLaw N).real {x | ∀ i : ℕ, M ≤ i → x i = false} =
      (windowGram N M (fun i : Fin M => i.val)).det / (fullGram N).det := by
  let e : (m : ℕ) → (Fin m ↪ ℕ) := fun m =>
    ⟨fun i => i.val + M, fun i j h => Fin.ext (Nat.add_right_cancel h)⟩
  let A : ℕ → Set (ℕ → Bool) := fun m => {x | ∀ i : Fin m, x (e m i) = false}
  have hm (m : ℕ) : MeasurableSet (A m) := by
    have hsite (i : Fin m) : MeasurableSet {x : ℕ → Bool | x (e m i) = false} := by
      exact (measurableSet_singleton false).preimage (measurable_pi_apply (e m i))
    simpa only [A, Set.ofPred_forall] using MeasurableSet.iInter hsite
  have hmono : Antitone A := by
    intro m n hmn x hx i
    exact hx ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
  have hA : (⋂ m, A m) = {x | ∀ i : ℕ, M ≤ i → x i = false} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hx i hi
      have h := hx (i - M + 1) ⟨i - M, by omega⟩
      change x ((i - M) + M) = false at h
      simpa only [Nat.sub_add_cancel hi] using h
    · intro hx m i
      change x (i.val + M) = false
      exact hx (i.val + M) (by omega)
  have hprob : Tendsto (fun m => (integerLaw N).real (A m)) atTop
      (𝓝 ((integerLaw N).real {x | ∀ i : ℕ, M ≤ i → x i = false})) := by
    have h := tendsto_measure_iInter_atTop (μ := integerLaw N)
      (fun m => (hm m).nullMeasurableSet)
      hmono ⟨0, measure_ne_top (integerLaw N) (A 0)⟩
    rw [hA] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top (integerLaw N)
      {x | ∀ i : ℕ, M ≤ i → x i = false})).comp h
  have hmat := (tendsto_const_nhds (x := fullGram N)).sub (windowGram_tail_tendsto N M)
  have he : fullGram N -
      (fullGram N - windowGram N M (fun i : Fin M => i.val)) =
      windowGram N M (fun i : Fin M => i.val) := by abel
  rw [he] at hmat
  have hdet := (continuous_id.matrix_det.tendsto _).comp hmat
  have hratio := hdet.div_const ((fullGram N).det)
  have hprob' : Tendsto (fun m =>
      (fullGram N - windowGram N m (fun i : Fin m => i.val + M)).det /
        (fullGram N).det) atTop
      (𝓝 ((integerLaw N).real {x | ∀ i : ℕ, M ≤ i → x i = false})) := by
    convert hprob using 1
    funext m
    exact (integerLaw_window_gram_determinant N m (e m)).symm
  exact tendsto_nhds_unique hprob' hratio

end RiemannResearch.RH.Pareto.IntegerDPP
