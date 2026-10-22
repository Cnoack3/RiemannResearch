import RiemannResearch.RH.IntegerDPPHistoricalTargets
import RiemannResearch.Analysis.ContinuousBiorthogonalDeletion
import RiemannResearch.Analysis.FiniteHilbertGramMatrix

/-!
# Strict positivity of every finite arithmetic occupation window

Source: user-provided fixed-window spectral-saturation research target,
21 September 2026. The proof uses triangular integer dilations of the
actual residue generator to construct exact finite-head interpolation.

The limiting window compression is positive definite and every finite
occupation event has positive probability. This supplies the provider for
HistoricalTargets.PositiveFiniteHead. No uniform lower bound as the window
grows, spectral saturation at one, or RH is asserted.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology Classical BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative

private def triangularResidue (k : ℕ) : ThresholdHilbert :=
  hilbertDilation (k + 1) (by omega) (residueAtom 0)

private theorem triangularResidue_mem (k : ℕ) :
    triangularResidue k ∈ closedSpace := by
  apply closedSpace_dilation
  exact normalizedResidue_mem_closedSpace 2 (by omega)

private theorem triangularResidue_before (k n : ℕ) (h : n < k + 1) :
    hilbertSequence (triangularResidue k) n = 0 := by
  rw [triangularResidue, hilbertDilation_sequence, residueAtom,
    normalizedResidueHilbert_sequence]
  simp [dilation, residueFraction, Nat.div_eq_of_lt h]

private theorem triangularResidue_at (k : ℕ) :
    hilbertSequence (triangularResidue k) (k + 1) = (k + 1 : ℕ) / 2 := by
  rw [triangularResidue, hilbertDilation_sequence, residueAtom,
    normalizedResidueHilbert_sequence]
  simp [dilation, residueFraction, Nat.div_self (Nat.succ_pos k)] <;> ring

/-- Exact interpolation in the genuine residue closure, without any norm bound. -/
theorem exists_closedSpace_head_interpolant (N : ℕ) (f : ThresholdHilbert) :
    ∃ g ∈ closedSpace, ∀ n, 0 < n → n ≤ N →
      hilbertSequence g n = hilbertSequence f n := by
  induction N with
  | zero => exact ⟨0, Submodule.zero_mem _, by intro n hn hnN; omega⟩
  | succ N ih =>
    obtain ⟨g, hg, hhead⟩ := ih
    let c : ℝ := (hilbertSequence f (N + 1) - hilbertSequence g (N + 1)) /
      ((N + 1 : ℕ) / 2 : ℝ)
    refine ⟨g + c • triangularResidue N,
      closedSpace.add_mem hg (closedSpace.smul_mem c (triangularResidue_mem N)), ?_⟩
    intro n hn hnN
    change hilbertSequenceLinear (g + c • triangularResidue N) n = _
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change hilbertSequence g n + c * hilbertSequence (triangularResidue N) n = _
    by_cases he : n = N + 1
    · subst n
      rw [triangularResidue_at]
      have hne : ((N + 1 : ℕ) / 2 : ℝ) ≠ 0 := by positivity
      dsimp [c]
      rw [div_mul_cancel₀ _ hne]
      ring
    · rw [triangularResidue_before N n (by omega), mul_zero, add_zero]
      exact hhead n hn (by omega)

private theorem inner_closedSpace_projection_coordinate (g : ThresholdHilbert)
    (hg : g ∈ closedSpace) (n : ℕ) :
    inner ℝ g (closedSpace.starProjection (countingBasis n)) = g n := by
  have ho : inner ℝ g
      (countingBasis n - closedSpace.starProjection (countingBasis n)) = 0 :=
    (closedSpace.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal (countingBasis n)) _ hg
  have he : inner ℝ g (countingBasis n) = g n := by
    rw [real_inner_comm]
    simp [countingBasis, lp.inner_single_left]
  rw [inner_sub_right, he] at ho
  linarith

/-- The projected coordinate vectors of every finite window are independent. -/
theorem limitingWindow_projected_basis_independent (m : ℕ) (e : Fin m ↪ ℕ) :
    LinearIndependent ℝ (fun i => closedSpace.starProjection (countingBasis (e i))) := by
  let M : ℕ := ∑ i : Fin m, (e i + 1)
  have heM (i : Fin m) : e i + 1 ≤ M :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (e j + 1)) (Finset.mem_univ i)
  choose g hg hhead using
    (fun j : Fin m => exists_closedSpace_head_interpolant M (countingBasis (e j)))
  apply RiemannResearch.Analysis.continuous_biorthogonal_linearIndependent
    (fun i => closedSpace.starProjection (countingBasis (e i)))
    (fun j => innerSL ℝ (g j))
  intro j i
  change inner ℝ (g j) (closedSpace.starProjection (countingBasis (e i))) = _
  rw [inner_closedSpace_projection_coordinate (g j) (hg j) (e i)]
  have hcoord := hhead j (e i + 1) (by omega) (heM i)
  simp only [hilbertSequence_succ] at hcoord
  have hs : Real.sqrt (paretoWeight (e i)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos (e i)))
  have hc : (g j) (e i) = countingBasis (e j) (e i) := by
    apply (div_left_inj' hs).mp
    exact hcoord
  rw [hc]
  by_cases hji : j = i
  · subst j
    simp [countingBasis]
  · have hne : e i ≠ e j := by intro h; exact hji (e.injective h).symm
    simp [countingBasis, hji, hne]

/-- Every finite compression is strictly positive definite unconditionally. -/
theorem limitingKernel_window_posDef (m : ℕ) (e : Fin m ↪ ℕ) :
    (Matrix.of (fun i j => limitingKernel (e i) (e j))).PosDef := by
  exact RiemannResearch.Analysis.FiniteHilbertGram.gramMatrix_posDef
    (limitingWindow_projected_basis_independent m e)

theorem limitingKernel_window_det_pos (m : ℕ) (e : Fin m ↪ ℕ) :
    0 < (Matrix.of (fun i j => limitingKernel (e i) (e j))).det :=
  (limitingKernel_window_posDef m e).det_pos

/-- Every prescribed finite set has strictly positive occupation probability. -/
theorem limitingLaw_window_occupation_pos (m : ℕ) (e : Fin m ↪ ℕ) :
    0 < limitingLaw.real {x | ∀ i, x (e i) = true} := by
  have h := limitingLaw_isDPP.correlation m e
  change limitingLaw.real {x | ∀ i, x (e i) = true} = _ at h
  rw [h]
  exact limitingKernel_window_det_pos m e

/-- Discharges the previously explicit historical PositiveFiniteHead target. -/
theorem positiveFiniteHead : HistoricalTargets.PositiveFiniteHead := by
  intro m
  have he : {x : ℕ → Bool | ∀ n < m, x n = true} =
      {x | ∀ i : Fin m, x ((prefixEmbedding m) i) = true} := by
    ext x
    constructor
    · intro h i
      exact h i.val i.isLt
    · intro h n hn
      exact h ⟨n, hn⟩
  change 0 < limitingLaw.real {x | ∀ n < m, x n = true}
  rw [he]
  exact limitingLaw_window_occupation_pos m (prefixEmbedding m)

end RiemannResearch.RH.Pareto.IntegerDPP
