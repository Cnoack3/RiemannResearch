import RiemannResearch.RH.MobiusResidualInfiniteDefects

/-!
# Escape of the canonical Möbius-defect reconstructions

Source: user-supplied RH_False_Canonical_Obstructions_and_Contradiction_Audit
(2026-09-19), Section 5, and the present independent continuation. No
mathematical novelty claim is made.

Finite Möbius inversion leaves one linear prefix error. The coefficient
Riesz vectors form a total dual dictionary independently of RH. Their
finite projections give an exact Cauchy--Schwarz obstruction and force
the actual residual reconstruction norms to tend to infinity under
the explicit hypothesis that Mathlib's RiemannHypothesis is false.

The cofinally bounded reconstruction implication is a conditional research
reduction. Its boundedness premise is open; no provider is asserted.
Multiplicity-sensitive Mellin rates are written proofs in the companion
continuation and are not formalized in this module.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Finite Möbius inversion leaves exactly one linear direction on a prefix. -/
theorem sequence_linear_on_prefix_of_mobius_zero (f : ThresholdHilbert) (N : ℕ)
    (hf : ∀ m : ℕ, 1 < m → m ≤ N → mobiusDifferenceCLM m f = 0) :
    ∀ n : ℕ, n ≤ N → hilbertSequence f n = (n : ℝ) * hilbertSequence f 1 := by
  have hstep (n : ℕ) (hn : n + 1 ≤ N) :
      hilbertSequence f (n + 1) - hilbertSequence f n = hilbertSequence f 1 := by
    have hi := sum_mobiusDifference (hilbertSequence f) (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hi
    rw [← hi]
    calc
      (∑ d ∈ (n + 1).divisors, mobiusDifference d (hilbertSequence f)) =
          ∑ d ∈ (n + 1).divisors, if d = 1 then hilbertSequence f 1 else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases h1 : d = 1
        · subst d
          simp [mobiusDifference]
        · have hp := Nat.pos_of_mem_divisors hd
          have hle : d ≤ N := (Nat.le_of_dvd (by omega)
            (Nat.dvd_of_mem_divisors hd)).trans hn
          rw [if_neg h1]
          simpa only [mobiusDifferenceCLM_apply] using hf d (by omega) hle
      _ = _ := by simp [Nat.mem_divisors]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    have hs := hstep n hn
    rw [ih (by omega)] at hs
    push_cast
    nlinarith

namespace CoefficientStabilization

/-- Ordered reconstruction agrees with its target on the first N+1 entries
up to one explicitly determined linear slope. -/
theorem coordinatePartialSum_prefix_linear (f : ThresholdHilbert) (N k : ℕ)
    (hk : k ≤ N + 1) :
    hilbertSequence (coordinatePartialSum f N - f) k =
      (k : ℝ) * hilbertSequence (coordinatePartialSum f N - f) 1 := by
  apply sequence_linear_on_prefix_of_mobius_zero _ (N + 1) _ k hk
  intro m hm hmN
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 2 := ⟨m - 2, by omega⟩
  have hc := coefficient_finite_sum N
    (fun i : Fin N => coefficientCLM (i.val + 2) f) ⟨j, by omega⟩
  change -mobiusDifferenceCLM (j + 2) (coordinatePartialSum f N) =
    -mobiusDifferenceCLM (j + 2) f at hc
  rw [map_sub]
  linarith

/-- Finite projection onto the Riesz vectors of the coefficient observations. -/
def dualCoordinateProjection (f : ThresholdHilbert) (N : ℕ) : ThresholdHilbert :=
  (walkSpan (fun i : ℕ => mobiusRieszHilbert (i + 2)) id N).starProjection f

/-- The dual dictionary is total, by joint separation of the Möbius coordinates.
This is not a density assertion about the residue dictionary. -/
theorem dualCoordinateProjection_tendsto (f : ThresholdHilbert) :
    Tendsto (dualCoordinateProjection f) atTop (𝓝 f) := by
  let v : ℕ → ThresholdHilbert := fun i => mobiusRieszHilbert (i + 2)
  let K := dictionaryClosure v
  have hz : f - K.starProjection f = 0 := by
    apply eq_zero_of_mobius_coordinates_zero
    intro m hm
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, m = i + 2 := ⟨m - 2, by omega⟩
    rw [← mobiusRieszHilbert_inner]
    apply (K.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal f)
    exact (Submodule.span ℝ (Set.range v)).le_topologicalClosure
      (Submodule.subset_span ⟨i, rfl⟩)
  have he : K.starProjection f = f := (sub_eq_zero.mp hz).symm
  have ht := walkProjection_tendsto v id Function.surjective_id f
  change Tendsto (dualCoordinateProjection f) atTop (𝓝 (K.starProjection f)) at ht
  rwa [he] at ht

/-- Exact observation agreement gives orthogonality to the finite dual span. -/
theorem coordinatePartialSum_dual_orthogonal (f : ThresholdHilbert) (N : ℕ) :
    inner ℝ (dualCoordinateProjection f N) (f - coordinatePartialSum f N) = 0 := by
  have hz (y : ThresholdHilbert)
      (hy : y ∈ walkSpan (fun i : ℕ => mobiusRieszHilbert (i + 2)) id N) :
      inner ℝ y (f - coordinatePartialSum f N) = 0 := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [mobiusRieszHilbert_inner, map_sub]
      have hc := coefficient_finite_sum N
        (fun j : Fin N => coefficientCLM (j.val + 2) f) i
      change -mobiusDifferenceCLM (i.val + 2) (coordinatePartialSum f N) =
        -mobiusDifferenceCLM (i.val + 2) f at hc
      change mobiusDifferenceCLM (i.val + 2) f -
        mobiusDifferenceCLM (i.val + 2) (coordinatePartialSum f N) = 0
      linarith
    | zero => simp
    | add x y hx hy hix hiy => simp [inner_add_left, hix, hiy]
    | smul c x hx hix => simp [inner_smul_left, hix]
  exact hz _ (Submodule.starProjection_apply_mem _ _)

/-- An exact pairing identity for the actual orthogonal residual. -/
theorem defect_dual_error_pairing (N : ℕ) :
    inner ℝ (limitResidual - coordinatePartialSum limitResidual N)
      (limitResidual - dualCoordinateProjection limitResidual N) = ‖limitResidual‖ ^ 2 := by
  have hw : inner ℝ (coordinatePartialSum limitResidual N) limitResidual = 0 :=
    (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
      (coordinatePartialSum_mem limitResidual N)
  have hd := coordinatePartialSum_dual_orthogonal limitResidual N
  rw [real_inner_comm] at hd
  rw [inner_sub_right, hd, sub_zero, inner_sub_left, hw, sub_zero,
    real_inner_self_eq_norm_sq]

/-- Cauchy--Schwarz with the actual shrinking dual error.
No upper bound on the reconstruction is assumed or supplied. -/
theorem defect_reconstruction_dual_bound (N : ℕ) :
    ‖limitResidual‖ ^ 2 ≤
      (‖limitResidual‖ + ‖coordinatePartialSum limitResidual N‖) *
        ‖limitResidual - dualCoordinateProjection limitResidual N‖ := by
  have hc := norm_inner_le_norm (𝕜 := ℝ)
    (limitResidual - coordinatePartialSum limitResidual N)
    (limitResidual - dualCoordinateProjection limitResidual N)
  rw [defect_dual_error_pairing, Real.norm_of_nonneg (sq_nonneg _)] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (norm_sub_le _ _) (norm_nonneg _))

/-- Pythagoras keeps the complete reconstruction norm in the denominator. -/
theorem defect_reconstruction_dual_bound_sq (N : ℕ) :
    ‖limitResidual‖ ^ 4 ≤
      (‖limitResidual‖ ^ 2 + ‖coordinatePartialSum limitResidual N‖ ^ 2) *
        ‖limitResidual - dualCoordinateProjection limitResidual N‖ ^ 2 := by
  have hw : inner ℝ limitResidual (coordinatePartialSum limitResidual N) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
      (coordinatePartialSum_mem limitResidual N)
  have hn : ‖limitResidual - coordinatePartialSum limitResidual N‖ ^ 2 =
      ‖limitResidual‖ ^ 2 + ‖coordinatePartialSum limitResidual N‖ ^ 2 := by
    rw [norm_sub_sq_real, hw]
    ring
  have hc := norm_inner_le_norm (𝕜 := ℝ)
    (limitResidual - coordinatePartialSum limitResidual N)
    (limitResidual - dualCoordinateProjection limitResidual N)
  rw [defect_dual_error_pairing, Real.norm_of_nonneg (sq_nonneg _)] at hc
  have hs := mul_self_le_mul_self (sq_nonneg ‖limitResidual‖) hc
  simp only [← pow_two] at hs
  rw [mul_pow, hn] at hs
  nlinarith only [hs]

/-- Failure of RH forces the ordered reconstruction norms to tend to infinity,
not merely to fail to converge. -/
theorem not_RH_defect_norms_tendsto_atTop (hRH : ¬ RiemannHypothesis) :
    Tendsto (fun N => ‖coordinatePartialSum limitResidual N‖) atTop atTop := by
  have hr : limitResidual ≠ 0 := by
    intro hz
    exact hRH (riemannHypothesis_of_limitCoefficients
      (limitCoefficients_eq_mobius_iff_residual_zero.mpr hz))
  have hp : 0 < ‖limitResidual‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hr)
  have ht : Tendsto
      (fun N => ‖limitResidual - dualCoordinateProjection limitResidual N‖)
      atTop (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds (x := limitResidual)).sub
        (dualCoordinateProjection_tendsto limitResidual)).norm
  apply tendsto_atTop.mpr
  intro b
  have hden : 0 < ‖limitResidual‖ + |b| + 1 := by positivity
  have he := ht.eventually (gt_mem_nhds (div_pos hp hden))
  filter_upwards [he] with N hN
  have hs := (lt_div_iff₀ hden).mp hN
  have hb := defect_reconstruction_dual_bound N
  have hnonneg := norm_nonneg
    (limitResidual - dualCoordinateProjection limitResidual N)
  by_contra! hn
  have hh : ‖coordinatePartialSum limitResidual N‖ ≤ |b| := hn.le.trans (le_abs_self b)
  have hm := mul_nonneg (sub_nonneg.mpr hh) hnonneg
  nlinarith

/-- A bounded cofinal collection of the actual defect reconstructions would
already force RH. The boundedness premise remains an open arithmetic input. -/
theorem riemannHypothesis_of_cofinally_bounded_defect_reconstruction
    (h : ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ‖coordinatePartialSum limitResidual n‖ ≤ C) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨C, hC⟩ := h
  have he := (tendsto_atTop.mp (not_RH_defect_norms_tendsto_atTop hRH)) (C + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  obtain ⟨n, hNn, hn⟩ := hC N
  have hh := hN n hNn
  linarith

end CoefficientStabilization
end RiemannResearch.RH.Pareto
