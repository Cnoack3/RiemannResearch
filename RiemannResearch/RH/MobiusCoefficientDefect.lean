import RiemannResearch.RH.ResidueOrthonormalCoordinates
import RiemannResearch.Analysis.WeakConvergenceDenseTests
/-!
# Rigidity and Gram-energy targets for the Möbius coefficient defect

Source: user-provided "RH_Eight_Ranked_Research_Candidates_2026-09-20.pdf",
Candidate 4 (Section 6), for the arithmetic coefficient target and the
continuous Möbius coordinates. The extensions below use standard Hilbert-space
duality and bounded weak convergence; their proofs are developed here.
No mathematical novelty is claimed.

The index i represents physical conductor i+2. The defect is the actual
limiting coefficient plus mu(i+2), not a finite-stage or numerical surrogate.

Established: coefficient uniqueness and reconstruction whenever the residue
series is summable; totality of the Möbius Riesz tests; bounded-coordinate weak
convergence; and divergence of coefficient truncations of every nonzero
orthogonal vector. In particular, not RH forces infinitely many arithmetic
coefficient defects and unbounded, indeed divergent, defect truncation norms.

CONDITIONAL RESEARCH REDUCTIONS: eventual Möbius identification, weighted
absolute summability of the defect, and a cofinal bound on its complete signed
Gram energy each imply RH. Their arithmetic hypotheses remain OPEN.
Unconditional convergence of each fixed Gram-Schmidt coefficient series does
not imply any of these conductor-wise conditions.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- The Möbius Riesz vectors at conductors at least two have dense span in H.
This is totality of the dual tests, not density of the residue atoms. -/
theorem mobiusRiesz_total :
    (Submodule.span ℝ (Set.range (fun i => mobiusRieszHilbert (i + 2)))).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply eq_bot_iff.mpr
  intro f hf
  have hz : f = 0 := by
    apply eq_zero_of_mobius_coordinates_zero
    intro m hm
    rw [← mobiusRieszHilbert_inner]
    apply (Submodule.mem_orthogonal _ _).mp hf
    exact Submodule.subset_span ⟨m - 2, congrArg mobiusRieszHilbert (by omega)⟩
  simp [hz]

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ArithmeticCumulative

/-- The continuous residue coefficients jointly separate all Hilbert vectors. -/
theorem coefficientCLM_ext (f g : ThresholdHilbert)
    (h : ∀ i : ℕ, coefficientCLM (i + 2) f = coefficientCLM (i + 2) g) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mobius_coordinates_zero
  intro m hm
  have hi := h (m - 2)
  have he : m - 2 + 2 = m := by omega
  rw [he] at hi
  change -mobiusDifferenceCLM m f = -mobiusDifferenceCLM m g at hi
  rw [map_sub]
  linarith

/-- A convergent residue synthesis reconstructs its vector by coefficient uniqueness. -/
theorem coefficient_tsum_reconstruction (f : ThresholdHilbert)
    (hs : Summable (fun i => coefficientCLM (i + 2) f • residueAtom i)) :
    (∑' i, coefficientCLM (i + 2) f • residueAtom i) = f := by
  apply coefficientCLM_ext
  intro i
  rw [(coefficientCLM (i + 2)).map_tsum hs]
  simp [map_smul, coefficientCLM_biorthogonal]

/-- Residue-series summability supplies closed-span membership. -/
theorem mem_closedSpace_of_summable_coefficients (f : ThresholdHilbert)
    (hs : Summable (fun i => coefficientCLM (i + 2) f • residueAtom i)) :
    f ∈ closedSpace := by
  rw [← coefficient_tsum_reconstruction f hs]
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs.hasSum
  apply Filter.Eventually.of_forall
  intro s
  apply closedSpace.sum_mem
  intro i hi
  apply closedSpace.smul_mem
  exact subset_closure (Submodule.subset_span ⟨i, rfl⟩)

/-- The orthogonal residual cannot have a nonzero summable residue synthesis. -/
theorem residual_zero_of_summable_coefficients
    (hs : Summable (fun i => coefficientCLM (i + 2) limitResidual • residueAtom i)) :
    limitResidual = 0 := by
  have hm := mem_closedSpace_of_summable_coefficients limitResidual hs
  have ho := (closedSpace.mem_orthogonal limitResidual).mp limitResidual_mem_orthogonal
    limitResidual hm
  exact inner_self_eq_zero.mp ho


/-- The signed defect at conductor i+2: c_infinity,i+2 + mu(i+2). -/
def coefficientDefect (i : ℕ) : ℝ :=
  limitCoefficient (i + 2) + (ArithmeticFunction.moebius (i + 2) : ℝ)

/-- The sign connecting the arithmetic defect to the residual's continuous coordinate. -/
theorem coefficientDefect_eq_neg_residual_coefficient (i : ℕ) :
    coefficientDefect i = -coefficientCLM (i + 2) limitResidual := by
  rw [coefficientDefect, limitCoefficient_eq_residual _ (by omega)]
  simp [coefficientCLM]

/-- Summability here is a substantive saturation condition, not automatic. -/
theorem defect_series_summable_iff_residual_zero :
    Summable (fun i => coefficientDefect i • residueAtom i) ↔ limitResidual = 0 := by
  constructor
  · intro hs
    apply residual_zero_of_summable_coefficients
    simpa only [coefficientDefect_eq_neg_residual_coefficient, neg_smul, neg_neg] using hs.neg
  · intro hr
    simp [coefficientDefect_eq_neg_residual_coefficient, hr]

/-- Finitely many exceptional conductors are harmless; eventual identification suffices. -/
theorem riemannHypothesis_of_eventual_mobius
    (h : ∀ᶠ i in atTop, limitCoefficient (i + 2) =
      -(ArithmeticFunction.moebius (i + 2) : ℝ)) : RiemannHypothesis := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hs : Summable (fun i => coefficientDefect i • residueAtom i) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro i hi
    have hiN : N ≤ i := by simpa using hi
    simp [coefficientDefect, hN i hiN]
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr (defect_series_summable_iff_residual_zero.mp hs))


/-- Uniform norm bounds turn convergence of the total coefficient tests into weak convergence. -/
theorem inner_tendsto_of_bounded_coefficients
    {u : ℕ → ThresholdHilbert} {f : ThresholdHilbert} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C)
    (hc : ∀ i, Tendsto (fun n => coefficientCLM (i + 2) (u n))
      atTop (𝓝 (coefficientCLM (i + 2) f))) (x : ThresholdHilbert) :
    Tendsto (fun n => inner ℝ x (u n)) atTop (𝓝 (inner ℝ x f)) := by
  have hz : Tendsto (fun n => inner ℝ x (u n - f)) atTop (𝓝 0) := by
    apply RiemannResearch.Analysis.tendsto_inner_zero_of_mem_closure_span
      (S := Set.range (fun i => mobiusRieszHilbert (i + 2)))
      (C := C + ‖f‖) (by positivity)
    · exact Filter.Eventually.of_forall (fun n =>
        (norm_sub_le _ _).trans (add_le_add (hb n) le_rfl))
    · rintro y ⟨i, rfl⟩
      have ht : Tendsto (fun n => mobiusDifferenceCLM (i + 2) (u n))
          atTop (𝓝 (mobiusDifferenceCLM (i + 2) f)) := by
        simpa only [coefficientCLM, neg_apply, neg_neg] using (hc i).neg
      simpa only [mobiusRieszHilbert_inner, map_sub, sub_self] using
        ht.sub_const (mobiusDifferenceCLM (i + 2) f)
    · rw [mobiusRiesz_total]
      trivial
  simpa only [inner_sub_right, sub_add_cancel, zero_add] using hz.add_const (inner ℝ x f)

/-- Truncate the continuous residue coordinates of an arbitrary Hilbert vector. -/
def coefficientPartialSum (f : ThresholdHilbert) (N : ℕ) : ThresholdHilbert :=
  ∑ i ∈ Finset.range N, coefficientCLM (i + 2) f • residueAtom i

/-- Each fixed coefficient is recovered exactly once the truncation reaches it. -/
theorem coefficientPartialSum_coordinate (f : ThresholdHilbert) (N i : ℕ) :
    coefficientCLM (i + 2) (coefficientPartialSum f N) =
      if i < N then coefficientCLM (i + 2) f else 0 := by
  simp [coefficientPartialSum, map_sum, map_smul, coefficientCLM_biorthogonal,
    Finset.mem_range]

/-- Every finite coefficient synthesis lies in the closed legal residue span. -/
theorem coefficientPartialSum_mem (f : ThresholdHilbert) (N : ℕ) :
    coefficientPartialSum f N ∈ closedSpace := by
  apply closedSpace.sum_mem
  intro i hi
  exact closedSpace.smul_mem _ (subset_closure (Submodule.subset_span ⟨i, rfl⟩))

/-- Even a bounded cofinal subsequence forces an orthogonal vector to vanish. -/
theorem zero_of_cofinally_bounded_coefficientPartialSum
    (f : ThresholdHilbert) (hf : f ∈ closedSpaceᗮ) (C : ℝ)
    (hb : ∀ N, ∃ n, N ≤ n ∧ ‖coefficientPartialSum f n‖ ≤ C) : f = 0 := by
  classical
  choose k hk hkb using hb
  have hC : 0 ≤ C := (norm_nonneg _).trans (hkb 0)
  have hcoord (i : ℕ) :
      Tendsto (fun n => coefficientCLM (i + 2) (coefficientPartialSum f (k n)))
        atTop (𝓝 (coefficientCLM (i + 2) f)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    rw [coefficientPartialSum_coordinate, if_pos (by have := hk n; omega)]
  have ht := inner_tendsto_of_bounded_coefficients hC hkb hcoord f
  have ho (n : ℕ) : inner ℝ f (coefficientPartialSum f (k n)) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal f).mp hf _ (coefficientPartialSum_mem f (k n))
  simp only [ho] at ht
  exact inner_self_eq_zero.mp (tendsto_nhds_unique ht tendsto_const_nhds)


/-- A nonzero orthogonal vector has residue-coordinate truncations tending to infinite norm. -/
theorem coefficientPartialSum_norm_tendsto
    (f : ThresholdHilbert) (hf : f ∈ closedSpaceᗮ) (hne : f ≠ 0) :
    Tendsto (fun N => ‖coefficientPartialSum f N‖) atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  by_contra h
  have hb : ∀ N, ∃ n, N ≤ n ∧ ‖coefficientPartialSum f n‖ ≤ C := by
    intro N
    by_contra hh
    push Not at hh
    apply h
    exact eventually_atTop.mpr ⟨N, fun n hn => le_of_lt (hh n hn)⟩
  exact hne (zero_of_cofinally_bounded_coefficientPartialSum f hf C hb)

/-- Finite synthesis of the actual signed arithmetic coefficient defect. -/
def defectPartialSum (N : ℕ) : ThresholdHilbert :=
  ∑ i ∈ Finset.range N, coefficientDefect i • residueAtom i

/-- Defect truncations are the negatives of the residual's coefficient truncations. -/
theorem defectPartialSum_eq_neg_residual_partialSum (N : ℕ) :
    defectPartialSum N = -coefficientPartialSum limitResidual N := by
  simp [defectPartialSum, coefficientPartialSum, coefficientDefect_eq_neg_residual_coefficient,
    Finset.sum_neg_distrib, neg_smul]

/-- A proved necessary failure under not RH, with no RH-to-density converse assumed. -/
theorem defectPartialSum_norm_tendsto_of_not_rh (h : ¬ RiemannHypothesis) :
    Tendsto (fun N => ‖defectPartialSum N‖) atTop atTop := by
  have hn : limitResidual ≠ 0 := by
    intro hz
    exact h (riemannHypothesis_of_limitCoefficients
      (limitCoefficients_eq_mobius_iff_residual_zero.mpr hz))
  simpa only [defectPartialSum_eq_neg_residual_partialSum, norm_neg] using
    coefficientPartialSum_norm_tendsto limitResidual limitResidual_mem_orthogonal hn

/-- Exact Gram energy, retaining every mixed term and the full Hilbert inner products. -/
theorem defectPartialSum_norm_sq (N : ℕ) :
    ‖defectPartialSum N‖ ^ 2 =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        coefficientDefect i * coefficientDefect j *
          inner ℝ (residueAtom i) (residueAtom j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [defectPartialSum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (residueAtom j) (residueAtom i)]
  ring


/-- The full atom energy is bounded by its exact mean because 0 <= g_d <= 1. -/
theorem residueAtom_norm_sq_le_log (i : ℕ) :
    ‖residueAtom i‖ ^ 2 ≤ Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) := by
  have hbounds (n : ℕ) : 0 ≤ hilbertSequence (residueAtom i) n ∧
      hilbertSequence (residueAtom i) n ≤ 1 := by
    rw [residueAtom, normalizedResidueHilbert_sequence]
    constructor
    · unfold residueFraction; positivity
    · unfold residueFraction
      apply (div_le_one (by positivity : (0 : ℝ) < (i + 2 : ℕ))).mpr
      exact_mod_cast (Nat.mod_lt n (by omega : 0 < i + 2)).le
  have habs (n : ℕ) : |hilbertSequence (residueAtom i) n| ≤ 1 := by
    rw [abs_of_nonneg (hbounds n).1]
    exact (hbounds n).2
  rw [← residueAtom_inner_one, hilbert_inner_one, hilbert_norm_weighted_sq]
  apply (hilbertSequence_square_summable _).tsum_le_tsum _ (weighted_summable_of_bounded habs)
  intro n
  apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg n)
  nlinarith [(hbounds n).1, (hbounds n).2]

/-- An explicit weight for absolute coefficient synthesis. -/
theorem residueAtom_norm_le_sqrt_log (i : ℕ) :
    ‖residueAtom i‖ ≤ Real.sqrt
      (Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ)) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (residueAtom_norm_sq_le_log i)

/-- Weighted absolute regularity of the actual defect forces zero residual. -/
theorem residual_zero_of_summable_weighted_defect
    (h : Summable (fun i => |coefficientDefect i| * Real.sqrt
      (Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ)))) :
    limitResidual = 0 := by
  apply defect_series_summable_iff_residual_zero.mp
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ h
  intro i
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (residueAtom_norm_le_sqrt_log i) (abs_nonneg _)

/-- OPEN arithmetic provider: a cofinal bounded full signed defect Gram energy implies RH. -/
theorem riemannHypothesis_of_cofinal_defect_gram_bound
    (C : ℝ)
    (h : ∀ N, ∃ n, N ≤ n ∧
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        coefficientDefect i * coefficientDefect j *
          inner ℝ (residueAtom i) (residueAtom j)) ≤ C) : RiemannHypothesis := by
  have hb : ∀ N, ∃ n, N ≤ n ∧
      ‖coefficientPartialSum limitResidual n‖ ≤ Real.sqrt (max C 0) := by
    intro N
    obtain ⟨n, hn, he⟩ := h N
    refine ⟨n, hn, ?_⟩
    have he' : ‖coefficientPartialSum limitResidual n‖ ^ 2 ≤ C := by
      simpa only [← defectPartialSum_norm_sq, defectPartialSum_eq_neg_residual_partialSum, norm_neg] using he
    exact (Real.le_sqrt (norm_nonneg _) (le_max_right _ _)).mpr
      (he'.trans (le_max_left _ _))
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (zero_of_cofinally_bounded_coefficientPartialSum limitResidual
        limitResidual_mem_orthogonal _ hb))


/-- Direct RH consumer for the explicit scalar regularity condition. -/
theorem riemannHypothesis_of_summable_weighted_defect
    (h : Summable (fun i => |coefficientDefect i| * Real.sqrt
      (Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ)))) :
    RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (residual_zero_of_summable_weighted_defect h))

/-- Failure of RH forces incorrect coefficients beyond every conductor bound. -/
theorem coefficient_defects_unbounded_of_not_rh (h : ¬ RiemannHypothesis) (N : ℕ) :
    ∃ d, N ≤ d ∧ 1 < d ∧ limitCoefficient d ≠ -(ArithmeticFunction.moebius d : ℝ) := by
  by_contra hn
  push Not at hn
  apply h
  apply riemannHypothesis_of_eventual_mobius
  filter_upwards [eventually_ge_atTop N] with i hi
  exact hn (i + 2) (by omega) (by omega)

/-- The same eventual criterion stated in the precise mode-series notation of Candidate 4. -/
theorem riemannHypothesis_of_eventual_mode_mobius_tsum
    (h : ∀ᶠ i in atTop, (∑' j, modeAlpha j * modeCoefficient (i + 2) j) =
      -(ArithmeticFunction.moebius (i + 2) : ℝ)) : RiemannHypothesis := by
  apply riemannHypothesis_of_eventual_mobius
  simpa only [← limitCoefficient_eq_mode_tsum] using h

end RiemannResearch.RH.Pareto.CoefficientStabilization
