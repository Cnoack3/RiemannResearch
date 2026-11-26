import RiemannResearch.RH.PhysicalHeadParityMinimum
import RiemannResearch.RH.RamanujanWeakConvergence
import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.CenteredMeanRHCriteria
import RiemannResearch.RH.CompositePacketClosure
import RiemannResearch.RH.MixedConductorSquareZero

/-!
# The weak-limit step for Nyman–Beurling physical head sections

Source: the proposed CRT and change-of-section argument. A bounded cofinal
selection with exact physical heads converges weakly to the ambient unit.
The finite-window construction below also allows each complete norm to exceed
an arbitrarily prescribed budget. Every correction at a given head can be
represented with the same period, independently of the prescribed budget.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadWeakLimit

open CoefficientStabilization AffineHeadTower PhysicalHeadFiniteMinimum PhysicalHeadParityMinimum
open TwoSeedExactHeadEnergy
open RiemannResearch.Analysis.HilbertWeakNorm
open RiemannResearch.RH.RamanujanWeakConvergence

/-- Changing the legal section twice composes to the single endpoint shear. -/
theorem changeUnit_through_seed (u g f x : closedSpace)
    (hu : legalPacketMean u = 1) (hg : legalPacketMean g = 1) :
    LegalMeanAlgebra.changeUnit g f (LegalMeanAlgebra.changeUnit u g x) =
      LegalMeanAlgebra.changeUnit u f x := by
  rw [LegalMeanAlgebra.changeUnit_apply g f, LegalMeanAlgebra.mean_changeUnit hu hg,
    LegalMeanAlgebra.changeUnit_apply, LegalMeanAlgebra.changeUnit_apply]
  module

/-- Signed orthogonality gives the exact full-axis error after any legal mixed correction. -/
theorem screened_mixed_error_sq {k : ThresholdHilbert} (hk : k ∈ mixedClosure) :
    ‖normalizedScreenedTwo + k - hilbertOne‖^2 =
      ‖normalizedScreenedTwo - hilbertOne‖^2 + ‖k‖^2 := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  have hper := mixedClosure.orthogonal.sub_mem hu.2 one_mem_mixedClosure_orthogonal
  have ho := (Submodule.mem_orthogonal' _ _).mp hper k hk
  rw [show normalizedScreenedTwo + k - hilbertOne =
    (normalizedScreenedTwo - hilbertOne) + k by abel, norm_add_sq_real, ho]
  ring

/-- A bounded cofinal selection of exact heads converges against every Hilbert test vector. -/
theorem bounded_sections_innerWeak (N : ℕ → ℕ) (v : ℕ → ThresholdHilbert)
    (hN : Tendsto N atTop atTop) (hv : ∀ j, v j ∈ fiber (N j))
    (C : ℝ) (hC : ∀ᶠ j in atTop, ‖v j‖ ^ 2 ≤ C) :
    InnerWeakTendsto v atTop hilbertOne := by
  refine pareto_innerWeak_of_bounded_pointwise v hilbertOne ?_ C hC
  intro k hk
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  apply tendsto_const_nhds.congr'
  filter_upwards [hN.eventually_ge_atTop (i+1)] with j hj
  have he := (hv j).2.2 i (by omega)
  simpa only [physicalEvaluationCLM_apply, hilbertOne_sequence, zeroAnchor,
    Nat.succ_ne_zero, if_false] using he.symm

/-- With the full Pareto norm bound, the weak limit belongs to the legal space,
the screened section equals the unit, the mixed space and constant line split orthogonally, and RH follows. -/
theorem nymanBeurling_of_bounded_sections (N : ℕ → ℕ) (v : ℕ → ThresholdHilbert)
    (hN : Tendsto N atTop atTop) (hv : ∀ j, v j ∈ fiber (N j))
    (C : ℝ) (hC : ∀ᶠ j in atTop, ‖v j‖ ^ 2 ≤ C) :
    InnerWeakTendsto v atTop hilbertOne ∧ hilbertOne ∈ closedSpace ∧
      normalizedScreenedTwo = hilbertOne ∧
      mixedClosure ⊔ Submodule.span ℝ {hilbertOne} = closedSpace ∧
      hilbertOne ∈ mixedClosureᗮ ∧ RiemannHypothesis := by
  have hweak := bounded_sections_innerWeak N v hN hv C hC
  have hcl := mem_closure_of_innerWeak closedSpace v hilbertOne
    (Eventually.of_forall fun j => (hv j).1) hweak
  have hmem : hilbertOne ∈ closedSpace :=
    closedSpace.topologicalClosure_minimal le_rfl (Submodule.isClosed_topologicalClosure _) hcl
  refine ⟨hweak, hmem, one_mem_closedSpace_iff_normalizedScreenedTwo.mp hmem,
    mixedClosure_sup_span_of_mean_ne_zero hmem ?_, one_mem_mixedClosure_orthogonal, ?_⟩
  · rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
    exact one_ne_zero
  · exact CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.mpr
      (BaezDuarte.naturalApproximation_iff_one_mem.mpr hmem)

/-- The final Nyman–Beurling implication for J₂ / log 2 plus finite mixed corrections.
The head agreement and the complete norm bound need only hold on a cofinal selection. -/
theorem nymanBeurling_of_bounded_parity_corrections (N B : ℕ → ℕ) (m : ℕ → ThresholdHilbert)
    (hN : Tendsto N atTop atTop) (hm : ∀ j, m j ∈ mixedSpace (Finset.Icc 2 (B j)))
    (hhead : ∀ j i, i < N j → physicalEvaluationCLM i (paritySeed + m j) = 1)
    (C : ℝ) (hC : ∀ᶠ j in atTop, ‖paritySeed + m j‖^2 ≤ C) :
    InnerWeakTendsto (fun j => paritySeed + m j) atTop hilbertOne ∧
      hilbertOne ∈ closedSpace ∧ normalizedScreenedTwo = hilbertOne ∧
      mixedClosure ⊔ Submodule.span ℝ {hilbertOne} = closedSpace ∧
      hilbertOne ∈ mixedClosureᗮ ∧ RiemannHypothesis := by
  refine nymanBeurling_of_bounded_sections N (fun j => paritySeed + m j) hN ?_ C hC
  intro j
  obtain ⟨hmV, hm0⟩ := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero (m j)).mp
    (mixedSpace_window_le_closure _ (hm j))
  refine ⟨closedSpace.add_mem paritySeed_mem_mean.1 hmV, ?_, hhead j⟩
  rw [inner_add_left, paritySeed_mem_mean.2, hm0, add_zero]

/-- Evaluating the unique full-norm minimizers in the quadratic windows leaves just the
cofinal bound on their complete Pareto norms as the final arithmetic hypothesis. -/
theorem nymanBeurling_of_bounded_parity_minima (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (C : ℝ) (hC : ∀ᶠ j in atTop, ‖paritySeed + optimalParityCorrection (N j)‖^2 ≤ C) :
    InnerWeakTendsto (fun j => paritySeed + optimalParityCorrection (N j)) atTop hilbertOne ∧
      hilbertOne ∈ closedSpace ∧ normalizedScreenedTwo = hilbertOne ∧
      mixedClosure ⊔ Submodule.span ℝ {hilbertOne} = closedSpace ∧
      hilbertOne ∈ mixedClosureᗮ ∧ RiemannHypothesis :=
  nymanBeurling_of_bounded_parity_corrections N (fun j => quadraticWindow (N j))
    (fun j => optimalParityCorrection (N j)) hN (fun j => (optimalParityCorrection_spec (N j)).1)
    (fun j => optimalParityCorrection_unit_head (N j)) C hC

/-- All finite mixed corrections supported in the same window have a common period. -/
theorem mixed_window_periodic (B : ℕ) {m : ThresholdHilbert}
    (hm : m ∈ mixedSpace (Finset.Icc 2 B)) :
    Function.Periodic (hilbertSequence m) B.factorial := by
  intro n
  let D := anchoredEvaluationCLM (n+B.factorial) - anchoredEvaluationCLM n
  have hker : mixedSpace (Finset.Icc 2 B) ≤ D.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    have hq : q.val ∈ Finset.Icc 2 B := (Finset.mem_filter.mp q.property).1
    obtain ⟨hq2, hqB⟩ := Finset.mem_Icc.mp hq
    change D (ramanujanPacketHilbert q.val) = 0
    simp only [D, ContinuousLinearMap.sub_apply, anchoredEvaluationCLM_apply,
      hilbertSequence_ramanujanPacketHilbert]
    exact sub_eq_zero.mpr
      (ramanujanPacket_period_of_dvd q.val B.factorial (Nat.dvd_factorial (by omega) hqB) n)
  have h := hker hm
  change D m = 0 at h
  simpa only [D, ContinuousLinearMap.sub_apply, anchoredEvaluationCLM_apply, sub_eq_zero] using h

/-- Anchored periodic physical sections vanish at their period. -/
theorem exact_head_lt_period {N L : ℕ} {v : ThresholdHilbert} (hL : 0 < L)
    (hper : Function.Periodic (hilbertSequence v) L) (hv : v ∈ fiber N) : N < L := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  by_contra! h
  have hz : hilbertSequence v (i+1) = 0 := by simpa using hper 0
  have ho := hv.2.2 i (by omega)
  rw [physicalEvaluationCLM_apply, hz] at ho
  exact zero_ne_one ho

/-- Adding J₂ / log 2 to an anchored L-periodic correction gives period 2L. -/
theorem parity_section_periodic {L : ℕ} {m : ThresholdHilbert}
    (hper : Function.Periodic (hilbertSequence m) L) :
    Function.Periodic (hilbertSequence (paritySeed + m)) (2*L) := by
  intro n
  have hm : hilbertSequence m (n+2*L) = hilbertSequence m n := by
    rw [show n+2*L = (n+L)+L by omega]
    exact (hper (n+L)).trans (hper n)
  have hp := ramanujanPacket_period_of_dvd 2 (2*L) ⟨L, rfl⟩ n
  have ev (k : ℕ) : hilbertSequence (paritySeed + m) k =
      (Real.log 2)⁻¹ * ramanujanPacket 2 k + hilbertSequence m k := by
    calc
      _ = anchoredEvaluationCLM k (paritySeed + m) :=
        (anchoredEvaluationCLM_apply _ _).symm
      _ = _ := by
        simp only [paritySeed, map_add, map_smul, anchoredEvaluationCLM_apply,
          hilbertSequence_ramanujanPacketHilbert, smul_eq_mul]
  rw [ev, ev, hm, hp]

/-- One fixed period for all corrections to the parity seed prevents cofinal unit heads. -/
theorem parity_head_lt_twice_correction_period {N L : ℕ} {m : ThresholdHilbert}
    (hL : 0 < L) (hper : Function.Periodic (hilbertSequence m) L)
    (hv : paritySeed + m ∈ fiber N) : N < 2*L :=
  exact_head_lt_period (by omega : 0 < 2*L) (parity_section_periodic hper) hv

/-- At fixed head and finite conductor window, a legal mean-one section can
exceed any complete-norm budget by prescribing its next physical value. -/
theorem arbitrarily_expensive_exact_head (g : ThresholdHilbert) (hg : g ∈ closedSpace)
    (hmean : inner ℝ g hilbertOne = 1) (N : ℕ) (C : ℝ) :
    ∃ m ∈ mixedSpace (Finset.Icc 2 (2*(N+2)^2)),
      g+m ∈ fiber N ∧ C < ‖g+m‖ := by
  let D := physicalEvaluationCLM N
  let A : ℝ := ‖D‖ * max C 0 + 1
  let a : Fin (N+1) → ℝ := fun i => if i.val = N then A else 1
  obtain ⟨m, hm, he⟩ := quadratic_window_mixed_head (N+1) (a - headRestriction (N+1) g)
  have hw : headRestriction (N+1) (g+m) = a := by rw [map_add, he]; abel
  have eval (i : ℕ) (hi : i < N+1) : physicalEvaluationCLM i (g+m) = a ⟨i,hi⟩ := by
    simpa only [physicalEvaluationCLM_apply, headRestriction_apply] using congrFun hw ⟨i,hi⟩
  obtain ⟨hmV, hm0⟩ := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero m).mp
    (mixedSpace_window_le_closure _ hm)
  refine ⟨m, hm, ⟨closedSpace.add_mem hg hmV, ?_, ?_⟩, ?_⟩
  · rw [inner_add_left, hmean, hm0, add_zero]
  · intro i hi
    simpa [a, ne_of_lt hi] using eval i (by omega)
  · have hA : 0 ≤ A := add_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _)) zero_le_one
    have heval : D (g+m) = A := by simpa [D, a] using eval N (by omega)
    have hbound := D.le_opNorm (g+m)
    rw [heval, Real.norm_eq_abs, abs_of_nonneg hA] at hbound
    by_contra! hbad
    have hle := mul_le_mul_of_nonneg_left (hbad.trans (le_max_left C 0)) (norm_nonneg D)
    dsimp only [A] at hbound
    linarith

/-- Periodic mixed corrections to J₂ / log 2 can have exact heads with costs exceeding
any prescribed sequence. Taking R(N)=N rules out every bounded subsequence of these lifts. -/
theorem exists_expensive_periodic_parity_sections (R : ℕ → ℝ) :
    ∃ m : ℕ → ThresholdHilbert, ∀ N,
      m N ∈ mixedSpace (Finset.Icc 2 (2*(N+2)^2)) ∧
      Function.Periodic (hilbertSequence (m N)) (2*(N+2)^2).factorial ∧
      Function.Periodic (hilbertSequence (paritySeed + m N)) (2*(2*(N+2)^2).factorial) ∧
      paritySeed + m N ∈ fiber N ∧ R N < ‖paritySeed + m N‖ := by
  choose m hm hf hcost using fun N => arbitrarily_expensive_exact_head paritySeed
    paritySeed_mem_mean.1 paritySeed_mem_mean.2 N (R N)
  refine ⟨m, fun N => ?_⟩
  have hper := mixed_window_periodic _ (hm N)
  exact ⟨hm N, hper, parity_section_periodic hper, hf N, hcost N⟩

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadWeakLimit
