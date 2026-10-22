import RiemannResearch.RH.ParetoIndependentEvenCorrection

/-!
# The actual corrected-sieve block-mean criterion for RH

Source: the next concrete target of the user's parity-closure handoff,
21 September 2026. Every corrected tail is lifted to the original residue
closure with its exact nonzero first-coordinate head. The final implication
is conditional on decay of the actual complete block-mean energy; that
arithmetic estimate remains Open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.ArithmeticCumulative

theorem tailAtom_lift_eq_residueAtom (i : ℕ) :
    tailAtom i + (1 / ((i + 2 : ℕ) : ℝ)) • paretoPointHilbert 0 = residueAtom i := by
  change residueAtom i - (anchoredEvaluationCLM 1 (residueAtom i)) •
    paretoPointHilbert 0 + _ = _
  rw [residueAtom_evaluation]
  abel

theorem finite_tail_lift_mem_closedSpace {ι : Type*} (s : Finset ι)
    (i : ι → ℕ) (c : ι → ℝ) :
    (∑ j ∈ s, c j • tailAtom (i j)) +
      (∑ j ∈ s, c j / ((i j + 2 : ℕ) : ℝ)) • paretoPointHilbert 0 ∈ closedSpace := by
  have hm : (∑ j ∈ s, (c j • tailAtom (i j) +
      (c j / ((i j + 2 : ℕ) : ℝ)) • paretoPointHilbert 0)) ∈ closedSpace := by
    apply Submodule.sum_mem
    intro j hj
    have he : c j / ((i j + 2 : ℕ) : ℝ) =
        c j * (1 / ((i j + 2 : ℕ) : ℝ)) := by ring
    rw [he, ← smul_smul, ← smul_add, tailAtom_lift_eq_residueAtom]
    apply closedSpace.smul_mem
    exact subset_closure (Submodule.subset_span ⟨i j, rfl⟩)
  simpa only [Finset.sum_add_distrib, Finset.sum_smul] using hm

theorem sieveMobiusTail_lift_mem_closedSpace (P : ℕ) (a : ℝ) :
    sieveMobiusTail P a + sieveMobiusHead P a • paretoPointHilbert 0 ∈ closedSpace := by
  have hm := finite_tail_lift_mem_closedSpace (P.divisors.erase 1)
    (fun d => d - 2) (fun d => -a * (ArithmeticFunction.moebius d : ℝ))
  have he : (∑ d ∈ P.divisors.erase 1,
      (-a * (ArithmeticFunction.moebius d : ℝ)) / ((d - 2 + 2 : ℕ) : ℝ)) =
      sieveMobiusHead P a := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.sub_add_cancel (sieve_nonunit_divisor_ge_two P d hd)]
  simpa only [he, sieveMobiusTail] using hm

theorem sieveMobiusNormalizedTail_lift_mem_closedSpace (P : ℕ) (a : ℝ) :
    sieveMobiusNormalizedTail P a + oddHeadConstant • paretoPointHilbert 0 ∈
      closedSpace := by
  have hm := closedSpace.add_mem (sieveMobiusTail_lift_mem_closedSpace P a)
    (closedSpace.smul_mem (2 * (oddHeadConstant - sieveMobiusHead P a))
      (show residueAtom 0 ∈ closedSpace from
        subset_closure (Submodule.subset_span ⟨0, rfl⟩)))
  have ht : tailAtom 0 = residueAtom 0 - (1 / 2 : ℝ) • paretoPointHilbert 0 := by
    change residueAtom 0 - (anchoredEvaluationCLM 1 (residueAtom 0)) • _ = _
    rw [residueAtom_evaluation]
    norm_num
  have he : sieveMobiusNormalizedTail P a + oddHeadConstant • paretoPointHilbert 0 =
      (sieveMobiusTail P a + sieveMobiusHead P a • paretoPointHilbert 0) +
        (2 * (oddHeadConstant - sieveMobiusHead P a)) • residueAtom 0 := by
    rw [sieveMobiusNormalizedTail, ht, smul_sub, smul_smul]
    rw [show 2 * (oddHeadConstant - sieveMobiusHead P a) * (1 / 2 : ℝ) =
      oddHeadConstant - sieveMobiusHead P a by ring, sub_smul]
    abel
  rw [he]
  exact hm

theorem evenTail_synthesis_zero_certificate_mem_closedSpace (n : ℕ)
    (c : EvenTailIndex n → ℝ)
    (hz : inner ℝ (Fintype.linearCombination ℝ (evenTailAtom n) c)
      (infiniteCoprimeCertificate 2) = 0) :
    Fintype.linearCombination ℝ (evenTailAtom n) c ∈ closedSpace := by
  have he : (∑ j : EvenTailIndex n, c j / ((j.val.val + 2 : ℕ) : ℝ)) = 0 := by
    rw [Fintype.linearCombination_apply, sum_inner] at hz
    simp only [real_inner_smul_left] at hz
    have ho (j : EvenTailIndex n) : inner ℝ (evenTailAtom n j)
        (infiniteCoprimeCertificate 2) = 1 / ((j.val.val + 2 : ℕ) : ℝ) := by
      unfold evenTailAtom
      rw [infiniteCoprimeCertificate_all_observations 2 j.val.val (by decide) (by decide),
        coprimeObservationDefect_two, if_pos j.property]
      ring
    simpa only [ho, div_eq_mul_inv, one_mul] using hz
  have hm := finite_tail_lift_mem_closedSpace (Finset.univ : Finset (EvenTailIndex n))
    (fun j => j.val.val) c
  simpa only [he, zero_smul, add_zero, Fintype.linearCombination_apply, evenTailAtom]
    using hm

theorem independentEvenCorrection_lift_mem_closedSpace (n : ℕ) (hn : 0 < n)
    (f : ThresholdHilbert) (a : ℝ)
    (hmem : f + a • paretoPointHilbert 0 ∈ closedSpace)
    (hz : inner ℝ f (infiniteCoprimeCertificate 2) = 0) :
    independentEvenCorrection n f + a • paretoPointHilbert 0 ∈ closedSpace := by
  let c := headConstrainedCoeff (evenTailAtom_independent n) f (infiniteCoprimeCertificate 2)
  have hc := independentEvenCorrection_observation n hn f
  change inner ℝ (f + Fintype.linearCombination ℝ (evenTailAtom n) c)
    (infiniteCoprimeCertificate 2) = 0 at hc
  rw [inner_add_left, hz, zero_add] at hc
  have hm := closedSpace.add_mem hmem
    (evenTail_synthesis_zero_certificate_mem_closedSpace n c hc)
  change (f + Fintype.linearCombination ℝ (evenTailAtom n) c) +
    a • paretoPointHilbert 0 ∈ closedSpace
  convert hm using 1 <;> abel

theorem independentlyCorrectedSieve_lift_mem_closedSpace (P m : ℕ)
    (hP : P ≠ 0) (h3 : 3 ∣ P) :
    independentlyCorrectedSieve P m + oddHeadConstant • paretoPointHilbert 0 ∈ closedSpace :=
  independentEvenCorrection_lift_mem_closedSpace (m + 1) (by omega) _ _
    (sieveMobiusNormalizedTail_lift_mem_closedSpace _ _)
    (sieveMobiusUnitTail_certificate P hP h3)

/-- CONDITIONAL RESEARCH REDUCTION: decay of the remaining actual block means
for any independent even-dictionary schedule implies Mathlib RH. -/
theorem riemannHypothesis_of_independentlyCorrectedSieve_blockMeans
    (m : ℕ → ℕ)
    (hblock : Tendsto (fun n => ‖dyadicHalfAdjoint
      (independentlyCorrectedSieve (n + 2).factorial (m n))‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have he := (independentlyCorrectedSieve_fullEnergy_iff_blockMeans m).mpr hblock
  have ht : Tendsto (fun n => independentlyCorrectedSieve (n + 2).factorial (m n) +
      oddHeadConstant • paretoPointHilbert 0) atTop
      (𝓝 (oddHeadConstant • paretoPointHilbert 0)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hs := he.eventually (gt_mem_nhds (sq_pos_of_pos hε))
    filter_upwards [hs] with n hn
    rw [dist_eq_norm, add_sub_cancel_right]
    nlinarith [norm_nonneg (independentlyCorrectedSieve (n + 2).factorial (m n))]
  have hm : ∀ᶠ n in atTop, independentlyCorrectedSieve (n + 2).factorial (m n) +
      oddHeadConstant • paretoPointHilbert 0 ∈ closedSpace := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact independentlyCorrectedSieve_lift_mem_closedSpace _ _ (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by norm_num) (by omega))
  have hc : IsClosed (closedSpace : Set ThresholdHilbert) :=
    Submodule.isClosed_topologicalClosure _
  have hp : oddHeadConstant • paretoPointHilbert 0 ∈ closedSpace := hc.mem_of_tendsto ht hm
  have hp' : paretoPointHilbert 0 ∈ closedSpace := by
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt oddHeadConstant_pos), one_smul] using
      closedSpace.smul_mem oddHeadConstant⁻¹ hp
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (firstPoint_mem_iff_one_mem.mp hp'))

end RiemannResearch.RH.Pareto
