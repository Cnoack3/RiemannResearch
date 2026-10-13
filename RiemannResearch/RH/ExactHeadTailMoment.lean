import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.ThresholdHilbertAdjoint
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.AffineObservationProjection
import RiemannResearch.RH.ExactHeadCofinalBounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Exact heads from one reciprocal tail moment

Source: user-provided `CRT_Exact_Head_Tail_Proof_and_Status_2026-09-30(1).md`.
The statements simplify its affine exact-head parameterization using the
already proved finite Mobius prefix identity. They do not prove any uniform
bound on the complete optimized tail error and do not assume RH.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open RiemannResearch.RH.ArithmeticCumulative
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

/-- Fixed Mobius head and an arbitrary finite high-conductor tail. -/
def mobiusTailSynthesis (M : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  -(∑ d ∈ Finset.Icc 1 M,
    (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) +
  ∑ d ∈ s, c d * residueFraction d n

/-- All exact-head defects are one scalar times the physical index. -/
theorem mobiusTailSynthesis_head_identity
    (M : ℕ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, M < d) (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    mobiusTailSynthesis M s c n =
      1 + (n : ℝ) *
        ((∑ d ∈ s, c d / (d : ℝ)) - mobiusReciprocalSum M) := by
  have htail : (∑ d ∈ s, c d * residueFraction d n) =
      (n : ℝ) * (∑ d ∈ s, c d / (d : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    unfold residueFraction
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hnM (hs d hd))]
    ring
  unfold mobiusTailSynthesis
  rw [mobius_residue_prefix_identity M n hn hnM, htail]
  ring

/-- Once the forced Mobius head is separated, one tail moment is necessary
and sufficient for the entire exact prefix. -/
theorem mobiusTailSynthesis_exact_head_iff
    (M : ℕ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hM : 0 < M) (hs : ∀ d ∈ s, M < d) :
    (∀ n, 0 < n → n ≤ M → mobiusTailSynthesis M s c n = 1) ↔
      (∑ d ∈ s, c d / (d : ℝ)) = mobiusReciprocalSum M := by
  constructor
  · intro hh
    have hfirst := hh 1 (by omega) hM
    rw [mobiusTailSynthesis_head_identity M s c hs 1 (by omega) hM] at hfirst
    norm_num at hfirst
    linarith
  · intro hrec n hn hnM
    rw [mobiusTailSynthesis_head_identity M s c hs n hn hnM, hrec]
    ring

end RiemannResearch.RH.Pareto


/-!
# Complete exact-head minima from a single tail observation

Source: user-provided `CRT_Exact_Head_Tail_Proof_and_Status_2026-09-30(1).md`.
The finite high-conductor span and the physical first observation implement
its exact-prefix optimization without forming a CRT period. Every candidate
has explicit finite legal support; all norms are complete Pareto norms.
Finite indices i in s represent actual tail conductors M+1+i. No RH is assumed;
the cofinal optimized-energy bound remains an explicit open premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open RiemannResearch.RH.ArithmeticCumulative
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ExactHeadTailMoment

open CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.SingleObservationProjection

/-- The physical first-coordinate observation representer. -/
def firstObservation : ThresholdHilbert := (2 : ℝ) • paretoPointHilbert 0

theorem firstObservation_apply (x : ThresholdHilbert) :
    inner ℝ firstObservation x = hilbertSequence x 1 := by
  rw [firstObservation, real_inner_smul_left, real_inner_comm, inner_paretoPoint,
    hilbertGibbsPhysical_eq]
  norm_num [paretoWeight] <;> ring

def tailResidueFamily (M : ℕ) (s : Finset ℕ) (i : s) : ThresholdHilbert :=
  normalizedResidueHilbert (M + 1 + i.val) (by omega)

abbrev tailResidueSpace (M : ℕ) (s : Finset ℕ) : Submodule ℝ ThresholdHilbert :=
  synthesisSpan (tailResidueFamily M s)

theorem normalizedResidue_mem_closedSpace (d : ℕ) (hd : 0 < d) :
    normalizedResidueHilbert d hd ∈ closedSpace := by
  apply (Submodule.le_topologicalClosure _)
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le residueAtom id d
    (normalizedResidueHilbert_mem_finiteSpace d d hd (by omega))

theorem tailResidueSpace_le_closedSpace (M : ℕ) (s : Finset ℕ) :
    tailResidueSpace M s ≤ closedSpace := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact normalizedResidue_mem_closedSpace (M + 1 + i.val) (by omega)

theorem tailResidueSpace_le_finiteSpace (M : ℕ) (s : Finset ℕ) :
    tailResidueSpace M s ≤ finiteSpace (M + s.sup id) := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  have hi : i.val ≤ s.sup id := Finset.le_sup (f := id) i.property
  exact normalizedResidueHilbert_mem_finiteSpace
    (M + s.sup id) (M + 1 + i.val) (by omega) (by omega)

theorem tail_observation_energy_pos (M : ℕ) (s : Finset ℕ)
    (hM : 0 < M) (hs : s.Nonempty) :
    0 < ‖(tailResidueSpace M s).starProjection firstObservation‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hs
  let j : s := ⟨i, hi⟩
  have hx : tailResidueFamily M s j ∈ tailResidueSpace M s :=
    Submodule.subset_span ⟨j, rfl⟩
  have hobs : 0 < inner ℝ firstObservation (tailResidueFamily M s j) := by
    rw [firstObservation_apply]
    unfold tailResidueFamily
    rw [normalizedResidueHilbert_sequence]
    unfold residueFraction
    rw [Nat.mod_eq_of_lt (by omega : 1 < M + 1 + j.val)]
    positivity
  exact projection_energy_pos_of_observation (tailResidueSpace M s)
    firstObservation (tailResidueFamily M s j) hx (ne_of_gt hobs)

theorem tailResidueFamily_head (M : ℕ) (s : Finset ℕ) (i : s)
    (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    hilbertSequence (tailResidueFamily M s i) n =
      (n : ℝ) * hilbertSequence (tailResidueFamily M s i) 1 := by
  unfold tailResidueFamily
  simp only [normalizedResidueHilbert_sequence]
  unfold residueFraction
  rw [Nat.mod_eq_of_lt (by omega : n < M + 1 + i.val),
    Nat.mod_eq_of_lt (by omega : 1 < M + 1 + i.val)]
  push_cast
  ring

/-- The entire finite tail subspace has only one independent head observation. -/
theorem tailResidueSpace_head (M : ℕ) (s : Finset ℕ)
    {x : ThresholdHilbert} (hx : x ∈ tailResidueSpace M s)
    (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    hilbertSequence x n = (n : ℝ) * hilbertSequence x 1 := by
  change x ∈ Submodule.span ℝ (Set.range (tailResidueFamily M s)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact tailResidueFamily_head M s i n hn hnM
  | zero => cases n <;> simp [hilbertSequence]
  | add x y hx hy hix hiy =>
      simp only [hilbertSequence_add, Pi.add_apply, hix, hiy]
      ring
  | smul a x hx hix =>
      simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, hix]
      ring

/-- The target remaining after the forced finite Mobius head is removed. -/
def tailTarget (M : ℕ) : ThresholdHilbert :=
  hilbertOne - canonicalMobiusHilbert M +
    (((M + 1 : ℕ) : ℝ) * mobiusReciprocalSum M) •
      normalizedResidueHilbert (M + 1) (Nat.succ_pos _)

/-- The observation target is exactly one plus the full signed Mobius head. -/
theorem tailTarget_sequence (M n : ℕ) :
    hilbertSequence (tailTarget M) n = zeroAnchor (fun _ => 1) n +
      ∑ d ∈ Finset.Icc 1 M,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d n := by
  unfold tailTarget
  simp only [hilbertSequence_add, hilbertSequence_sub, hilbertSequence_smul,
    Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [hilbertOne_sequence, canonicalMobiusHilbert_sequence,
    normalizedResidueHilbert_sequence]
  unfold canonicalMobiusHead
  ring

theorem tailTarget_head (M n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    hilbertSequence (tailTarget M) n = (n : ℝ) * mobiusReciprocalSum M := by
  unfold tailTarget
  simp only [hilbertSequence_add, hilbertSequence_sub, hilbertSequence_smul,
    Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [hilbertOne_sequence, canonicalMobiusHilbert_exact M n hn hnM,
    normalizedResidueHilbert_sequence]
  simp only [zeroAnchor, ne_of_gt hn, if_false]
  unfold residueFraction
  rw [Nat.mod_eq_of_lt (by omega : n < M + 1)]
  have hden : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

def tailCandidate (M : ℕ) (x : ThresholdHilbert) : ThresholdHilbert :=
  hilbertOne - tailTarget M + x

theorem tailCandidate_error (M : ℕ) (x : ThresholdHilbert) :
    hilbertOne - tailCandidate M x = tailTarget M - x := by
  unfold tailCandidate
  abel

theorem tailCandidate_mem_closedSpace (M : ℕ) (s : Finset ℕ)
    {x : ThresholdHilbert} (hx : x ∈ tailResidueSpace M s) :
    tailCandidate M x ∈ closedSpace := by
  have hid : tailCandidate M x = canonicalMobiusHilbert M -
      (((M + 1 : ℕ) : ℝ) * mobiusReciprocalSum M) •
        normalizedResidueHilbert (M + 1) (Nat.succ_pos _) + x := by
    unfold tailCandidate tailTarget
    abel
  rw [hid]
  exact closedSpace.add_mem
    (closedSpace.sub_mem (canonicalMobiusHilbert_mem_closedSpace M)
      (closedSpace.smul_mem _
        (normalizedResidue_mem_closedSpace (M + 1) (Nat.succ_pos _))))
    (tailResidueSpace_le_closedSpace M s hx)

/-- Every candidate is literally finite legal, with an explicit conductor cap. -/
theorem tailCandidate_mem_finiteSpace (M : ℕ) (s : Finset ℕ)
    {x : ThresholdHilbert} (hx : x ∈ tailResidueSpace M s) :
    tailCandidate M x ∈ finiteSpace (M + s.sup id) := by
  have hid : tailCandidate M x = canonicalMobiusHilbert M -
      (((M + 1 : ℕ) : ℝ) * mobiusReciprocalSum M) •
        normalizedResidueHilbert (M + 1) (Nat.succ_pos _) + x := by
    unfold tailCandidate tailTarget
    abel
  rw [hid]
  exact (finiteSpace (M + s.sup id)).add_mem
    ((finiteSpace (M + s.sup id)).sub_mem
      (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
        (by omega : M ≤ M + s.sup id) (canonicalMobiusHilbert_mem_finiteSpace M))
      ((finiteSpace (M + s.sup id)).smul_mem _
        (normalizedResidueHilbert_mem_finiteSpace (M + s.sup id)
          (M + 1) (Nat.succ_pos _) (by omega))))
    (tailResidueSpace_le_finiteSpace M s hx)

theorem tailCandidate_head (M : ℕ) (s : Finset ℕ)
    {x : ThresholdHilbert} (hx : x ∈ tailResidueSpace M s)
    (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    hilbertSequence (tailCandidate M x) n =
      1 + (n : ℝ) * (inner ℝ firstObservation x - mobiusReciprocalSum M) := by
  change hilbertSequence (hilbertOne - tailTarget M + x) n = _
  simp only [hilbertSequence_add, hilbertSequence_sub, Pi.add_apply, Pi.sub_apply]
  rw [hilbertOne_sequence, tailTarget_head M n hn hnM,
    tailResidueSpace_head M s hx n hn hnM, firstObservation_apply]
  simp only [zeroAnchor, ne_of_gt hn, if_false]
  ring

/-- Literal full head interpolation becomes one scalar observation. -/
theorem tailCandidate_exact_head_iff (M : ℕ) (s : Finset ℕ) (hM : 0 < M)
    {x : ThresholdHilbert} (hx : x ∈ tailResidueSpace M s) :
    (∀ n, 0 < n → n ≤ M → hilbertSequence (tailCandidate M x) n = 1) ↔
      inner ℝ firstObservation x = mobiusReciprocalSum M := by
  constructor
  · intro hh
    have hfirst := hh 1 (by omega) hM
    rw [tailCandidate_head M s hx 1 (by omega) hM] at hfirst
    norm_num at hfirst
    linarith
  · intro hrec n hn hnM
    rw [tailCandidate_head M s hx n hn hnM, hrec]
    ring

def optimalTailVector (M : ℕ) (s : Finset ℕ) : ThresholdHilbert :=
  affineObservationOptimizer (tailResidueSpace M s)
    firstObservation (tailTarget M) (mobiusReciprocalSum M)

def tailMinimum (M : ℕ) (s : Finset ℕ) : ℝ :=
  ‖tailTarget M - (tailResidueSpace M s).starProjection (tailTarget M)‖ ^ 2 +
    (mobiusReciprocalSum M -
      inner ℝ firstObservation ((tailResidueSpace M s).starProjection (tailTarget M))) ^ 2 /
    ‖(tailResidueSpace M s).starProjection firstObservation‖ ^ 2

theorem optimalTailVector_exact_head (M : ℕ) (s : Finset ℕ) (hM : 0 < M)
    (hq : ‖(tailResidueSpace M s).starProjection firstObservation‖ ^ 2 ≠ 0) :
    ∀ n, 0 < n → n ≤ M →
      hilbertSequence (tailCandidate M (optimalTailVector M s)) n = 1 := by
  apply (tailCandidate_exact_head_iff M s hM
    (affineObservationOptimizer_mem (tailResidueSpace M s)
      firstObservation (tailTarget M) (mobiusReciprocalSum M))).mpr
  exact affineObservationOptimizer_observation (tailResidueSpace M s)
    firstObservation (tailTarget M) (mobiusReciprocalSum M) hq

theorem tailMinimum_attained (M : ℕ) (s : Finset ℕ)
    (hq : ‖(tailResidueSpace M s).starProjection firstObservation‖ ^ 2 ≠ 0) :
    ‖hilbertOne - tailCandidate M (optimalTailVector M s)‖ ^ 2 = tailMinimum M s := by
  rw [tailCandidate_error]
  exact affineObservationOptimizer_energy (tailResidueSpace M s)
    firstObservation (tailTarget M) (mobiusReciprocalSum M) hq

theorem tailMinimum_completion (M : ℕ) (s : Finset ℕ) (hM : 0 < M)
    (hq : ‖(tailResidueSpace M s).starProjection firstObservation‖ ^ 2 ≠ 0)
    {x : ThresholdHilbert} (hx : x ∈ tailResidueSpace M s)
    (hh : ∀ n, 0 < n → n ≤ M → hilbertSequence (tailCandidate M x) n = 1) :
    ‖hilbertOne - tailCandidate M x‖ ^ 2 = tailMinimum M s +
      ‖x - optimalTailVector M s‖ ^ 2 := by
  rw [tailCandidate_error]
  exact affine_observation_error_completion (tailResidueSpace M s)
    firstObservation (tailTarget M) x (mobiusReciprocalSum M) hq hx
    ((tailCandidate_exact_head_iff M s hM hx).mp hh)

end RiemannResearch.RH.Pareto.ExactHeadTailMoment


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.ExactHeadTailMoment
open CoefficientStabilization
open RiemannResearch.Analysis.SingleObservationProjection

theorem tailMinimum_nonneg (M : ℕ) (s : Finset ℕ) :
    0 ≤ tailMinimum M s := by
  unfold tailMinimum
  positivity

theorem tailMinimum_isLeast (M : ℕ) (s : Finset ℕ)
    (hM : 0 < M) (hs : s.Nonempty) :
    IsLeast {E : ℝ | ∃ x : ThresholdHilbert, x ∈ tailResidueSpace M s ∧
      (∀ n, 0 < n → n ≤ M → hilbertSequence (tailCandidate M x) n = 1) ∧
      ‖hilbertOne - tailCandidate M x‖ ^ 2 = E} (tailMinimum M s) := by
  have hq := ne_of_gt (tail_observation_energy_pos M s hM hs)
  refine ⟨⟨optimalTailVector M s, ?_, optimalTailVector_exact_head M s hM hq,
    tailMinimum_attained M s hq⟩, ?_⟩
  · exact affineObservationOptimizer_mem (tailResidueSpace M s)
      firstObservation (tailTarget M) (mobiusReciprocalSum M)
  · rintro E ⟨x, hx, hh, rfl⟩
    rw [tailMinimum_completion M s hM hq hx hh]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem tailResidueSpace_mono (M : ℕ) {s t : Finset ℕ} (hst : s ⊆ t) :
    tailResidueSpace M s ≤ tailResidueSpace M t := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact Submodule.subset_span ⟨⟨i.val, hst i.property⟩, rfl⟩

theorem tailMinimum_antitone_dictionary (M : ℕ) {s t : Finset ℕ}
    (hM : 0 < M) (hs : s.Nonempty) (hst : s ⊆ t) :
    tailMinimum M t ≤ tailMinimum M s := by
  have ht : t.Nonempty := hs.mono hst
  have hq := ne_of_gt (tail_observation_energy_pos M s hM hs)
  apply (tailMinimum_isLeast M t hM ht).2
  exact ⟨optimalTailVector M s,
    tailResidueSpace_mono M hst
      (affineObservationOptimizer_mem (tailResidueSpace M s)
        firstObservation (tailTarget M) (mobiusReciprocalSum M)),
    optimalTailVector_exact_head M s hM hq, tailMinimum_attained M s hq⟩

/-- Conditional research reduction. The cofinal bound on the actual complete
minimum is the open arithmetic premise; no estimate for it is asserted. -/
theorem riemannHypothesis_of_cofinally_bounded_tailMinimum
    (s : ℕ → Finset ℕ) (hs : ∀ N, (s N).Nonempty) (C : ℝ)
    (hbound : ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ tailMinimum (N + 1) (s N) ≤ C) :
    RiemannHypothesis := by
  let F : ℕ → ThresholdHilbert := fun N =>
    tailCandidate (N + 1) (optimalTailVector (N + 1) (s N))
  have hq (N : ℕ) :
      ‖(tailResidueSpace (N + 1) (s N)).starProjection firstObservation‖ ^ 2 ≠ 0 :=
    ne_of_gt (tail_observation_energy_pos (N + 1) (s N) (by omega) (hs N))
  have hz : limitEnergy = 0 := by
    refine limitEnergy_eq_zero_of_cofinally_bounded_exact_head_errors F ?_ ?_ C ?_
    · intro N
      exact tailCandidate_mem_closedSpace (N + 1) (s N)
        (affineObservationOptimizer_mem (tailResidueSpace (N + 1) (s N))
          firstObservation (tailTarget (N + 1)) (mobiusReciprocalSum (N + 1)))
    · intro N k hk hkN
      exact optimalTailVector_exact_head (N + 1) (s N) (by omega) (hq N)
        k hk (by omega)
    · intro M
      obtain ⟨N, hMN, hN⟩ := hbound M
      refine ⟨N, hMN, ?_⟩
      change ‖hilbertOne - tailCandidate (N + 1)
        (optimalTailVector (N + 1) (s N))‖ ^ 2 ≤ C
      rw [tailMinimum_attained (N + 1) (s N) (hq N)]
      exact hN
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (limitEnergy_zero_iff_mem.mp hz))

end RiemannResearch.RH.Pareto.ExactHeadTailMoment
