import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.PrimeSievePointEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Explicit finite Euler residue candidates and their exact physical heads

Source: the user's finite Euler-operator proposal, 13 October 2026.
The signed divisor expansion is the finite Möbius Euler action on one residue.
The factorial conductor is redundant: nonsquarefree divisors have coefficient
zero. The exact rough-count identity proves eventual equality at every physical
coordinate. It does not assert convergence in the complete Q norm.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QFloorEulerCandidates
open ZetaTwoHilbert QFloorDilation QFullResidueProjection Pareto

/-- The explicit signed residue form of a finite Möbius Euler action. -/
def candidate (P m : ℕ) : QHilbert :=
  (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) • qResidue (m * d)) -
    (1 / (m : ℝ)) •
      ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) • qResidue d

theorem candidate_signed_expansion (P m : ℕ) :
    candidate P m = ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) •
      (qResidue (m * d) - (1 / (m : ℝ)) • qResidue d) := by
  unfold candidate
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [smul_sub, smul_smul]
  rw [mul_comm (1 / (m : ℝ))]

/-- Each summand is literally a floor dilation of the starting residue. -/
theorem candidate_summand (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    qResidue (m * d) - (1 / (m : ℝ)) • qResidue d =
      floorDilation d hd (qResidue m) := by
  rw [floorDilation_qResidue d m hd hm, Nat.mul_comm d m]

theorem candidate_legal (P m : ℕ) (hm : 0 < m) :
    candidate P m ∈ legalSpan := by
  rw [candidate_signed_expansion]
  apply legalSpan.sum_mem
  intro d hd
  exact legalSpan.smul_mem _ (legalSpan.sub_mem
    (qResidue_mem_legalSpan (m * d) (Nat.mul_pos hm (Nat.pos_of_mem_divisors hd)))
    (legalSpan.smul_mem _ (qResidue_mem_legalSpan d (Nat.pos_of_mem_divisors hd))))

theorem candidate_sequence (P m : ℕ) :
    qSequence (candidate P m) = fun n =>
      sieveResidue P m n - (1 / (m : ℝ)) * sieveResidue P 1 n := by
  change qSequenceLinear (candidate P m) = _
  unfold candidate
  rw [map_sub, map_smul, map_sum, map_sum]
  simp only [map_smul]
  funext n
  have hq (d : ℕ) : qSequenceLinear (qResidue d) =
      ArithmeticCumulative.residueFraction d := qSequence_qResidue d
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    hq, sieveResidue, Nat.one_mul]

/-- The two linear drift terms cancel exactly, without an estimate. -/
theorem candidate_rough_count (P m n : ℕ) (hP : 0 < P) (hm : 0 < m) :
    qSequence (candidate P m) n =
      sieveRoughCount P n / (m : ℝ) - sieveRoughCount P (n / m) := by
  rw [candidate_sequence]
  dsimp only
  rw [sieveResidue_exact P m n hP hm,
    sieveResidue_exact P 1 n hP (by decide)]
  simp only [Nat.div_one, Nat.cast_one, div_one]
  ring

/-- The target of the undamped Euler action on a single residue. -/
def target (m : ℕ) (hm : 0 < m) : QHilbert :=
  (1 / (m : ℝ)) • qOne - floorDilation m hm qOne

theorem target_sequence (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    qSequence (target m hm) n = 1 / (m : ℝ) - if m ≤ n then 1 else 0 := by
  change qSequenceLinear ((1 / (m : ℝ)) • qOne - floorDilation m hm qOne) n = _
  rw [map_sub, map_smul]
  change (1 / (m : ℝ)) * qSequence qOne n -
    qSequence (floorDilation m hm qOne) n = _
  rw [floorDilation_sequence, qSequence_qOne]
  by_cases hmn : m ≤ n
  · have hd : 0 < n / m := Nat.div_pos hmn hm
    simp [qOneSequence, ne_of_gt hn, ne_of_gt hd, hmn]
  · simp [qOneSequence, ne_of_gt hn,
      Nat.div_eq_of_lt (lt_of_not_ge hmn), hmn]

/-- At factorial cutoff Y, all positive coordinates up to Y already equal the target. -/
theorem candidate_factorial_head (Y m n : ℕ) (hm : 0 < m)
    (hn : 0 < n) (hnY : n ≤ Y) :
    qSequence (candidate Y.factorial m) n = qSequence (target m hm) n := by
  rw [candidate_rough_count _ _ _ (Nat.factorial_pos Y) hm,
    sieveRoughCount_factorial_head Y n hn hnY, target_sequence m n hm hn]
  by_cases hmn : m ≤ n
  · rw [if_pos hmn, sieveRoughCount_factorial_head Y (n / m)
      (Nat.div_pos hmn hm) ((Nat.div_le_self n m).trans hnY)]
  · rw [if_neg hmn, Nat.div_eq_of_lt (lt_of_not_ge hmn), sieveRoughCount_zero]

/-- Pointwise convergence is eventual equality; full-Q norm convergence is not inferred. -/
theorem candidate_pointwise_tendsto (m n : ℕ) (hm : 0 < m) :
    Tendsto (fun Y : ℕ => qSequence (candidate Y.factorial m) n)
      atTop (𝓝 (qSequence (target m hm) n)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with Y hY
  by_cases hn : n = 0
  · subst n
    simp [qSequence]
  · exact (candidate_factorial_head Y m n hm (Nat.pos_of_ne_zero hn) hY).symm

end RiemannResearch.RH.QFloorEulerCandidates
