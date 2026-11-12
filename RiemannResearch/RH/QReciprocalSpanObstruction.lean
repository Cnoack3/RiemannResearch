import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QDensitySquarefreeObstruction
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Restricted reciprocal-image spans: approximation and exact obstructions

Source: the user's density questions and the explicit two-site and four-site
calculations in the discussion. D divides physical coordinates by n, whereas
QDensityMetric.B is dQ/dP. An unbounded D-image family approximates one, but
omitted conductors can still force its entire closed span to be proper.
The sequence-preserving P/Q equivalence transfers these closure statements;
no symmetry of the two orthogonal projections is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QReciprocalSpanObstruction
open ZetaTwoHilbert ZetaTwoProbability QReciprocalMetric
open QDensitySquarefreeObstruction

def reciprocalSpan (s : Set ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ {f | ∃ k, k ∈ s ∧ f = D (qResidue k)}

theorem approximation_mem_reciprocalSpan (s : Set ℕ) (m : ℕ) (hm : m ∈ s) :
    QDensityMetric.approximation m ∈ reciprocalSpan s :=
  (reciprocalSpan s).smul_mem (m : ℝ) (Submodule.subset_span ⟨m, hm, rfl⟩)

theorem one_mem_reciprocalClosure_of_unbounded (s : Set ℕ)
    (hs : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ s) :
    qOne ∈ (reciprocalSpan s).topologicalClosure := by
  classical
  choose p hp hpS using hs
  have hpt : Tendsto p atTop atTop := tendsto_atTop_mono hp tendsto_id
  change qOne ∈ _root_.closure (reciprocalSpan s : Set QHilbert)
  exact mem_closure_of_tendsto (QDensityMetric.approximation_tendsto.comp hpt)
    (Eventually.of_forall fun N => approximation_mem_reciprocalSpan s (p N) (hpS N))

theorem one_mem_squarefree_reciprocalClosure :
    qOne ∈ (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure := by
  apply one_mem_reciprocalClosure_of_unbounded
  intro N
  obtain ⟨p, hN, hp⟩ := Nat.exists_infinite_primes N
  exact ⟨p, hN, hp.two_le, hp.squarefree⟩

theorem one_mem_strict_reciprocalClosure :
    qOne ∈ (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure := by
  apply one_mem_reciprocalClosure_of_unbounded
  intro N
  exact ⟨N + 3, by omega, by dsimp; omega⟩

/-- The four-site residue test after removing the reciprocal multiplier. -/
def reciprocalFourSite : QHilbert →L[ℝ] ℝ :=
  qEvalCLM 1 - (2 : ℝ) • qEvalCLM 2 -
    (3 : ℝ) • qEvalCLM 3 + (4 : ℝ) • qEvalCLM 4

theorem reciprocalFourSite_apply (f : QHilbert) :
    reciprocalFourSite f = qSequence f 1 - 2 * qSequence f 2 -
      3 * qSequence f 3 + 4 * qSequence f 4 := by
  simp [reciprocalFourSite, qEvalCLM_apply]

theorem reciprocalFourSite_D (f : QHilbert) :
    reciprocalFourSite (D f) =
      qSequence f 1 - qSequence f 2 - qSequence f 3 + qSequence f 4 := by
  rw [reciprocalFourSite_apply]
  simp only [qSequence_D]
  norm_num
  ring

theorem reciprocalFourSite_D_qResidue (k : ℕ) (hk : k ≠ 4) :
    reciprocalFourSite (D (qResidue k)) = 0 := by
  rw [reciprocalFourSite_D]
  simp only [qSequence_qResidue, ArithmeticCumulative.residueFraction]
  by_cases hsmall : k ≤ 4
  · interval_cases k <;> norm_num at *
  · have h1 : 1 < k := by omega
    have h2 : 2 < k := by omega
    have h3 : 3 < k := by omega
    have h4 : 4 < k := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
    norm_num only [Nat.cast_ofNat]
    ring

theorem reciprocalFourSite_D_qResidue_four :
    reciprocalFourSite (D (qResidue 4)) = -1 := by
  rw [reciprocalFourSite_D]
  simp only [qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

theorem reciprocalFourSite_qOne : reciprocalFourSite qOne = 0 := by
  rw [reciprocalFourSite_apply]
  simp only [qSequence_qOne]
  norm_num [qOneSequence]

theorem reciprocalFourSite_zero_on_closure {s : Set ℕ} (h4 : 4 ∉ s)
    {f : QHilbert} (hf : f ∈ (reciprocalSpan s).topologicalClosure) :
    reciprocalFourSite f = 0 := by
  have hle : reciprocalSpan s ≤ reciprocalFourSite.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨k, hk, rfl⟩
    change reciprocalFourSite (D (qResidue k)) = 0
    exact reciprocalFourSite_D_qResidue k (fun h => h4 (h ▸ hk))
  exact ((reciprocalSpan s).topologicalClosure_minimal hle
    reciprocalFourSite.isClosed_ker) hf

theorem reciprocal_four_not_mem_of_four_not_mem {s : Set ℕ} (h4 : 4 ∉ s) :
    D (qResidue 4) ∉ (reciprocalSpan s).topologicalClosure := by
  intro h
  have hz := reciprocalFourSite_zero_on_closure h4 h
  rw [reciprocalFourSite_D_qResidue_four] at hz
  norm_num at hz

theorem squarefree_reciprocal_four_not_mem :
    D (qResidue 4) ∉
      (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure := by
  apply reciprocal_four_not_mem_of_four_not_mem
  rintro ⟨_, hs⟩
  have hh := Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two
  norm_num at hh

theorem squarefree_reciprocalClosure_ne_top :
    (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure ≠ ⊤ := by
  intro h
  apply squarefree_reciprocal_four_not_mem
  rw [h]
  trivial

def twoSite : QHilbert →L[ℝ] ℝ := qEvalCLM 1 - qEvalCLM 2

theorem twoSite_apply (f : QHilbert) :
    twoSite f = qSequence f 1 - qSequence f 2 := by
  simp [twoSite, qEvalCLM_apply]

theorem twoSite_D_qResidue (k : ℕ) (hk : 2 < k) :
    twoSite (D (qResidue k)) = 0 := by
  rw [twoSite_apply]
  simp only [qSequence_D, qSequence_qResidue, ArithmeticCumulative.residueFraction]
  rw [Nat.mod_eq_of_lt (show 1 < k by omega), Nat.mod_eq_of_lt hk]
  norm_num only [Nat.cast_ofNat]
  ring

theorem twoSite_D_qResidue_two : twoSite (D (qResidue 2)) = (1 : ℝ) / 2 := by
  rw [twoSite_apply]
  simp only [qSequence_D, qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

theorem strict_reciprocalClosure_twoSite {f : QHilbert}
    (hf : f ∈ (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure) :
    qSequence f 1 = qSequence f 2 := by
  have hle : reciprocalSpan {k : ℕ | 2 < k} ≤ twoSite.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨k, hk, rfl⟩
    exact twoSite_D_qResidue k hk
  have h := ((reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure_minimal hle
    twoSite.isClosed_ker) hf
  change twoSite f = 0 at h
  rw [twoSite_apply, sub_eq_zero] at h
  exact h

theorem strict_reciprocal_two_not_mem :
    D (qResidue 2) ∉ (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure := by
  intro h
  have he := strict_reciprocalClosure_twoSite h
  have hz : twoSite (D (qResidue 2)) = 0 := by rw [twoSite_apply, he, sub_self]
  rw [twoSite_D_qResidue_two] at hz
  norm_num at hz

theorem strict_reciprocalClosure_ne_top :
    (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure ≠ ⊤ := by
  intro h
  apply strict_reciprocal_two_not_mem
  rw [h]
  trivial

def densityTwoSite : QHilbert →L[ℝ] ℝ :=
  (3 : ℝ) • qEvalCLM 1 - (2 : ℝ) • qEvalCLM 2

theorem densityTwoSite_apply (f : QHilbert) :
    densityTwoSite f = 3 * qSequence f 1 - 2 * qSequence f 2 := by
  simp [densityTwoSite, qEvalCLM_apply]

theorem densityTwoSite_B_qResidue (k : ℕ) (hk : 2 < k) :
    densityTwoSite (QDensityMetric.B (qResidue k)) = 0 := by
  rw [densityTwoSite_apply]
  simp only [QDensityMetric.qSequence_B, qSequence_qResidue,
    ArithmeticCumulative.residueFraction]
  rw [Nat.mod_eq_of_lt (show 1 < k by omega), Nat.mod_eq_of_lt hk]
  norm_num only [Nat.cast_ofNat]
  ring

theorem densityTwoSite_qOne : densityTwoSite qOne = 1 := by
  rw [densityTwoSite_apply]
  simp only [qSequence_qOne]
  norm_num [qOneSequence]

theorem strict_density_one_not_mem :
    qOne ∉ (densitySpan {k : ℕ | 2 < k}).topologicalClosure := by
  intro hf
  have hle : densitySpan {k : ℕ | 2 < k} ≤ densityTwoSite.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨k, hk, rfl⟩
    exact densityTwoSite_B_qResidue k hk
  have h := ((densitySpan {k : ℕ | 2 < k}).topologicalClosure_minimal hle
    densityTwoSite.isClosed_ker) hf
  change densityTwoSite qOne = 0 at h
  rw [densityTwoSite_qOne] at h
  norm_num at h

theorem strict_densityClosure_ne_top :
    (densitySpan {k : ℕ | 2 < k}).topologicalClosure ≠ ⊤ := by
  intro h
  apply strict_density_one_not_mem
  rw [h]
  trivial

open Pareto ZetaTwoParetoTransfer QParetoEquivalence

/-- Closed-span membership is symmetric under the physical P/Q identification. -/
theorem pareto_reciprocalClosure_mem_iff (s : Set ℕ) (f : QHilbert) :
    toPareto f ∈ ((reciprocalSpan s).map
      paretoEquiv.toLinearMap).topologicalClosure ↔
      f ∈ (reciprocalSpan s).topologicalClosure :=
  mem_closure_map_iff _ _

theorem pareto_one_mem_reciprocalClosure_of_unbounded (s : Set ℕ)
    (hs : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ s) :
    hilbertOne ∈ ((reciprocalSpan s).map
      paretoEquiv.toLinearMap).topologicalClosure := by
  have h := (pareto_reciprocalClosure_mem_iff s qOne).mpr
    (one_mem_reciprocalClosure_of_unbounded s hs)
  simpa only [toPareto_qOne] using h

theorem pareto_squarefree_reciprocalClosure_ne_top :
    ((reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).map
      paretoEquiv.toLinearMap).topologicalClosure ≠ ⊤ := by
  intro h
  apply squarefree_reciprocal_four_not_mem
  apply (pareto_reciprocalClosure_mem_iff _ (D (qResidue 4))).mp
  rw [h]
  trivial

theorem pareto_strict_reciprocalClosure_ne_top :
    ((reciprocalSpan {k : ℕ | 2 < k}).map
      paretoEquiv.toLinearMap).topologicalClosure ≠ ⊤ := by
  intro h
  apply strict_reciprocal_two_not_mem
  apply (pareto_reciprocalClosure_mem_iff _ (D (qResidue 2))).mp
  rw [h]
  trivial

theorem pareto_strict_density_one_not_mem :
    hilbertOne ∉ ((densitySpan {k : ℕ | 2 < k}).map
      paretoEquiv.toLinearMap).topologicalClosure := by
  intro h
  apply strict_density_one_not_mem
  apply (mem_closure_map_iff (densitySpan {k : ℕ | 2 < k}) qOne).mp
  simpa only [toPareto_qOne] using h

/-- Continuous removal of the conductor-two component. -/
def cutTwo : QHilbert →L[ℝ] QHilbert :=
  ContinuousLinearMap.id ℝ QHilbert -
    ((2 : ℝ) • twoSite).smulRight (D (qResidue 2))

theorem cutTwo_apply (f : QHilbert) :
    cutTwo f = f - (2 * twoSite f) • D (qResidue 2) := rfl

theorem cutTwo_D_qResidue_two : cutTwo (D (qResidue 2)) = 0 := by
  rw [cutTwo_apply, twoSite_D_qResidue_two]
  norm_num

theorem cutTwo_D_qResidue (k : ℕ) (hk : 2 < k) :
    cutTwo (D (qResidue k)) = D (qResidue k) := by
  rw [cutTwo_apply, twoSite_D_qResidue k hk]
  simp

/-- Full reciprocal density specializes to an exact codimension-one description
after removing conductor two. The full-density hypothesis is discharged in the
downstream full-conductor density module. -/
theorem strict_reciprocalClosure_eq_twoSite_ker
    (hfull : (reciprocalSpan {k : ℕ | 2 ≤ k}).topologicalClosure = ⊤) :
    (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure = twoSite.ker := by
  let H := (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure
  apply le_antisymm
  · intro f hf
    change twoSite f = 0
    rw [twoSite_apply, strict_reciprocalClosure_twoSite hf, sub_self]
  · intro f hf
    have hle : reciprocalSpan {k : ℕ | 2 ≤ k} ≤
        H.comap cutTwo.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro g ⟨k, hk, rfl⟩
      change 2 ≤ k at hk
      change cutTwo (D (qResidue k)) ∈ H
      by_cases hk2 : k = 2
      · subst k
        rw [cutTwo_D_qResidue_two]
        exact H.zero_mem
      · have hk3 : 2 < k := by omega
        rw [cutTwo_D_qResidue k hk3]
        exact (reciprocalSpan {k : ℕ | 2 < k}).le_topologicalClosure
          (Submodule.subset_span ⟨k, hk3, rfl⟩)
    have hc : IsClosed (H.comap cutTwo.toLinearMap : Set QHilbert) :=
      (Submodule.isClosed_topologicalClosure _).preimage cutTwo.continuous
    have hclosed := (reciprocalSpan {k : ℕ | 2 ≤ k}).topologicalClosure_minimal hle hc
    rw [hfull] at hclosed
    have hTf : cutTwo f ∈ H := hclosed (show f ∈ (⊤ : Submodule ℝ QHilbert) from trivial)
    change twoSite f = 0 at hf
    simpa only [cutTwo_apply, hf, mul_zero, zero_smul, sub_zero] using hTf

theorem pareto_strict_reciprocalClosure_iff
    (hfull : (reciprocalSpan {k : ℕ | 2 ≤ k}).topologicalClosure = ⊤)
    (f : QHilbert) :
    toPareto f ∈ ((reciprocalSpan {k : ℕ | 2 < k}).map
      paretoEquiv.toLinearMap).topologicalClosure ↔
      qSequence f 1 = qSequence f 2 := by
  rw [pareto_reciprocalClosure_mem_iff, strict_reciprocalClosure_eq_twoSite_ker hfull]
  change twoSite f = 0 ↔ _
  rw [twoSite_apply, sub_eq_zero]


/-- The strict-conductor family misses the smoothed RH target, although it
contains the unsmoothed constant. -/
theorem twoSite_D_qOne : twoSite (D qOne) = (1 : ℝ) / 2 := by
  rw [twoSite_apply]
  simp only [qSequence_D, qSequence_qOne]
  norm_num [qOneSequence]

theorem strict_reciprocal_D_one_not_mem :
    D qOne ∉ (reciprocalSpan {k : ℕ | 2 < k}).topologicalClosure := by
  intro h
  have he := strict_reciprocalClosure_twoSite h
  have hz : twoSite (D qOne) = 0 := by rw [twoSite_apply, he, sub_self]
  rw [twoSite_D_qOne] at hz
  norm_num at hz

theorem squarefree_reciprocalClosure_fourSite {f : QHilbert}
    (hf : f ∈ (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure) :
    reciprocalFourSite f = 0 := by
  apply reciprocalFourSite_zero_on_closure (s := {k : ℕ | 2 ≤ k ∧ Squarefree k}) _ hf
  rintro ⟨_, hs⟩
  have hh := Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two
  norm_num at hh

theorem reciprocalFourSite_D_D_qOne :
    reciprocalFourSite (D (D qOne)) = (5 : ℝ) / 12 := by
  rw [reciprocalFourSite_D]
  simp only [qSequence_D, qSequence_qOne]
  norm_num [qOneSequence]

theorem reciprocalFourSite_D_D_qResidue_two :
    reciprocalFourSite (D (D (qResidue 2))) = (1 : ℝ) / 3 := by
  rw [reciprocalFourSite_D]
  simp only [qSequence_D, qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

theorem squarefree_reciprocal_D_D_one_not_mem :
    D (D qOne) ∉
      (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure := by
  intro h
  have hz := squarefree_reciprocalClosure_fourSite h
  rw [reciprocalFourSite_D_D_qOne] at hz
  norm_num at hz

theorem squarefree_reciprocal_D_D_two_not_mem :
    D (D (qResidue 2)) ∉
      (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure := by
  intro h
  have hz := squarefree_reciprocalClosure_fourSite h
  rw [reciprocalFourSite_D_D_qResidue_two] at hz
  norm_num at hz

/-- Reciprocal smoothing cannot be iterated within the squarefree smoothed span. -/
theorem D_not_preserves_squarefree_reciprocalClosure :
    ¬ (∀ f ∈ (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure,
      D f ∈ (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure) := by
  intro h
  apply squarefree_reciprocal_D_D_two_not_mem
  apply h
  apply (reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).le_topologicalClosure
  exact Submodule.subset_span ⟨2, ⟨by decide, Nat.prime_two.squarefree⟩, rfl⟩

theorem pareto_strict_reciprocal_D_one_not_mem :
    toPareto (D qOne) ∉ ((reciprocalSpan {k : ℕ | 2 < k}).map
      paretoEquiv.toLinearMap).topologicalClosure := by
  intro h
  exact strict_reciprocal_D_one_not_mem
    ((pareto_reciprocalClosure_mem_iff _ _).mp h)

theorem pareto_squarefree_reciprocal_D_D_one_not_mem :
    toPareto (D (D qOne)) ∉
      ((reciprocalSpan {k : ℕ | 2 ≤ k ∧ Squarefree k}).map
        paretoEquiv.toLinearMap).topologicalClosure := by
  intro h
  exact squarefree_reciprocal_D_D_one_not_mem
    ((pareto_reciprocalClosure_mem_iff _ _).mp h)
end RiemannResearch.RH.QReciprocalSpanObstruction
