import RiemannResearch.RH.RamanujanMultipleConstraints
import RiemannResearch.RH.RamanujanCoefficientConstraints
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.Analysis.FiniteGramFeasibleSources
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Exact feasibility and singular source Grams for Ramanujan constraints

Source: user-requested continuation of the duality structure, 23 October 2026.
Repeated conductors and conductors outside a finite packet stage are allowed.
Feasibility is classified exactly by agreement of repeated requests and zero
requests outside the stage. These elementary arithmetic conditions also
characterize solvability of the actual, possibly singular source Gram system.
Every feasible system has a unique legal optimizer with its full signed cost
and complete Gram-norm remainder, without an assumed row-rank condition.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanConstraintFeasibility
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RamanujanCoefficientConstraints
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramMultipleConstraint
open RiemannResearch.Analysis.FiniteGramFeasibleSources

variable {κ : Type*} [Fintype κ]

/-- The complete arithmetic compatibility condition, including repetitions. -/
def Compatible (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) : Prop :=
  (∀ i j, m i = m j → t i = t j) ∧ (∀ j, n + 1 < m j → t j = 0)

private def selectedValue (m : κ → ℕ) (t : κ → ℝ) (d : ℕ) : ℝ := by
  classical
  exact if h : ∃ j, m j = d then t (Classical.choose h) else 0

private theorem selectedValue_at (m : κ → ℕ) (t : κ → ℝ)
    (hc : ∀ i j, m i = m j → t i = t j) (j : κ) :
    selectedValue m t (m j) = t j := by
  classical
  rw [selectedValue, dif_pos (show ∃ i, m i = m j from ⟨j, rfl⟩)]
  apply hc
  exact Classical.choose_spec (show ∃ i, m i = m j from ⟨j, rfl⟩)

/-- Complete feasibility classification for arbitrary finite conductor requests. -/
theorem feasible_iff (n : ℕ) (m : κ → ℕ) (hm : ∀ j, 1 < m j) (t : κ → ℝ) :
    (∃ a : Fin n → ℝ, ∀ j, packetMultipleTransform n a (m j) = t j) ↔
      Compatible n m t := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    constructor
    · intro i j hij
      rw [← ha i, ← ha j, hij]
    · intro j hj
      have h := ha j
      rw [coordinateSource_pairing, coordinateSource_eq_zero_of_large n (m j) hj] at h
      simpa using h.symm
  · rintro ⟨hc, ho⟩
    let c : Fin n → ℝ := fun i => selectedValue m t (i.val + 2)
    let f : ThresholdHilbert := ∑ i : Fin n, c i • residueAtom i.val
    have hf : f ∈ Submodule.span ℝ
        (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))) := by
      rw [finitePacket_span_eq]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [← Fintype.range_linearCombination] at hf
    obtain ⟨a, ha⟩ := hf
    refine ⟨a, ?_⟩
    intro j
    by_cases hj : m j ≤ n + 1
    · let i : Fin n := ⟨m j - 2, by have := hm j; omega⟩
      have hi : i.val + 2 = m j := by dsimp [i]; have := hm j; omega
      rw [← coefficient_packet_synthesis n a (m j) (hm j), ha]
      have hcoord := coefficient_finite_sum n c i
      rw [hi] at hcoord
      change coefficientCLM (m j) f = c i at hcoord
      rw [hcoord]
      change selectedValue m t (i.val + 2) = t j
      rw [hi]
      exact selectedValue_at m t hc j
    · rw [coordinateSource_pairing,
        coordinateSource_eq_zero_of_large n (m j) (by omega), ho j (by omega)]
      simp

def sources (n : ℕ) (m : κ → ℕ) (j : κ) : Fin n → ℝ := coordinateSource n (m j)

def rows (n : ℕ) (m : κ → ℕ) : κ → ThresholdHilbert :=
  sourceRows (finitePacket_independent n) (sources n m)

/-- This characterizes exactly when the source Gram inverse is available. -/
theorem rows_independent_iff (n : ℕ) (m : κ → ℕ) (hm : ∀ j, 1 < m j) :
    LinearIndependent ℝ (rows n m) ↔
      Function.Injective m ∧ ∀ j, m j ≤ n + 1 := by
  classical
  constructor
  · intro hr
    constructor
    · intro i j hij
      apply hr.injective
      simp only [rows, sourceRows, sources, hij]
    · intro j
      by_contra hj
      have hz : rows n m j = 0 := by
        simp only [rows, sources, sourceRows,
          coordinateSource_eq_zero_of_large n (m j) (by omega), minimumVector, map_zero]
      exact (LinearIndependent.ne_zero j hr) hz
  · rintro ⟨hinj, hstage⟩
    let e : κ ↪ Fin n :=
      { toFun := fun j => ⟨m j - 2, by have := hm j; have := hstage j; omega⟩
        inj' := by
          intro i j hij
          apply hinj
          have he := congrArg Fin.val hij
          dsimp at he
          have := hm i
          have := hm j
          omega }
    have he : ∀ j, (e j).val + 2 = m j := by
      intro j
      change m j - 2 + 2 = m j
      have := hm j
      omega
    have hsame : rows n m = RamanujanMultipleConstraints.rows n e := by
      funext j
      simp only [rows, sourceRows, sources, RamanujanMultipleConstraints.rows,
        RamanujanMultipleConstraints.sources, he]
    rw [hsame]
    exact RamanujanMultipleConstraints.rows_independent n e

def defect (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (j : κ) : ℝ :=
  t j - packetMultipleCoefficient n (m j)

theorem mismatch_eq (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) :
    mismatch (finitePacket_independent n) (sources n m) hilbertOne t = defect n m t := by
  funext j
  unfold mismatch defect packetMultipleCoefficient
  rw [coordinateSource_pairing]
  rfl

/-- Source-normal multipliers, possibly nonunique, give a unique legal optimizer. -/
def optimizerCoefficients (n : ℕ) (m : κ → ℕ) (d : κ → ℝ) : Fin n → ℝ :=
  normalCoefficients (finitePacket_independent n) (sources n m) hilbertOne d

def IsNormal (n : ℕ) (m : κ → ℕ) (t d : κ → ℝ) : Prop :=
  ∀ j, inner ℝ (rows n m j) (Fintype.linearCombination ℝ (rows n m) d) = defect n m t j

/-- The singular source Gram is solvable exactly under elementary arithmetic compatibility. -/
theorem normal_exists_iff (n : ℕ) (m : κ → ℕ) (hm : ∀ j, 1 < m j) (t : κ → ℝ) :
    (∃ d : κ → ℝ, IsNormal n m t d) ↔ Compatible n m t := by
  constructor
  · rintro ⟨d, hd⟩
    apply (feasible_iff n m hm t).mp
    refine ⟨optimizerCoefficients n m d, ?_⟩
    intro j
    rw [coordinateSource_pairing]
    apply normalCoefficients_source (finitePacket_independent n) (sources n m) hilbertOne t d
    intro k
    rw [mismatch_eq]
    exact hd k
  · intro hc
    obtain ⟨a, ha⟩ := (feasible_iff n m hm t).mpr hc
    have hf : ∃ a : Fin n → ℝ, ∀ j, (∑ i, a i * sources n m j i) = t j := by
      refine ⟨a, ?_⟩
      intro j
      exact (coordinateSource_pairing n (m j) a).symm.trans (ha j)
    obtain ⟨d, hd⟩ := normal_exists (finitePacket_independent n) (sources n m) hilbertOne t hf
    refine ⟨d, ?_⟩
    intro j
    rw [mismatch_eq] at hd
    exact hd j

theorem optimizer_error_exact (n : ℕ) (m : κ → ℕ) (t d : κ → ℝ)
    (hd : IsNormal n m t d) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (optimizerCoefficients n m d)‖ ^ 2 =
      1 - packetMass n + ∑ j, d j * (t j - packetMultipleCoefficient n (m j)) := by
  have hn : ∀ j, inner ℝ (sourceRows (finitePacket_independent n) (sources n m) j)
      (Fintype.linearCombination ℝ (sourceRows (finitePacket_independent n) (sources n m)) d) =
        mismatch (finitePacket_independent n) (sources n m) hilbertOne t j := by
    rw [mismatch_eq]
    exact hd
  have h := normalCoefficients_energy (finitePacket_independent n) (sources n m) hilbertOne t d hn
  rw [mismatch_eq] at h
  change _ = ‖hilbertOne - packetCandidate n‖ ^ 2 + ∑ j, d j * defect n m t j at h
  rw [packet_error] at h
  exact h

theorem optimizer_completion (n : ℕ) (m : κ → ℕ) (t d : κ → ℝ)
    (hd : IsNormal n m t d) (a : Fin n → ℝ)
    (ha : ∀ j, packetMultipleTransform n a (m j) = t j) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
      1 - packetMass n + ∑ j, d j * (t j - packetMultipleCoefficient n (m j)) +
        ‖Fintype.linearCombination ℝ
          (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
          (a - optimizerCoefficients n m d)‖ ^ 2 := by
  have hn : ∀ j, inner ℝ (sourceRows (finitePacket_independent n) (sources n m) j)
      (Fintype.linearCombination ℝ (sourceRows (finitePacket_independent n) (sources n m)) d) =
        mismatch (finitePacket_independent n) (sources n m) hilbertOne t j := by
    rw [mismatch_eq]
    exact hd
  have hc : ∀ j, (∑ i, a i * sources n m j i) = t j := by
    intro j
    exact (coordinateSource_pairing n (m j) a).symm.trans (ha j)
  have h := normalCoefficients_completion (finitePacket_independent n) (sources n m)
    hilbertOne t d hn a hc
  change _ = ‖hilbertOne - Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (optimizerCoefficients n m d)‖ ^ 2 + _ at h
  rw [optimizer_error_exact n m t d hd] at h
  exact h

theorem optimizer_optimal_iff (n : ℕ) (m : κ → ℕ) (t d : κ → ℝ)
    (hd : IsNormal n m t d) (a : Fin n → ℝ)
    (ha : ∀ j, packetMultipleTransform n a (m j) = t j) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
      1 - packetMass n + ∑ j, d j * (t j - packetMultipleCoefficient n (m j)) ↔
        a = optimizerCoefficients n m d := by
  constructor
  · intro he
    have ht := optimizer_completion n m t d hd a ha
    have hz : ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - optimizerCoefficients n m d)‖ ^ 2 = 0 := by linarith
    have hz' := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have hcoeff : a - optimizerCoefficients n m d = 0 := by
      apply (finitePacket_independent n).fintypeLinearCombination_injective
      simpa only [map_zero] using hz'
    exact sub_eq_zero.mp hcoeff
  · rintro rfl
    exact optimizer_error_exact n m t d hd

/-- Exact negative-Moebius pinning may include an offstage conductor precisely
when its target value is zero; repeated conductor requests are automatic. -/
theorem moebius_feasible_iff (n : ℕ) (m : κ → ℕ) (hm : ∀ j, 1 < m j) :
    (∃ a : Fin n → ℝ, ∀ j,
      packetMultipleTransform n a (m j) = -(ArithmeticFunction.moebius (m j) : ℝ)) ↔
      ∀ j, n + 1 < m j → (ArithmeticFunction.moebius (m j) : ℝ) = 0 := by
  rw [feasible_iff n m hm]
  constructor
  · rintro ⟨_, ho⟩ j hj
    exact neg_eq_zero.mp (ho j hj)
  · intro ho
    constructor
    · intro i j hij
      change -(ArithmeticFunction.moebius (m i) : ℝ) =
        -(ArithmeticFunction.moebius (m j) : ℝ)
      rw [hij]
    · intro j hj
      change -(ArithmeticFunction.moebius (m j) : ℝ) = 0
      rw [ho j hj, neg_zero]

end RiemannResearch.RH.RamanujanConstraintFeasibility
