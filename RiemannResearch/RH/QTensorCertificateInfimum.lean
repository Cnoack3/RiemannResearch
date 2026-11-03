/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTensorCertificate
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QCovarianceInverse
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Genuine certificate infima and conditional RH implications

Source: user-provided PrimeTensorCRTResults20261102.md, sections 3--5,
and the user's request to prove the infimum RH implicator. The order-theoretic
argument uses nonempty sets bounded below; no attainment is assumed.

B. Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis", Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006),
137--146, Remark 8 and the equivalent-weight discussion after Theorem 1:
https://arxiv.org/pdf/math/0607733. This supports the squarefree-closure
context. The RH implication here uses the existing checked repository
consumer. No RH-to-density analytic provider is introduced.

The anchored infimum equals the actual finite squarefree legal-error
infimum, because projected anchors recover each exact complete error.
Both infimum-to-RH theorems are CONDITIONAL RESEARCH REDUCTIONS.
OPEN: prove that either complete certificate infimum is zero.
The unconditional benchmark below is strictly below 59/1000, not zero.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTensorCertificate
open ZetaTwoHilbert ZetaTwoProbability QCovarianceInverse
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteTensorTail

def columnValues : Set ℝ := {x | ∃ m n : ℕ, ∃ r : Fin m → ℕ+,
  ∃ d : Fin n → {d : ℕ // 2 ≤ d ∧ Squarefree d}, ∃ c : Fin n → ℝ,
    Function.Injective r ∧ (∃ k, r k = 1) ∧
    certificate r (fun i => (d i).val) c = x}

def anchoredValues : Set ℝ := {x | ∃ m n : ℕ, ∃ r : Fin m → ℕ+,
  ∃ d : Fin n → {d : ℕ // 2 ≤ d ∧ Squarefree d}, ∃ c : Fin n → ℝ,
  ∃ b : Fin n → QHilbert,
    Function.Injective r ∧ (∃ k, r k = 1) ∧
    (∀ i, b i ∈ synthesisSpan (rows r)) ∧
    anchoredCertificate r (fun i => (d i).val) c b = x}

def legalErrorValues : Set ℝ := {x | ∃ n : ℕ,
  ∃ d : Fin n → {d : ℕ // 2 ≤ d ∧ Squarefree d}, ∃ c : Fin n → ℝ,
    ‖qOne - qSynthesis (fun i => (d i).val) c‖ ^ 2 = x}

def columnInfimum : ℝ := sInf columnValues
def anchoredInfimum : ℝ := sInf anchoredValues
def legalErrorInfimum : ℝ := sInf legalErrorValues

theorem columnValues_nonempty : columnValues.Nonempty := by
  let r : Fin 1 → ℕ+ := fun _ => 1
  let d : Fin 0 → {d : ℕ // 2 ≤ d ∧ Squarefree d} := Fin.elim0
  let c : Fin 0 → ℝ := fun _ => 0
  refine ⟨_, 1, 0, r, d, c, ?_, ?_, rfl⟩
  · intro i j _
    exact Subsingleton.elim i j
  · exact ⟨0, rfl⟩

theorem anchoredValues_nonempty : anchoredValues.Nonempty := by
  let r : Fin 1 → ℕ+ := fun _ => 1
  let d : Fin 0 → {d : ℕ // 2 ≤ d ∧ Squarefree d} := Fin.elim0
  let c : Fin 0 → ℝ := fun _ => 0
  let b : Fin 0 → QHilbert := fun _ => 0
  refine ⟨_, 1, 0, r, d, c, b, ?_, ?_, ?_, rfl⟩
  · intro i j _
    exact Subsingleton.elim i j
  · exact ⟨0, rfl⟩
  · intro i
    exact (synthesisSpan (rows r)).zero_mem

theorem legalErrorValues_nonempty : legalErrorValues.Nonempty := by
  let d : Fin 0 → {d : ℕ // 2 ≤ d ∧ Squarefree d} := Fin.elim0
  let c : Fin 0 → ℝ := fun _ => 0
  exact ⟨_, 0, d, c, rfl⟩

theorem columnValues_nonneg {x : ℝ} (hx : x ∈ columnValues) : 0 ≤ x := by
  obtain ⟨m, n, r, d, c, hr, hone, rfl⟩ := hx
  exact (sq_nonneg _).trans (error_le_certificate r hr hone _ c)

theorem anchoredValues_nonneg {x : ℝ} (hx : x ∈ anchoredValues) : 0 ≤ x := by
  obtain ⟨m, n, r, d, c, b, hr, hone, hb, rfl⟩ := hx
  exact (sq_nonneg _).trans (error_le_anchoredCertificate r hr hone _ c b hb)

theorem legalErrorValues_nonneg {x : ℝ} (hx : x ∈ legalErrorValues) : 0 ≤ x := by
  obtain ⟨n, d, c, rfl⟩ := hx
  exact sq_nonneg _

private theorem nonnegative_sInf_zero_iff (s : Set ℝ) (hs : s.Nonempty)
    (hn : ∀ x ∈ s, 0 ≤ x) :
    sInf s = 0 ↔ ∀ ε : ℝ, 0 < ε → ∃ x ∈ s, x < ε := by
  have hb : BddBelow s := ⟨0, hn⟩
  have hi : 0 ≤ sInf s := le_csInf hs hn
  constructor
  · intro h ε hε
    by_contra hx
    have hlow : ε ≤ sInf s := by
      apply le_csInf hs
      intro x hxmem
      by_contra hlt
      exact hx ⟨x, hxmem, lt_of_not_ge hlt⟩
    linarith
  · intro h
    apply le_antisymm _ hi
    by_contra hx
    have hp : 0 < sInf s := lt_of_not_ge hx
    obtain ⟨x, hxmem, hlt⟩ := h (sInf s) hp
    have hlow := csInf_le hb hxmem
    linarith

theorem columnInfimum_eq_zero_iff :
    columnInfimum = 0 ↔ ArbitrarilySmallCertificates := by
  rw [columnInfimum, nonnegative_sInf_zero_iff columnValues
    columnValues_nonempty (fun _ hx => columnValues_nonneg hx)]
  constructor
  · intro h ε hε
    obtain ⟨x, ⟨m, n, r, d, c, hr, hone, rfl⟩, hx⟩ := h ε hε
    exact ⟨m, n, r, d, c, hr, hone, hx⟩
  · intro h ε hε
    obtain ⟨m, n, r, d, c, hr, hone, hc⟩ := h ε hε
    exact ⟨_, ⟨m, n, r, d, c, hr, hone, rfl⟩, hc⟩

theorem anchoredInfimum_eq_zero_iff :
    anchoredInfimum = 0 ↔ ArbitrarilySmallAnchoredCertificates := by
  rw [anchoredInfimum, nonnegative_sInf_zero_iff anchoredValues
    anchoredValues_nonempty (fun _ hx => anchoredValues_nonneg hx)]
  constructor
  · intro h ε hε
    obtain ⟨x, ⟨m, n, r, d, c, b, hr, hone, hb, rfl⟩, hx⟩ := h ε hε
    exact ⟨m, n, r, d, c, b, hr, hone, hb, hx⟩
  · intro h ε hε
    obtain ⟨m, n, r, d, c, b, hr, hone, hb, hc⟩ := h ε hε
    exact ⟨_, ⟨m, n, r, d, c, b, hr, hone, hb, rfl⟩, hc⟩

theorem riemannHypothesis_of_columnInfimum_zero (h : columnInfimum = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_certificates (columnInfimum_eq_zero_iff.mp h)

theorem riemannHypothesis_of_anchoredInfimum_zero (h : anchoredInfimum = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_anchoredCertificates (anchoredInfimum_eq_zero_iff.mp h)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def projectionAnchors (r : κ → ℕ+) (d : ι → ℕ) : ι → QHilbert :=
  fun i => (synthesisSpan (rows r)).starProjection (qResidue (d i))

omit [Fintype ι] in
theorem projectionAnchors_mem (r : κ → ℕ+) (hr : Function.Injective r)
    (d : ι → ℕ) (i : ι) :
    projectionAnchors r d i ∈ synthesisSpan (rows r) := by
  rw [projectionAnchors, projection_eq_orthonormal_sum (rows_orthonormal r hr)]
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨k, rfl⟩

theorem anchoredCertificate_projection_eq_error (r : κ → ℕ+)
    (hr : Function.Injective r) (hone : ∃ k, r k = 1)
    (d : ι → ℕ) (c : ι → ℝ) :
    anchoredCertificate r d c (projectionAnchors r d) =
      ‖qOne - qSynthesis d c‖ ^ 2 := by
  rw [anchoredCertificate_eq_error_add_bias r hr hone d c _
    (projectionAnchors_mem r hr d)]
  have hB : Fintype.linearCombination ℝ (projectionAnchors r d) c =
      (synthesisSpan (rows r)).starProjection (qSynthesis d c) := by
    simp only [Fintype.linearCombination_apply, projectionAnchors, qSynthesis,
      map_sum, map_smul]
  have hinner (k : κ) : inner ℝ (rows r k)
      (qSynthesis d c - Fintype.linearCombination ℝ (projectionAnchors r d) c) = 0 := by
    rw [hB, inner_sub_right,
      projection_eq_orthonormal_sum (rows_orthonormal r hr),
      (rows_orthonormal r hr).inner_right_fintype, sub_self]
  simp only [hinner, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero]


theorem columnValues_bddBelow : BddBelow columnValues :=
  ⟨0, fun _ hx => columnValues_nonneg hx⟩

theorem anchoredValues_bddBelow : BddBelow anchoredValues :=
  ⟨0, fun _ hx => anchoredValues_nonneg hx⟩

theorem legalErrorValues_bddBelow : BddBelow legalErrorValues :=
  ⟨0, fun _ hx => legalErrorValues_nonneg hx⟩

theorem columnInfimum_nonneg : 0 ≤ columnInfimum :=
  le_csInf columnValues_nonempty (fun _ hx => columnValues_nonneg hx)

theorem anchoredInfimum_nonneg : 0 ≤ anchoredInfimum :=
  le_csInf anchoredValues_nonempty (fun _ hx => anchoredValues_nonneg hx)

theorem legalErrorInfimum_nonneg : 0 ≤ legalErrorInfimum :=
  le_csInf legalErrorValues_nonempty (fun _ hx => legalErrorValues_nonneg hx)

theorem legalErrorInfimum_le_error (n : ℕ)
    (d : Fin n → {d : ℕ // 2 ≤ d ∧ Squarefree d}) (c : Fin n → ℝ) :
    legalErrorInfimum ≤ ‖qOne - qSynthesis (fun i => (d i).val) c‖ ^ 2 :=
  csInf_le legalErrorValues_bddBelow ⟨n, d, c, rfl⟩

/-- No attainment of the global infimum is asserted. A single constant
analysis row suffices for exact anchoring of each fixed legal synthesis. -/
theorem anchoredInfimum_le_error (n : ℕ)
    (d : Fin n → {d : ℕ // 2 ≤ d ∧ Squarefree d}) (c : Fin n → ℝ) :
    anchoredInfimum ≤ ‖qOne - qSynthesis (fun i => (d i).val) c‖ ^ 2 := by
  let r : Fin 1 → ℕ+ := fun _ => 1
  have hr : Function.Injective r := fun i j _ => Subsingleton.elim i j
  have hone : ∃ k, r k = 1 := ⟨0, rfl⟩
  let b := projectionAnchors r (fun i => (d i).val)
  have hb : ∀ i, b i ∈ synthesisSpan (rows r) :=
    projectionAnchors_mem r hr (fun i => (d i).val)
  have hm : anchoredCertificate r (fun i => (d i).val) c b ∈ anchoredValues :=
    ⟨1, n, r, d, c, b, hr, hone, hb, rfl⟩
  have hlow := csInf_le anchoredValues_bddBelow hm
  simpa only [anchoredInfimum, b, anchoredCertificate_projection_eq_error r hr hone] using hlow

/-- Optimizing the anchor certificate is exactly the actual legal-error
optimization. In particular, free anchor choices do not prove its value is zero. -/
theorem anchoredInfimum_eq_legalErrorInfimum :
    anchoredInfimum = legalErrorInfimum := by
  apply le_antisymm
  · apply le_csInf legalErrorValues_nonempty
    rintro x ⟨n, d, c, rfl⟩
    exact anchoredInfimum_le_error n d c
  · apply le_csInf anchoredValues_nonempty
    rintro x ⟨m, n, r, d, c, b, hr, hone, hb, rfl⟩
    exact (legalErrorInfimum_le_error n d c).trans
      (error_le_anchoredCertificate r hr hone _ c b hb)

theorem legalErrorInfimum_le_columnInfimum :
    legalErrorInfimum ≤ columnInfimum := by
  apply le_csInf columnValues_nonempty
  rintro x ⟨m, n, r, d, c, hr, hone, rfl⟩
  exact (legalErrorInfimum_le_error n d c).trans
    (error_le_certificate r hr hone _ c)

/-- Conditional research reduction: the zero-infimum equality is the
single remaining arithmetic premise. -/
theorem riemannHypothesis_of_legalErrorInfimum_zero (h : legalErrorInfimum = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_anchoredInfimum_zero
    (anchoredInfimum_eq_legalErrorInfimum.trans h)

/-- The previously checked rational benchmark supplies an unconditional,
strictly positive numerical upper bound, not a zero-infimum theorem. -/
theorem legalErrorInfimum_lt_benchmark :
    legalErrorInfimum < (59 : ℝ) / 1000 := by
  have h2 : Squarefree (2 : ℕ) := by
    intro m hm
    have hle : m ≤ 2 := Nat.le_of_dvd (by decide)
      (dvd_trans (dvd_mul_right m m) hm)
    interval_cases m <;> norm_num at *
  have h3 : Squarefree (3 : ℕ) := by
    intro m hm
    have hle : m ≤ 3 := Nat.le_of_dvd (by decide)
      (dvd_trans (dvd_mul_right m m) hm)
    interval_cases m <;> norm_num at *
  have h6 : Squarefree (6 : ℕ) := by
    intro m hm
    have hle : m ≤ 6 := Nat.le_of_dvd (by decide)
      (dvd_trans (dvd_mul_right m m) hm)
    interval_cases m <;> norm_num at *
  let d : Fin 3 → {d : ℕ // 2 ≤ d ∧ Squarefree d} :=
    ![⟨2, ⟨by decide, h2⟩⟩, ⟨3, ⟨by decide, h3⟩⟩, ⟨6, ⟨by decide, h6⟩⟩]
  let c : Fin 3 → ℝ :=
    ![1045918 / 1000000, 1069558 / 1000000, 604750 / 1000000]
  have he : qOne - qSynthesis (fun i => (d i).val) c = Benchmark.errorVector := by
    simp [qSynthesis, d, c, Fin.sum_univ_succ, Benchmark.errorVector, add_assoc]
  have hi := legalErrorInfimum_le_error 3 d c
  rw [he] at hi
  exact hi.trans_lt Benchmark.complete_norm_lt

theorem anchoredInfimum_lt_benchmark :
    anchoredInfimum < (59 : ℝ) / 1000 := by
  rw [anchoredInfimum_eq_legalErrorInfimum]
  exact legalErrorInfimum_lt_benchmark

end RiemannResearch.RH.QTensorCertificate
