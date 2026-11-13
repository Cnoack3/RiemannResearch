/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.LinearAlgebra.CenteredNormalEquations
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QOptimizerParity
import RiemannResearch.RH.QCRTNestedCutoffs
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QDivisibilityResidueCoefficients
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Data.Nat.Factorial.Basic
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QCRTLeakageParseval
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# CRT Gram decomposition and the actual inverse-Gram saturation limit

Source: the user's CRT, orthonormal-basis, and Parseval investigation,
13 November 2026.

For the full residue family with conductors 2 through N+1, the complete
Gram matrix splits into its retained divisor-CRT rows and complementary
rows. Both energies are retained. The actual inverse-Gram optimizer has
saturation tending to the squared norm of the projection of one onto the
closed legal residue span.

Along every nested cofinal CRT tower, the omitted energy of these moving
optimizers tends to zero unconditionally. The retained error tends to the
full limiting residual energy. Its zero limit is equivalent to legal
closure membership and is an explicit hypothesis of the RH consumer.

This module does not identify the unaugmented legal span with the
density-augmented span and does not assert unconditional saturation to one.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix
namespace RiemannResearch.RH.QCRTGramSaturation
open ZetaTwoHilbert QCovarianceInverse QCovarianceInvertibility
open QFullResidueProjection QDivisorHilbert QDivisibilityDensity
open QCRTFiniteCollocation
open RiemannResearch.LinearAlgebra.CenteredNormalEquations
open RiemannResearch.Analysis.FiniteHilbertGram

def saturation (n : ℕ) : ℝ :=
  dotProduct (qMean (conductor n))
    ((residueGramMatrix (conductor n))⁻¹.mulVec (qMean (conductor n)))

theorem saturation_eq_norm_sq (n : ℕ) :
    saturation n = ‖candidate n‖ ^ 2 := by
  change dot (qMean (conductor n)) (coefficients n) =
    ‖qSynthesis (conductor n) (coefficients n)‖ ^ 2
  rw [qSynthesis_norm_sq, quadratic,
    show action (qGram (conductor n)) (coefficients n) = qMean (conductor n)
      from funext (coefficients_normal n), dot_comm]

theorem error_identity (n : ℕ) :
    ‖qOne - candidate n‖ ^ 2 = 1 - saturation n := by
  exact qError_gram_solution (conductor n) (coefficients n) (coefficients_normal n)

theorem saturation_tendsto :
    Tendsto saturation atTop (𝓝 (‖closure.starProjection qOne‖ ^ 2)) := by
  simpa only [← saturation_eq_norm_sq] using
    candidate_tendsto_projection.norm.pow 2

def defect : QHilbert := qOne - closure.starProjection qOne

theorem error_tendsto :
    Tendsto (fun n => 1 - saturation n) atTop (𝓝 (‖defect‖ ^ 2)) := by
  have h := ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => qOne) atTop (𝓝 qOne)).sub
      candidate_tendsto_projection).norm.pow 2
  simpa only [error_identity, defect] using h

theorem defect_norm_sq :
    ‖defect‖ ^ 2 = 1 - ‖closure.starProjection qOne‖ ^ 2 := by
  have h := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem qOne)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) qOne)
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [defect, norm_sub_sq_real, qOne_norm_sq]
  nlinarith [real_inner_comm qOne (closure.starProjection qOne)]

theorem saturation_tendsto_one_iff :
    Tendsto saturation atTop (𝓝 1) ↔ qOne ∈ closure := by
  constructor
  · intro h
    have he : ‖closure.starProjection qOne‖ ^ 2 = 1 :=
      tendsto_nhds_unique saturation_tendsto h
    have hz : ‖defect‖ ^ 2 = 0 := by rw [defect_norm_sq, he]; ring
    have hd : defect = 0 := norm_eq_zero.mp (by
      nlinarith [norm_nonneg defect])
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hd).symm
  · intro h
    simpa only [← saturation_eq_norm_sq, qOne_norm_sq] using
      (candidate_tendsto_qOne h).norm.pow 2

theorem gram_parseval (n : ℕ) (i j : Fin n) :
    residueGramMatrix (conductor n) i j =
      ∑' r : ℕ+, qResidueDivisorCoefficient (conductor n i) r *
        qResidueDivisorCoefficient (conductor n j) r /
          qJordanTwo r := by
  exact (qResidue_gram_parseval (conductor n i) (conductor n j)).symm

theorem error_parseval (n : ℕ) :
    1 - saturation n =
      ∑' r : ℕ+, ((if r = 1 then (1 : ℝ) else 0) -
        ∑ i : Fin n, coefficients n i *
          qResidueDivisorCoefficient (conductor n i) r) ^ 2 /
            qJordanTwo r := by
  rw [← error_identity]
  exact (qSynthesis_error_parseval (conductor n) (coefficients n)).symm

theorem limiting_defect_parseval :
    1 - ‖closure.starProjection qOne‖ ^ 2 =
      ∑' r : ℕ+, (inner ℝ defect (divisorWavelet r)) ^ 2 /
        qJordanTwo r := by
  rw [← defect_norm_sq]
  exact (divisorWavelet_parseval_norm defect).symm

theorem inner_crt_split (L : ℕ) (x y : QHilbert) :
    inner ℝ x y =
      inner ℝ (conditionalProjection L x) (conditionalProjection L y) +
      inner ℝ (x - conditionalProjection L x) (y - conditionalProjection L y) := by
  have h1 := conditional_inner L x (conditionalProjection L y)
    ((cellSpace L).starProjection_apply_mem y)
  have h2 := conditional_inner L y (conditionalProjection L x)
    ((cellSpace L).starProjection_apply_mem x)
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  nlinarith [real_inner_comm (conditionalProjection L y) (conditionalProjection L x),
    real_inner_comm y (conditionalProjection L x)]

def headGram (L n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  inner ℝ (conditionalProjection L (qResidue (conductor n i)))
    (conditionalProjection L (qResidue (conductor n j)))

def tailGram (L n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  inner ℝ (qResidue (conductor n i) - conditionalProjection L (qResidue (conductor n i)))
    (qResidue (conductor n j) - conditionalProjection L (qResidue (conductor n j)))

theorem gram_crt_split (L n : ℕ) :
    residueGramMatrix (conductor n) = headGram L n + tailGram L n := by
  ext i j
  exact inner_crt_split L (qResidue (conductor n i)) (qResidue (conductor n j))

theorem tail_quadratic (L n : ℕ) (c : Fin n → ℝ) :
    dotProduct c ((tailGram L n).mulVec c) =
      ‖∑ i : Fin n, c i •
        (qResidue (conductor n i) - conditionalProjection L (qResidue (conductor n i)))‖ ^ 2 := by
  exact (gramMatrix_quadratic
    (fun i : Fin n => qResidue (conductor n i) -
      conditionalProjection L (qResidue (conductor n i))) c).symm

theorem error_crt_split (L n : ℕ) (hL : 0 < L) :
    1 - saturation n =
      ‖qOne - conditionalProjection L (candidate n)‖ ^ 2 +
      ‖candidate n - conditionalProjection L (candidate n)‖ ^ 2 := by
  have h := inner_crt_split L (qOne - candidate n) (qOne - candidate n)
  have hone : conditionalProjection L qOne = qOne :=
    Submodule.starProjection_eq_self_iff.mpr (qOne_mem_cell L hL)
  have he : (qOne - candidate n) -
      conditionalProjection L (qOne - candidate n) =
      -(candidate n - conditionalProjection L (candidate n)) := by
    rw [map_sub, hone]
    abel
  rw [real_inner_self_eq_norm_sq, he, real_inner_self_eq_norm_sq,
    map_sub, hone, real_inner_self_eq_norm_sq, norm_neg, error_identity] at h
  exact h


/-- The CRT cell spaces exhaust the ambient space; this is not legal density. -/
theorem cell_closure_iSup_eq_top (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n) :
    (⨆ n, cellSpace (L n)).topologicalClosure = ⊤ := by
  have hle : Submodule.span ℝ (Set.range (fun r : ℕ+ => divisorWavelet (r : ℕ))) ≤
      ⨆ n, cellSpace (L n) := by
    apply Submodule.span_le.mpr
    rintro x ⟨r, rfl⟩
    obtain ⟨n, hn⟩ := hcover r r.pos
    exact le_iSup (fun n => cellSpace (L n)) n
      (QCRTLeakageParseval.wavelet_mem_cell (L n) (hpos n) r hn)
  have hc := Submodule.topologicalClosure_mono hle
  rw [divisorWavelet_span_dense] at hc
  exact le_antisymm le_top hc

theorem conditionalProjection_tendsto (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n) (f : QHilbert) :
    Tendsto (fun n => conditionalProjection (L n) f) atTop (𝓝 f) := by
  have hm : Monotone (fun n => cellSpace (L n)) := fun i j hij =>
    QCRTNestedCutoffs.cellSpace_mono_of_dvd (L i) (L j) (hpos j) (hnest i j hij)
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun n => cellSpace (L n)) hm f
  have htop : (⊤ : Submodule ℝ QHilbert).starProjection f = f :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_top)
  simpa only [conditionalProjection, cell_closure_iSup_eq_top L hpos hcover,
    htop] using h

theorem conditional_tail_norm_le (L : ℕ) (f : QHilbert) :
    ‖f - conditionalProjection L f‖ ≤ ‖f‖ := by
  have h := inner_crt_split L f f
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg f, norm_nonneg (f - conditionalProjection L f),
    sq_nonneg ‖conditionalProjection L f‖]

/-- Strongly convergent vectors have vanishing tails along a cofinal CRT tower. -/
theorem moving_conditional_tail_tendsto (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n)
    {f : ℕ → QHilbert} {v : QHilbert} (hf : Tendsto f atTop (𝓝 v)) :
    Tendsto (fun n => ‖f n - conditionalProjection (L n) (f n)‖) atTop (𝓝 0) := by
  have hb (n : ℕ) :
      ‖f n - conditionalProjection (L n) (f n)‖ ≤
        ‖f n - v‖ + ‖v - conditionalProjection (L n) v‖ := by
    have he : f n - conditionalProjection (L n) (f n) =
        ((f n - v) - conditionalProjection (L n) (f n - v)) +
          (v - conditionalProjection (L n) v) := by
      rw [map_sub]
      abel
    rw [he]
    exact (norm_add_le _ _).trans
      (_root_.add_le_add (conditional_tail_norm_le (L n) (f n - v)) le_rfl)
  apply squeeze_zero (fun n => norm_nonneg _) hb
  have h1 : Tendsto (fun n => ‖f n - v‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hf.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => v) atTop (𝓝 v))).norm
  have h2 : Tendsto (fun n => ‖v - conditionalProjection (L n) v‖)
      atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => v) atTop (𝓝 v)).sub
        (conditionalProjection_tendsto L hpos hnest hcover v)).norm
  simpa using h1.add h2

/-- No arithmetic provider is needed for the moving CRT tail of the actual minimizers. -/
theorem candidate_crt_tail_tendsto_zero (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n) :
    Tendsto (fun n => ‖candidate n - conditionalProjection (L n) (candidate n)‖ ^ 2)
      atTop (𝓝 0) := by
  simpa using (moving_conditional_tail_tendsto L hpos hnest hcover
    candidate_tendsto_projection).pow 2

/-- The visible CRT head converges to the full residual energy, not automatically zero. -/
theorem candidate_crt_head_tendsto (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n) :
    Tendsto (fun n => ‖qOne - conditionalProjection (L n) (candidate n)‖ ^ 2)
      atTop (𝓝 (‖defect‖ ^ 2)) := by
  have he :
      (fun n => ‖qOne - conditionalProjection (L n) (candidate n)‖ ^ 2) =
      (fun n => (1 - saturation n) -
        ‖candidate n - conditionalProjection (L n) (candidate n)‖ ^ 2) := by
    funext n
    linarith [error_crt_split (L n) n (hpos n)]
  rw [he]
  simpa using error_tendsto.sub
    (candidate_crt_tail_tendsto_zero L hpos hnest hcover)

theorem candidate_factorial_crt_tail_tendsto_zero :
    Tendsto (fun n => ‖candidate n -
      conditionalProjection n.factorial (candidate n)‖ ^ 2) atTop (𝓝 0) := by
  apply candidate_crt_tail_tendsto_zero (fun n => n.factorial)
    Nat.factorial_pos
    (fun i j hij => Nat.factorial_dvd_factorial hij)
  intro m hm
  exact ⟨m, Nat.dvd_factorial hm le_rfl⟩

theorem candidate_tail_parseval (L n : ℕ) (hL : 0 < L) :
    ‖candidate n - conditionalProjection L (candidate n)‖ ^ 2 =
      ∑' r : ℕ+, if (r : ℕ) ∣ L then 0 else
        (inner ℝ (candidate n) (divisorWavelet r)) ^ 2 / qJordanTwo r := by
  rw [← divisorWavelet_parseval_norm]
  apply tsum_congr
  intro r
  rw [inner_sub_left, QCRTLeakageParseval.conditional_wavelet_coordinate L hL]
  split_ifs <;> simp

theorem headGram_parseval (L n : ℕ) (hL : 0 < L) (i j : Fin n) :
    headGram L n i j =
      ∑' r : ℕ+, if (r : ℕ) ∣ L then
        qResidueDivisorCoefficient (conductor n i) r *
          qResidueDivisorCoefficient (conductor n j) r / qJordanTwo r else 0 := by
  rw [headGram, ← divisorWavelet_parseval_inner]
  apply tsum_congr
  intro r
  have hrev : inner ℝ (divisorWavelet r)
      (conditionalProjection L (qResidue (conductor n j))) =
      inner ℝ (conditionalProjection L (qResidue (conductor n j)))
        (divisorWavelet r) := real_inner_comm _ _
  rw [hrev, QCRTLeakageParseval.conditional_wavelet_coordinate L hL,
    QCRTLeakageParseval.conditional_wavelet_coordinate L hL]
  split_ifs <;> simp [qResidue_divisorWavelet_inner]


/-- The requested projection-energy gap vanishes without a legal-density assumption. -/
theorem projection_energy_gap_tendsto_zero :
    Tendsto (fun n => ‖closure.starProjection qOne‖ ^ 2 - saturation n)
      atTop (𝓝 0) := by
  simpa only [sub_self] using
    ((tendsto_const_nhds : Tendsto
      (fun _ : ℕ => ‖closure.starProjection qOne‖ ^ 2)
      atTop (𝓝 (‖closure.starProjection qOne‖ ^ 2))).sub saturation_tendsto)

/-- Matrix quadratic form for the retained CRT component of the actual minimizer. -/
theorem candidate_head_quadratic (L n : ℕ) :
    dotProduct (coefficients n) ((headGram L n).mulVec (coefficients n)) =
      ‖conditionalProjection L (candidate n)‖ ^ 2 := by
  have h := (gramMatrix_quadratic
    (fun i : Fin n => conditionalProjection L (qResidue (conductor n i)))
      (coefficients n)).symm
  change dotProduct (coefficients n) ((headGram L n).mulVec (coefficients n)) =
    ‖∑ i : Fin n, coefficients n i •
      conditionalProjection L (qResidue (conductor n i))‖ ^ 2 at h
  simpa only [candidate, qSynthesis, map_sum, map_smul] using h

/-- Matrix quadratic form for the omitted CRT component of the actual minimizer. -/
theorem candidate_tail_quadratic (L n : ℕ) :
    dotProduct (coefficients n) ((tailGram L n).mulVec (coefficients n)) =
      ‖candidate n - conditionalProjection L (candidate n)‖ ^ 2 := by
  simpa only [candidate, qSynthesis, map_sum, map_smul,
    smul_sub, Finset.sum_sub_distrib] using tail_quadratic L n (coefficients n)

/-- Retained error written entirely in terms of the coefficient vector and matrices. -/
def headEnergy (L n : ℕ) : ℝ :=
  1 - 2 * saturation n +
    dotProduct (coefficients n) ((headGram L n).mulVec (coefficients n))

theorem matrix_error_crt_split (L n : ℕ) :
    1 - saturation n = headEnergy L n +
      dotProduct (coefficients n) ((tailGram L n).mulVec (coefficients n)) := by
  have h := inner_crt_split L (candidate n) (candidate n)
  simp only [real_inner_self_eq_norm_sq] at h
  rw [← saturation_eq_norm_sq, ← candidate_head_quadratic,
    ← candidate_tail_quadratic] at h
  unfold headEnergy
  linarith

theorem headEnergy_eq_norm_sq (L n : ℕ) (hL : 0 < L) :
    headEnergy L n = ‖qOne - conditionalProjection L (candidate n)‖ ^ 2 := by
  have h1 := matrix_error_crt_split L n
  have h2 := error_crt_split L n hL
  rw [candidate_tail_quadratic] at h1
  linarith

/-- Vanishing omitted energy, with literal inverse-Gram coefficient vectors. -/
theorem matrix_tail_tendsto_zero (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n) :
    Tendsto (fun n => dotProduct (coefficients n)
      ((tailGram (L n) n).mulVec (coefficients n))) atTop (𝓝 0) := by
  simpa only [candidate_tail_quadratic] using
    candidate_crt_tail_tendsto_zero L hpos hnest hcover

theorem matrix_head_tendsto (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n) :
    Tendsto (fun n => headEnergy (L n) n) atTop (𝓝 (‖defect‖ ^ 2)) := by
  simpa only [headEnergy_eq_norm_sq _ _ (hpos _)] using
    candidate_crt_head_tendsto L hpos hnest hcover

theorem matrix_head_tendsto_zero_iff (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n) :
    Tendsto (fun n => headEnergy (L n) n) atTop (𝓝 0) ↔
      qOne ∈ closure := by
  constructor
  · intro h
    have hz : ‖defect‖ ^ 2 = 0 :=
      tendsto_nhds_unique (matrix_head_tendsto L hpos hnest hcover) h
    have hd : defect = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg defect])
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hd).symm
  · intro h
    have hd : defect = 0 := by
      rw [defect, Submodule.starProjection_eq_self_iff.mpr h, sub_self]
    simpa only [hd, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      matrix_head_tendsto L hpos hnest hcover

/-- A conditional RH consumer: the retained-mode zero limit remains an explicit hypothesis. -/
theorem riemannHypothesis_of_matrix_head_tendsto_zero (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n)
    (hhead : Tendsto (fun n => headEnergy (L n) n) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    ((matrix_head_tendsto_zero_iff L hpos hnest hcover).mp hhead)


/-- info: 'RiemannResearch.RH.QCRTGramSaturation.gram_crt_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gram_crt_split

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.saturation_tendsto_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saturation_tendsto_one_iff

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.matrix_tail_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms matrix_tail_tendsto_zero

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.riemannHypothesis_of_matrix_head_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_matrix_head_tendsto_zero

/-! Source: the user's retained-head obligation, 13 November 2026.
The exact identity is unconditional; small-certificate existence remains Open. -/

theorem candidate_constant_pairing (n : ℕ) :
    inner ℝ qOne (candidate n) = saturation n := by
  have h := error_identity n
  rw [norm_sub_sq_real, qOne_norm_sq, ← saturation_eq_norm_sq] at h
  linarith

theorem head_constant_mode_exact (L n : ℕ) (hL : 0 < L) :
    headEnergy L n = (1 - saturation n)^2 +
      ‖conditionalProjection L (candidate n) - saturation n • qOne‖^2 := by
  have hp := conditional_inner L (candidate n) qOne (qOne_mem_cell L hL)
  have hm : inner ℝ (conditionalProjection L (candidate n)) qOne = saturation n := by
    rw [hp, real_inner_comm]
    exact candidate_constant_pairing n
  have hm' : inner ℝ qOne (conditionalProjection L (candidate n)) = saturation n :=
    (real_inner_comm _ _).trans hm
  rw [headEnergy_eq_norm_sq L n hL]
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, qOne_norm_sq, inner_smul_right, hm, hm']
  ring

theorem head_constant_mode_bounds (L n : ℕ) (hL : 0 < L) :
    (1 - saturation n)^2 ≤ headEnergy L n ∧ headEnergy L n ≤ 1 - saturation n := by
  constructor
  · rw [head_constant_mode_exact L n hL]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have h := matrix_error_crt_split L n
    rw [candidate_tail_quadratic] at h
    linarith [sq_nonneg ‖candidate n - conditionalProjection L (candidate n)‖]

/-- Conditional reduction: cutoffs need not be nested or exhaustive. -/
theorem one_mem_of_cofinal_head_small
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ L : ℕ, 0 < L ∧ headEnergy L n < ε) : qOne ∈ closure := by
  have hz : (‖defect‖^2)^2 = 0 := by
    by_contra hn
    have hp : 0 < (‖defect‖^2)^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)
    have hf : ∃ᶠ n in atTop, (1 - saturation n)^2 ≤ (‖defect‖^2)^2 / 2 := by
      rw [frequently_atTop]
      intro N
      obtain ⟨n, hn, L, hL, he⟩ := hsmall ((‖defect‖^2)^2 / 2) (by positivity) N
      exact ⟨n, hn, ((head_constant_mode_bounds L n hL).1.trans_lt he).le⟩
    have hh := le_of_tendsto_of_frequently (error_tendsto.pow 2) hf
    linarith
  have hd : defect = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (sq_eq_zero_iff.mp hz))
  exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hd).symm

theorem riemannHypothesis_of_cofinal_head_small
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ L : ℕ, 0 < L ∧ headEnergy L n < ε) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure (one_mem_of_cofinal_head_small hsmall)

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.head_constant_mode_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms head_constant_mode_exact
/-- info: 'RiemannResearch.RH.QCRTGramSaturation.riemannHypothesis_of_cofinal_head_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_cofinal_head_small

/-!
Source: the user's retained-head criterion audit, 13 November 2026.
The cutoff-one identity identifies cofinal smallness with saturation exactly.
Positive cutoff restrictions do not provide a new arithmetic decay estimate.
The complete Gram tail and nonconstant retained energy remain explicit below.
-/

/-- The optimizer's cutoff-one projection is its saturation times one. -/
theorem candidate_projection_one (n : ℕ) :
    conditionalProjection 1 (candidate n) = saturation n • qOne := by
  rw [conditionalProjection_one, real_inner_comm, candidate_constant_pairing]

/-- The one-cell retained error is exactly the square of the saturation gap. -/
theorem headEnergy_one (n : ℕ) :
    headEnergy 1 n = (1 - saturation n)^2 := by
  rw [head_constant_mode_exact 1 n (by decide), candidate_projection_one]
  simp

/-- The complementary one-cell energy is retained exactly. -/
theorem tailEnergy_one (n : ℕ) :
    dotProduct (coefficients n) ((tailGram 1 n).mulVec (coefficients n)) =
      saturation n * (1 - saturation n) := by
  have h := matrix_error_crt_split 1 n
  rw [headEnergy_one] at h
  nlinarith

/-- The nonconstant retained modes and complete omitted modes sum to the optimizer variance. -/
theorem centered_head_tail_exact (L n : ℕ) (hL : 0 < L) :
    ‖conditionalProjection L (candidate n) - saturation n • qOne‖^2 +
      dotProduct (coefficients n) ((tailGram L n).mulVec (coefficients n)) =
      saturation n * (1 - saturation n) := by
  have h := matrix_error_crt_split L n
  rw [head_constant_mode_exact L n hL] at h
  nlinarith

/-- The one-cell cutoff minimizes the retained error over all positive cutoffs. -/
theorem headEnergy_one_le (L n : ℕ) (hL : 0 < L) :
    headEnergy 1 n ≤ headEnergy L n := by
  rw [headEnergy_one]
  exact (head_constant_mode_bounds L n hL).1

/-- Cofinal retained-head smallness is exactly the existing saturation condition. -/
theorem cofinal_head_small_iff_saturation :
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ L : ℕ, 0 < L ∧ headEnergy L n < ε) ↔
      Tendsto saturation atTop (𝓝 1) := by
  constructor
  · intro h
    exact saturation_tendsto_one_iff.mpr (one_mem_of_cofinal_head_small h)
  · intro hs ε hε N
    have hh : Tendsto (fun n => headEnergy 1 n) atTop (𝓝 0) := by
      simpa only [headEnergy_one, sub_self, zero_pow (by decide : 2 ≠ 0)]
        using ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hs).pow 2
    have he : ∀ᶠ n in atTop, headEnergy 1 n < ε :=
      (tendsto_order.1 hh).2 ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1 he
    exact ⟨max N K, le_max_left _ _, 1, by decide, hK _ (le_max_right _ _)⟩

/-- Cofinal retained-head smallness is exactly legal closure membership. -/
theorem cofinal_head_small_iff_one_mem :
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ L : ℕ, 0 < L ∧ headEnergy L n < ε) ↔ qOne ∈ closure :=
  cofinal_head_small_iff_saturation.trans saturation_tendsto_one_iff

/-- Any prescribed positive cutoff sequence gives the same zero-limit condition; no nesting is needed. -/
theorem headEnergy_tendsto_zero_iff_positive (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n) :
    Tendsto (fun n => headEnergy (L n) n) atTop (𝓝 0) ↔
      Tendsto saturation atTop (𝓝 1) := by
  constructor
  · intro h
    apply cofinal_head_small_iff_saturation.mp
    intro ε hε N
    have he : ∀ᶠ n in atTop, headEnergy (L n) n < ε :=
      (tendsto_order.1 h).2 ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1 he
    exact ⟨max N K, le_max_left _ _, L (max N K), hpos _, hK _ (le_max_right _ _)⟩
  · intro hs
    have he : Tendsto (fun n => 1 - saturation n) atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hs
    apply squeeze_zero _ (fun n => (head_constant_mode_bounds (L n) n (hpos n)).2) he
    intro n
    exact (sq_nonneg (1 - saturation n)).trans
      (head_constant_mode_bounds (L n) n (hpos n)).1

/-- Refining the CRT cutoff reveals an exact additional square at a fixed conductor stage. -/
theorem headEnergy_refinement_exact (L M n : ℕ) (hM : 0 < M)
    (hLM : L ∣ M) :
    headEnergy M n = headEnergy L n +
      ‖conditionalProjection M (candidate n) -
        conditionalProjection L (candidate n)‖^2 := by
  have hLmem := (cellSpace L).starProjection_apply_mem (candidate n)
  have hMmem := QCRTNestedCutoffs.cellSpace_mono_of_dvd L M hM hLM hLmem
  have h1 := conditional_inner M (candidate n)
    (conditionalProjection L (candidate n)) hMmem
  have h2 := conditional_inner L (candidate n)
    (conditionalProjection L (candidate n)) hLmem
  rw [real_inner_self_eq_norm_sq] at h2
  simp only [headEnergy, candidate_head_quadratic, norm_sub_sq_real]
  linarith

/-- The retained error increases under divisor refinement. -/
theorem headEnergy_mono_of_dvd (L M n : ℕ) (hM : 0 < M)
    (hLM : L ∣ M) : headEnergy L n ≤ headEnergy M n := by
  rw [headEnergy_refinement_exact L M n hM hLM]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- No finite conductor stage has zero retained error at a positive cutoff. -/
theorem headEnergy_pos (L n : ℕ) (hL : 0 < L) : 0 < headEnergy L n := by
  have he : 0 < 1 - saturation n := by
    rw [← error_identity]
    exact residual_energy_pos n
  exact (pow_pos he 2).trans_le (head_constant_mode_bounds L n hL).1

/-- Optimizer orthogonality to the parity residue determines the two-cell residual. -/
theorem residual_projection_two (n : ℕ) (hn : 0 < n) :
    conditionalProjection 2 (qOne - candidate n) =
      (4 * (1 - saturation n)) • QDivisibilityDensity.qDivisor 2 := by
  apply conditional_eq_of_match
  · exact (cellSpace 2).smul_mem _
      (divisor_mem_cell 2 2 (by decide) (dvd_refl 2))
  · intro d hd
    have hdp := Nat.pos_of_mem_divisors hd
    have hdle := Nat.le_of_dvd (by decide : 0 < 2) (Nat.dvd_of_mem_divisors hd)
    have hd12 : d = 1 ∨ d = 2 := by omega
    have hr : inner ℝ (qOne - candidate n) qOne = 1 - saturation n := by
      rw [residual_inner_qOne, error_identity]
    rcases hd12 with rfl | rfl
    · rw [qDivisor_one, hr, real_inner_smul_left, real_inner_comm,
        QDivisibilityDensity.qOne_inner_qDivisor 2 (by decide)]
      norm_num
      ring
    · have hg := residual_inner_stage n (qResidue 2) (qResidue_two_mem_stage n hn)
      have hdv : inner ℝ (qOne - candidate n)
          (QDivisibilityDensity.qDivisor 2) = 1 - saturation n := by
        rw [QDivisorLegality.qDivisor_two_eq, inner_sub_right, inner_smul_right, hr, hg]
        ring
      rw [hdv, real_inner_smul_left, real_inner_self_eq_norm_sq,
        QDivisibilityDensity.qDivisor_norm_sq 2 (by decide)]
      norm_num
      ring

/-- Even the two-cell retained error is an exact multiple of the squared saturation gap. -/
theorem headEnergy_two (n : ℕ) (hn : 0 < n) :
    headEnergy 2 n = 4 * (1 - saturation n)^2 := by
  have hone : conditionalProjection 2 qOne = qOne :=
    Submodule.starProjection_eq_self_iff.mpr (qOne_mem_cell 2 (by decide))
  rw [headEnergy_eq_norm_sq 2 n (by decide), ← hone, ← map_sub,
    residual_projection_two n hn]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    QDivisibilityDensity.qDivisor_norm_sq 2 (by decide)]
  norm_num
  ring

/-- Every even cutoff satisfies the sharper parity lower bound, retaining the full-error upper bound. -/
theorem even_cutoff_head_bounds (L n : ℕ) (hL : 0 < L)
    (hn : 0 < n) (heven : 2 ∣ L) :
    4 * (1 - saturation n)^2 ≤ headEnergy L n ∧
      headEnergy L n ≤ 1 - saturation n := by
  constructor
  · rw [← headEnergy_two n hn]
    exact headEnergy_mono_of_dvd 2 L n hL heven
  · exact (head_constant_mode_bounds L n hL).2

/-- Every nonempty stage captures at least three quarters of the target energy and strictly less than one. -/
theorem saturation_bounds (n : ℕ) (hn : 0 < n) :
    (3 / 4 : ℝ) ≤ saturation n ∧ saturation n < 1 := by
  have he : 0 < 1 - saturation n := by
    rw [← error_identity]
    exact residual_energy_pos n
  have hb := (head_constant_mode_bounds 2 n (by decide)).2
  rw [headEnergy_two n hn] at hb
  have hx : (4 * (1 - saturation n)) * (1 - saturation n) ≤
      1 * (1 - saturation n) := by nlinarith
  have hy : 4 * (1 - saturation n) ≤ 1 := by
    by_contra h
    have hp : 0 < 4 * (1 - saturation n) - 1 := by linarith
    have hz := mul_pos he hp
    nlinarith
  constructor <;> linarith

/-- Along a divisor-exhausting tower, the centered head tends to the limiting optimizer variance. -/
theorem centered_head_tendsto (L : ℕ → ℕ)
    (hpos : ∀ n, 0 < L n)
    (hnest : ∀ i j, i ≤ j → L i ∣ L j)
    (hcover : ∀ m : ℕ, 0 < m → ∃ n, m ∣ L n) :
    Tendsto (fun n => ‖conditionalProjection (L n) (candidate n) -
      saturation n • qOne‖^2) atTop
      (𝓝 (‖closure.starProjection qOne‖^2 * ‖defect‖^2)) := by
  have he : (fun n => ‖conditionalProjection (L n) (candidate n) -
        saturation n • qOne‖^2) =
      (fun n => saturation n * (1 - saturation n) -
        dotProduct (coefficients n) ((tailGram (L n) n).mulVec (coefficients n))) := by
    funext n
    linarith [centered_head_tail_exact (L n) n (hpos n)]
  rw [he]
  simpa only [sub_zero] using
    (saturation_tendsto.mul error_tendsto).sub
      (matrix_tail_tendsto_zero L hpos hnest hcover)

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.headEnergy_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms headEnergy_one

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.tailEnergy_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tailEnergy_one

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.centered_head_tail_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centered_head_tail_exact

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.cofinal_head_small_iff_saturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_head_small_iff_saturation

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.cofinal_head_small_iff_one_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_head_small_iff_one_mem

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.headEnergy_tendsto_zero_iff_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms headEnergy_tendsto_zero_iff_positive

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.headEnergy_refinement_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms headEnergy_refinement_exact

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.headEnergy_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms headEnergy_two

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.even_cutoff_head_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms even_cutoff_head_bounds

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.saturation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saturation_bounds

/-- info: 'RiemannResearch.RH.QCRTGramSaturation.centered_head_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centered_head_tendsto

end RiemannResearch.RH.QCRTGramSaturation
