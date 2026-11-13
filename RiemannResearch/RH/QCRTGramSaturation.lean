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

end RiemannResearch.RH.QCRTGramSaturation
