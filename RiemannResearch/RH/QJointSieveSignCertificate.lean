/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QJointSieveForcing
import RiemannResearch.RH.QPrimeCarryProjection
import Mathlib.Topology.Algebra.Order.Field

/-!
# One-sided signed certificates for the actual K block

Source: the signed K middle-block obligation, 16 November 2026.
The inputs are the complete signed factorial-sieve error in
`QJointSieveForcing` and positivity of the reciprocal multiplier.

This proves an unconditional quantitative estimate for the actual squarefree fit:
`‖k‖² ≤ 2 * b_N + 1 / (N + 1)`, where `b_N` retains both the signed
composite-conductor sum and the actual middle coupling. A cofinal one-sided
upper bound on `b_N` is equivalent to the requested cancellation. That
arithmetic upper bound is NOT proved here. No Q-mean-zero premise is used.

The classical Nyman--Beurling/Báez-Duarte criterion is background, not an
unconditional density input: Bagchi, arXiv:math/0607733, Theorem 1;
Báez-Duarte, arXiv:math/0202141, Theorem 1.1. Neither paper proves this
specific prime/squarefree K-block cancellation.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QJointSieveSignCertificate
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open QParetoJointAnnihilator QParetoJointBlock QParetoCostTransfer
open QSievePairingCertificates QJointSieveForcing

/-- A one-sided consequence of the signed quadratic error certificate. -/
theorem scalar_signed_certificate (r E b a : ℝ)
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hE : r ^ 2 ≤ E)
    (herr : (E - b) ^ 2 ≤ r ^ 2 * a) :
    r ^ 2 ≤ 2 * b + a ∧ -(a / 4) ≤ b := by
  have hs : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hupper : E - b ≤ r * Real.sqrt a := by
    have hn : 0 ≤ r * Real.sqrt a := mul_nonneg hr (Real.sqrt_nonneg a)
    have hs' : (E - b) ^ 2 ≤ (r * Real.sqrt a) ^ 2 := by
      simpa only [mul_pow, hs] using herr
    nlinarith only [hs', hn, sq_nonneg (E - b - r * Real.sqrt a)]
  constructor
  · nlinarith [sq_nonneg (r - Real.sqrt a)]
  · nlinarith [sq_nonneg (r - Real.sqrt a / 2)]

variable (V : Submodule ℝ ThresholdHilbert) (W : Submodule ℝ QHilbert)
variable [(jointAnnihilator V W).HasOrthogonalProjection]
variable (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)

/-- The signed quantity retains the complete actual middle coupling. -/
def signedSieve (k u : ThresholdHilbert) (N : ℕ) : ℝ :=
  mobiusPairing k N - inner ℝ k (reciprocalD u)

include hW in
theorem block_signed_sieve_bounds (k u : ThresholdHilbert)
    (hk : k ∈ jointAnnihilator V W)
    (hb : k + (jointAnnihilator V W).starProjection (reciprocalD k) =
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) -
        (jointAnnihilator V W).starProjection (reciprocalD u)) (N : ℕ) :
    ‖k‖ ^ 2 ≤ 2 * signedSieve k u N + 1 / ((N : ℝ) + 1) ∧
      -(1 / ((N : ℝ) + 1) / 4) ≤ signedSieve k u N := by
  have hc := block_sieve_certificate V W hW k u hk hb N
  rw [sq_abs] at hc
  exact scalar_signed_certificate ‖k‖
    (‖k‖ ^ 2 + inner ℝ k (reciprocalD k)) (signedSieve k u N)
    (1 / ((N : ℝ) + 1)) (norm_nonneg _) (by positivity)
    (by linarith [reciprocalD_positive k]) (by simpa [signedSieve, div_eq_mul_inv] using hc)

include hW in
theorem block_norm_sq_le_of_signed_sieve_nonpos (k u : ThresholdHilbert)
    (hk : k ∈ jointAnnihilator V W)
    (hb : k + (jointAnnihilator V W).starProjection (reciprocalD k) =
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) -
        (jointAnnihilator V W).starProjection (reciprocalD u))
    (N : ℕ) (hN : signedSieve k u N ≤ 0) :
    ‖k‖ ^ 2 ≤ 1 / ((N : ℝ) + 1) := by
  have hc := (block_signed_sieve_bounds V W hW k u hk hb N).1
  linarith

include hW in
theorem block_eq_zero_iff_cofinal_signed_sieve_upper (k u : ThresholdHilbert)
    (hk : k ∈ jointAnnihilator V W)
    (hb : k + (jointAnnihilator V W).starProjection (reciprocalD k) =
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) -
        (jointAnnihilator V W).starProjection (reciprocalD u)) :
    k = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N ≥ J, signedSieve k u N ≤ ε := by
  constructor
  · rintro rfl ε hε J
    exact ⟨J, le_rfl, by simpa [signedSieve, mobiusPairing] using hε.le⟩
  · intro hc
    by_contra hk0
    have hr : 0 < ‖k‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hk0)
    have ht : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
          (tendsto_add_atTop_nat 1)
    have hev : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / ((N : ℝ) + 1) < ‖k‖ ^ 2 / 4 :=
      ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ‖k‖ ^ 2 / 4))
    obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨N, hNJ, hN⟩ := hc (‖k‖ ^ 2 / 4) (by positivity) J
    have hcert := (block_signed_sieve_bounds V W hW k u hk hb N).1
    have hi := hJ N hNJ
    linarith

variable [(W.map toParetoLinear).HasOrthogonalProjection]

include hW in
theorem actual_middle_signed_sieve_bounds
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S) (N : ℕ) :
    let f := toPareto (S.starProjection qOne)
    let k := (jointAnnihilator V W).starProjection f
    let u := middleComponent V W f
    ‖k‖ ^ 2 ≤ 2 * signedSieve k u N + 1 / ((N : ℝ) + 1) ∧
      -(1 / ((N : ℝ) + 1) / 4) ≤ signedSieve k u N := by
  dsimp only
  exact block_signed_sieve_bounds V W hW _ _
    ((jointAnnihilator V W).starProjection_apply_mem _)
    (actual_middle_block_equation V W hW S hsame) N

include hW in
theorem actual_k_cancellation_iff_cofinal_signed_sieve_upper
    [V.HasOrthogonalProjection]
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S) :
    (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) =
      (jointAnnihilator V W).starProjection
        (reciprocalD (middleComponent V W (toPareto (S.starProjection qOne)))) ↔
    ∀ ε : ℝ, 0 < ε → ∀ J : ℕ, ∃ N ≥ J,
      signedSieve (kDisplacement V W S)
        (middleComponent V W (toPareto (S.starProjection qOne))) N ≤ ε := by
  rw [← kDisplacement_eq_zero_iff_cancellation V W hW S hsame]
  exact block_eq_zero_iff_cofinal_signed_sieve_upper V W hW _ _
    ((jointAnnihilator V W).starProjection_apply_mem _)
    (kDisplacement_normal V W hW S hsame)


namespace Squarefree
open ZetaTwoOptimizerStage QSquarefreeMeasureRigidity QPrimeCarryProjection

/-- The prime closure is closed also in its physical Pareto realization. -/
instance primePareto_isClosed :
    IsClosed (primeClosure.map toParetoLinear : Set ThresholdHilbert) := by
  change IsClosed (paretoEquiv '' (primeClosure : Set QHilbert))
  exact paretoEquiv.toHomeomorph.isClosedMap _
    QSimultaneousCRT.primeSpan.isClosed_topologicalClosure

/-- The squarefree Pareto closure is closed, supplying the joint projection instance. -/
instance squarefreePareto_isClosed :
    IsClosed (paretoSquarefreeClosure : Set ThresholdHilbert) := by
  unfold paretoSquarefreeClosure
  exact Submodule.isClosed_topologicalClosure _

/-- The actual squarefree joint annihilator; the conductor family is unchanged. -/
abbrev K : Submodule ℝ ThresholdHilbert :=
  jointAnnihilator paretoSquarefreeClosure primeClosure

/-- P projection of the difference between the actual Q and P squarefree fits. -/
def actualK : ThresholdHilbert :=
  kDisplacement paretoSquarefreeClosure primeClosure closure

/-- The actual middle component of the physical Q fit. -/
def actualMiddle : ThresholdHilbert :=
  middleComponent paretoSquarefreeClosure primeClosure
    (toPareto (closure.starProjection qOne))

def actualSignedSieve (N : ℕ) : ℝ := signedSieve actualK actualMiddle N

theorem actualK_normal :
    actualK + K.starProjection (reciprocalD actualK) =
      K.starProjection (reciprocalD hilbertOne) -
        K.starProjection (reciprocalD actualMiddle) :=
  kDisplacement_normal paretoSquarefreeClosure primeClosure
    qResidue_mem_primeClosure closure toPareto_mem_paretoSquarefreeClosure_iff

theorem actual_signed_sieve_bounds (N : ℕ) :
    ‖actualK‖ ^ 2 ≤ 2 * actualSignedSieve N + 1 / ((N : ℝ) + 1) ∧
      -(1 / ((N : ℝ) + 1) / 4) ≤ actualSignedSieve N :=
  block_signed_sieve_bounds paretoSquarefreeClosure primeClosure
    qResidue_mem_primeClosure actualK actualMiddle
    (K.starProjection_apply_mem _) actualK_normal N

/-- This is an equivalence, not an assertion of the right-hand arithmetic condition. -/
theorem cancellation_iff_cofinal_signed_sieve_upper :
    K.starProjection (reciprocalD hilbertOne) =
      K.starProjection (reciprocalD actualMiddle) ↔
    ∀ ε : ℝ, 0 < ε → ∀ J : ℕ, ∃ N ≥ J, actualSignedSieve N ≤ ε :=
  actual_k_cancellation_iff_cofinal_signed_sieve_upper
    paretoSquarefreeClosure primeClosure qResidue_mem_primeClosure closure
    toPareto_mem_paretoSquarefreeClosure_iff

/-- The established P-mean theorem does apply to the actual block. -/
theorem actualK_pMean_zero : inner ℝ hilbertOne actualK = 0 :=
  joint_mean_zero_of_all_primes paretoSquarefreeClosure primeClosure
    qResidue_mem_primeClosure actualK (K.starProjection_apply_mem _)

/-- Q-mean zero on K is a distinct obligation. This theorem does not assert it. -/
theorem qMean_zero_iff_reciprocal_projection_zero :
    (∀ h ∈ K, inner ℝ qOne (toQ h) = 0) ↔
      K.starProjection (reciprocalD hilbertOne) = 0 :=
  joint_qMean_zero_iff_project_reciprocal_one_zero
    paretoSquarefreeClosure primeClosure qResidue_mem_primeClosure

/-- Both the Q mean and the signed middle coupling remain in the exact energy. -/
theorem actualK_energy_qMean :
    ‖actualK‖ ^ 2 + inner ℝ actualK (reciprocalD actualK) =
      ZetaTwoProbability.zetaTwo * inner ℝ qOne (toQ actualK) -
        inner ℝ actualK (reciprocalD actualMiddle) := by
  have he := block_pairing_energy paretoSquarefreeClosure primeClosure
    actualK actualMiddle (K.starProjection_apply_mem _) actualK_normal
  have hm := joint_qMean_identity paretoSquarefreeClosure primeClosure
    qResidue_mem_primeClosure actualK (K.starProjection_apply_mem _)
  have hsym : inner ℝ (reciprocalD hilbertOne) actualK =
      inner ℝ actualK (reciprocalD hilbertOne) := real_inner_comm _ _
  rw [hsym] at hm
  linarith

end Squarefree

end RiemannResearch.RH.QJointSieveSignCertificate

namespace RiemannResearch.RH.QJointSieveSignCertificate.Squarefree

/-- info: 'RiemannResearch.RH.QJointSieveSignCertificate.Squarefree.actual_signed_sieve_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_signed_sieve_bounds

/-- info: 'RiemannResearch.RH.QJointSieveSignCertificate.Squarefree.cancellation_iff_cofinal_signed_sieve_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cancellation_iff_cofinal_signed_sieve_upper

end RiemannResearch.RH.QJointSieveSignCertificate.Squarefree
