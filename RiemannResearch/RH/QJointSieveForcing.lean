import RiemannResearch.RH.QSievePairingCertificates
import RiemannResearch.RH.QParetoJointBlock

/-!
# Actual middle-component cancellation through signed sieves

The finite signed pairing approximates the nonnegative K-block energy after subtracting the actual middle coupling. Its convergence to zero is equivalent to vanishing of that block. This is not asserted to be an RH equivalence.

Research agenda: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QJointSieveForcing
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open QParetoJointAnnihilator QParetoJointBlock QParetoCostTransfer QSievePairingCertificates

variable (V : Submodule ℝ ThresholdHilbert) (W : Submodule ℝ QHilbert)
variable [(jointAnnihilator V W).HasOrthogonalProjection]
variable (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)

theorem block_pairing_energy (k u : ThresholdHilbert)
    (hk : k ∈ jointAnnihilator V W)
    (hb : k + (jointAnnihilator V W).starProjection (reciprocalD k) =
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) -
        (jointAnnihilator V W).starProjection (reciprocalD u)) :
    ‖k‖^2 + inner ℝ k (reciprocalD k) =
      inner ℝ k (reciprocalD hilbertOne) - inner ℝ k (reciprocalD u) := by
  have hp (z : ThresholdHilbert) :
      inner ℝ k ((jointAnnihilator V W).starProjection z) = inner ℝ k z := by
    have h := Submodule.inner_right_of_mem_orthogonal hk
      (Submodule.sub_starProjection_mem_orthogonal (K := jointAnnihilator V W) z)
    rw [inner_sub_right] at h
    linarith
  have hi := congrArg (fun z => inner ℝ k z) hb
  simpa only [inner_add_right, inner_sub_right, hp, real_inner_self_eq_norm_sq] using hi

include hW in
theorem block_sieve_certificate (k u : ThresholdHilbert)
    (hk : k ∈ jointAnnihilator V W)
    (hb : k + (jointAnnihilator V W).starProjection (reciprocalD k) =
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) -
        (jointAnnihilator V W).starProjection (reciprocalD u)) (N : ℕ) :
    |(‖k‖^2 + inner ℝ k (reciprocalD k)) -
      (mobiusPairing k N-inner ℝ k (reciprocalD u))|^2 ≤ ‖k‖^2/((N : ℝ)+1) := by
  have hm : inner ℝ k hilbertOne = 0 := by
    simpa only [real_inner_comm] using joint_mean_zero_of_all_primes V W hW k hk
  have he := block_pairing_energy V W k u hk hb
  have hi : (‖k‖^2 + inner ℝ k (reciprocalD k)) -
      (mobiusPairing k N-inner ℝ k (reciprocalD u)) =
      inner ℝ k (toPareto (QReciprocalMetric.D qOne))-mobiusPairing k N := by
    rw [toPareto_D, toPareto_qOne]
    linarith only [he]
  rw [hi]
  exact pairing_error_sq k hm N

include hW in
theorem block_sieve_cancellation_iff (k u : ThresholdHilbert)
    (hk : k ∈ jointAnnihilator V W)
    (hb : k + (jointAnnihilator V W).starProjection (reciprocalD k) =
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) -
        (jointAnnihilator V W).starProjection (reciprocalD u)) :
    Tendsto (fun N => mobiusPairing k N-inner ℝ k (reciprocalD u)) atTop (𝓝 0) ↔ k = 0 := by
  have hm : inner ℝ k hilbertOne = 0 := by
    simpa only [real_inner_comm] using joint_mean_zero_of_all_primes V W hW k hk
  have ht := (mobiusPairing_tendsto k hm).sub_const (inner ℝ k (reciprocalD u))
  have he := block_pairing_energy V W k u hk hb
  rw [toPareto_D, toPareto_qOne, ← he] at ht
  constructor
  · intro h0
    have hz := tendsto_nhds_unique ht h0
    have hn : ‖k‖ = 0 := by nlinarith [reciprocalD_positive k, norm_nonneg k]
    exact norm_eq_zero.mp hn
  · rintro rfl
    simpa [mobiusPairing] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

variable [(W.map toParetoLinear).HasOrthogonalProjection]

include hW in
theorem actual_middle_sieve_cancellation_iff
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S) :
    let f := toPareto (S.starProjection qOne)
    let k := (jointAnnihilator V W).starProjection f
    let u := middleComponent V W f
    Tendsto (fun N => mobiusPairing k N-inner ℝ k (reciprocalD u)) atTop (𝓝 0) ↔ k = 0 := by
  dsimp only
  exact block_sieve_cancellation_iff V W hW _ _
    ((jointAnnihilator V W).starProjection_apply_mem _)
    (actual_middle_block_equation V W hW S hsame)

include hW in
theorem actual_middle_sieve_certificate
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S) (N : ℕ) :
    let f := toPareto (S.starProjection qOne)
    let k := (jointAnnihilator V W).starProjection f
    let u := middleComponent V W f
    |(‖k‖^2 + inner ℝ k (reciprocalD k)) -
      (mobiusPairing k N-inner ℝ k (reciprocalD u))|^2 ≤ ‖k‖^2/((N : ℝ)+1) := by
  dsimp only
  exact block_sieve_certificate V W hW _ _
    ((jointAnnihilator V W).starProjection_apply_mem _)
    (actual_middle_block_equation V W hW S hsame) N

end RiemannResearch.RH.QJointSieveForcing
