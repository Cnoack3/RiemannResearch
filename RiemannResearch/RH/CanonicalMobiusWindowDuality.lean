/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusWindowRecursion
import RiemannResearch.RH.ParetoFiniteHeadDilation
import RiemannResearch.Analysis.BoundedInterpolation

/-!
# Fixed-head capacity and an infinite normal witness

Source: user-provided exact Schur continuation, Sections 12–13. This develops
the standard Hilbert-space duality behind the exact finite capacity increments.
Bounded capacities are equivalent to a common normal vector for all canonical
tails at the fixed head. The equivalence supplies no arithmetic bound.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The actual unnormalized normal vector of the canonical conductor window. -/
def windowNormal (N M : ℕ) (hN : 0 < N) : ThresholdHilbert :=
  capacityNormal N (canonicalWindowIndex N M) (canonicalWindowIndex_pos N M hN)

theorem windowNormal_energy (N M : ℕ) (hN : 0 < N) :
    ‖windowNormal N M hN‖ ^ 2 = windowCapacity N M hN :=
  capacityNormal_energy N (canonicalWindowIndex N M) _

theorem windowNormal_increment (N M K : ℕ) (hN : 0 < N) (hMK : M ≤ K) :
    ‖windowNormal N K hN - windowNormal N M hN‖ ^ 2 =
      windowCapacity N K hN - windowCapacity N M hN := by
  let e : Fin (M - N + 1) → Fin (K - N + 1) :=
    fun i => ⟨i.val, by omega⟩
  exact (capacity_increment_eq_normal_distance_sq N
    (canonicalWindowIndex N M) (canonicalWindowIndex N K)
    (canonicalWindowIndex_pos N M hN) (canonicalWindowIndex_pos N K hN)
    e (fun i => rfl)).symm

theorem windowNormal_equation (N M k : ℕ) (hN : 0 < N)
    (hNk : N ≤ k) (hkM : k ≤ M) :
    inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N)
      (windowNormal N M hN) = 1 := by
  let i : Fin (M - N + 1) := ⟨k - N, by omega⟩
  have hi : canonicalWindowIndex N M i = k := by
    dsimp [canonicalWindowIndex, i]
    omega
  have he := capacityNormal_equations N (canonicalWindowIndex N M)
    (canonicalWindowIndex_pos N M hN) i
  simpa only [tailFamily, hi, windowNormal] using he

/-- Every common normal witness has the finite normal as its projection;
the exact signed remainder gives an upper bound on every finite capacity. -/
theorem windowNormal_completion (N M : ℕ) (hN : 0 < N)
    (Z : ThresholdHilbert)
    (hZ : ∀ k, N ≤ k →
      inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) Z = 1) :
    ‖Z‖ ^ 2 = windowCapacity N M hN + ‖Z - windowNormal N M hN‖ ^ 2 := by
  have hc : inner ℝ (windowNormal N M hN) Z = windowCapacity N M hN := by
    unfold windowNormal capacityNormal
    rw [inner_synthesis_left]
    change (∑ i, normal N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN) i *
        inner ℝ (tailFamily N (canonicalWindowIndex N M) i) Z) = _
    simp only [tailFamily, hZ _ (canonicalWindowIndex_ge N M _), mul_one]
    rfl
  have hc' : inner ℝ Z (windowNormal N M hN) = windowCapacity N M hN := by
    rw [real_inner_comm]
    exact hc
  rw [norm_sub_sq_real, hc', windowNormal_energy]
  ring

theorem windowCapacity_le_commonNormal_energy (N M : ℕ) (hN : 0 < N)
    (Z : ThresholdHilbert)
    (hZ : ∀ k, N ≤ k →
      inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) Z = 1) :
    windowCapacity N M hN ≤ ‖Z‖ ^ 2 := by
  rw [windowNormal_completion N M hN Z hZ]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- A finite upper bound makes the entire normal sequence Cauchy in norm. -/
theorem windowNormal_cauchySeq_of_capacity_bddAbove (N : ℕ) (hN : 0 < N)
    (hb : BddAbove (Set.range (fun M => windowCapacity N M hN))) :
    CauchySeq (fun M => windowNormal N M hN) := by
  apply RiemannResearch.Analysis.BoundedInterpolation.cauchySeq_of_bounded_exact_energy
    (fun M => windowNormal N M hN) (fun M => windowCapacity N M hN) _ hb
  intro M K hMK
  rw [dist_eq_norm]
  exact windowNormal_increment N M K hN hMK

/-- Bounded fixed-head capacity produces a genuine Hilbert-space solution
to every infinite normal equation, as a strong limit of finite solutions. -/
theorem exists_commonNormal_limit_of_capacity_bddAbove (N : ℕ) (hN : 0 < N)
    (hb : BddAbove (Set.range (fun M => windowCapacity N M hN))) :
    ∃ Z : ThresholdHilbert,
      Tendsto (fun M => windowNormal N M hN) atTop (𝓝 Z) ∧
      (∀ k, N ≤ k →
        inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) Z = 1) ∧
      Tendsto (fun M => windowCapacity N M hN) atTop (𝓝 (‖Z‖ ^ 2)) := by
  obtain ⟨Z, hlim⟩ := cauchySeq_tendsto_of_complete
    (windowNormal_cauchySeq_of_capacity_bddAbove N hN hb)
  refine ⟨Z, hlim, ?_, ?_⟩
  · intro k hNk
    have hc : Continuous (fun x : ThresholdHilbert =>
        inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) x) :=
      continuous_const.inner continuous_id
    have he : (fun M => inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N)
        (windowNormal N M hN)) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
      filter_upwards [eventually_ge_atTop k] with M hM
      exact windowNormal_equation N M k hN hNk hM
    exact tendsto_nhds_unique ((hc.tendsto Z).comp hlim)
      (tendsto_const_nhds.congr' he.symm)
  · have he := hlim.norm.pow 2
    simpa only [windowNormal_energy] using he

/-- Exact infinite duality. Neither side of the equivalence is asserted to
hold for any specified positive head. -/
theorem windowCapacity_bddAbove_iff_commonNormal (N : ℕ) (hN : 0 < N) :
    BddAbove (Set.range (fun M => windowCapacity N M hN)) ↔
      ∃ Z : ThresholdHilbert, ∀ k, N ≤ k →
        inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) Z = 1 := by
  constructor
  · intro hb
    obtain ⟨Z, _, hZ, _⟩ := exists_commonNormal_limit_of_capacity_bddAbove N hN hb
    exact ⟨Z, hZ⟩
  · rintro ⟨Z, hZ⟩
    refine ⟨‖Z‖ ^ 2, ?_⟩
    rintro _ ⟨M, rfl⟩
    exact windowCapacity_le_commonNormal_energy N M hN Z hZ

/-- The strong limit is a minimum-energy infinite normal witness, and its
squared distance from each finite normal is exactly the remaining capacity. -/
theorem exists_minimum_commonNormal_of_capacity_bddAbove (N : ℕ) (hN : 0 < N)
    (hb : BddAbove (Set.range (fun M => windowCapacity N M hN))) :
    ∃ Z : ThresholdHilbert,
      Tendsto (fun M => windowNormal N M hN) atTop (𝓝 Z) ∧
      IsLeast {E : ℝ | ∃ W : ThresholdHilbert,
        (∀ k, N ≤ k →
          inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) W = 1) ∧
        ‖W‖ ^ 2 = E} (‖Z‖ ^ 2) ∧
      ∀ M, ‖Z - windowNormal N M hN‖ ^ 2 =
        ‖Z‖ ^ 2 - windowCapacity N M hN := by
  obtain ⟨Z, hlim, hZ, hcap⟩ :=
    exists_commonNormal_limit_of_capacity_bddAbove N hN hb
  refine ⟨Z, hlim, ⟨⟨Z, hZ, rfl⟩, ?_⟩, ?_⟩
  · rintro E ⟨W, hW, rfl⟩
    exact le_of_tendsto hcap (Eventually.of_forall fun M =>
      windowCapacity_le_commonNormal_energy N M hN W hW)
  · intro M
    linarith [windowNormal_completion N M hN Z hZ]

/-- The energy of a strong normal limit is exactly the supremum of the
finite-window capacities. -/
theorem windowNormal_limit_energy_eq_iSup (N : ℕ) (hN : 0 < N)
    (hb : BddAbove (Set.range (fun M => windowCapacity N M hN)))
    (Z : ThresholdHilbert)
    (hlim : Tendsto (fun M => windowNormal N M hN) atTop (𝓝 Z)) :
    ‖Z‖ ^ 2 = ⨆ M, windowCapacity N M hN := by
  have hcap : Tendsto (fun M => windowCapacity N M hN) atTop (𝓝 (‖Z‖ ^ 2)) := by
    simpa only [windowNormal_energy] using hlim.norm.pow 2
  exact tendsto_nhds_unique hcap
    (tendsto_atTop_ciSup (canonicalWindow_capacity_mono N hN) hb)

/-- At the infinite conductor limit, every competing normal witness retains
an exact nonnegative orthogonal remainder. -/
theorem commonNormal_completion_at_limit (N : ℕ) (hN : 0 < N)
    (Z : ThresholdHilbert)
    (hlim : Tendsto (fun M => windowNormal N M hN) atTop (𝓝 Z))
    (W : ThresholdHilbert)
    (hW : ∀ k, N ≤ k →
      inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) W = 1) :
    ‖W‖ ^ 2 = ‖Z‖ ^ 2 + ‖W - Z‖ ^ 2 := by
  have hcap : Tendsto (fun M => windowCapacity N M hN) atTop (𝓝 (‖Z‖ ^ 2)) := by
    simpa only [windowNormal_energy] using hlim.norm.pow 2
  have hrest : Tendsto (fun M => ‖W - windowNormal N M hN‖ ^ 2)
      atTop (𝓝 (‖W - Z‖ ^ 2)) :=
    (tendsto_const_nhds.sub hlim).norm.pow 2
  have he : (fun M => windowCapacity N M hN + ‖W - windowNormal N M hN‖ ^ 2) =
      (fun _ : ℕ => ‖W‖ ^ 2) := by
    funext M
    exact (windowNormal_completion N M hN W hW).symm
  have ht := hcap.add hrest
  rw [he] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

/-- Equality in the infinite minimum forces equality of the actual vectors,
not merely equality of their finite coefficient descriptions. -/
theorem commonNormal_energy_eq_limit_iff (N : ℕ) (hN : 0 < N)
    (Z : ThresholdHilbert)
    (hlim : Tendsto (fun M => windowNormal N M hN) atTop (𝓝 Z))
    (W : ThresholdHilbert)
    (hW : ∀ k, N ≤ k →
      inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) W = 1) :
    ‖W‖ ^ 2 = ‖Z‖ ^ 2 ↔ W = Z := by
  constructor
  · intro he
    have hz : ‖W - Z‖ ^ 2 = 0 := by
      linarith [commonNormal_completion_at_limit N hN Z hlim W hW]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro rfl
    rfl

/-- A nonzero actual projection residual supplies an explicit common normal
at every positive head, with every signed pairing retained. -/
theorem residual_commonNormal (N : ℕ) (hN : 0 < N) (hpos : 0 < limitEnergy)
    (k : ℕ) (hNk : N ≤ k) :
    inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N)
      (-(residualHeadPairing N)⁻¹ • hilbertTailShift limitResidual N) = 1 := by
  have hp := residualHeadPairing_pos N hN hpos
  have hh : ∀ j, 0 < j → j ≤ N → hilbertSequence (canonicalMobiusHilbert k) j = 1 := by
    intro j hj hjN
    exact canonicalMobiusHilbert_exact k j hj (hjN.trans hNk)
  have he := residual_tail_pairing_eq_neg_head N
    (canonicalMobiusHilbert_mem_closedSpace k) hh
  rw [inner_smul_right, real_inner_comm, he]
  field_simp [ne_of_gt hp]

/-- Under a positive residual, every fixed-head capacity has one finite bound. -/
theorem windowCapacity_bddAbove_of_residual_pos (N : ℕ) (hN : 0 < N)
    (hpos : 0 < limitEnergy) :
    BddAbove (Set.range (fun M => windowCapacity N M hN)) := by
  apply (windowCapacity_bddAbove_iff_commonNormal N hN).mpr
  exact ⟨-(residualHeadPairing N)⁻¹ • hilbertTailShift limitResidual N,
    residual_commonNormal N hN hpos⟩

/-- Failure of Mathlib RH gives an actual strong limiting normal vector at
EVERY positive fixed head, and a finite limit of its capacities. -/
theorem exists_commonNormal_limit_of_not_RH (N : ℕ) (hN : 0 < N)
    (hRH : ¬ RiemannHypothesis) :
    ∃ Z : ThresholdHilbert,
      Tendsto (fun M => windowNormal N M hN) atTop (𝓝 Z) ∧
      (∀ k, N ≤ k →
        inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) Z = 1) ∧
      Tendsto (fun M => windowCapacity N M hN) atTop (𝓝 (‖Z‖ ^ 2)) :=
  exists_commonNormal_limit_of_capacity_bddAbove N hN
    (windowCapacity_bddAbove_of_residual_pos N hN (not_RH_limitEnergy_pos hRH))

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
