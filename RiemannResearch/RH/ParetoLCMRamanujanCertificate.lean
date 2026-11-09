/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoLCMZeroCertificate
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.Analysis.FiniteHilbertGramMatrix

/-!
# Ramanujan normal equations on the full LCM dictionary

Möbius inversion exchanges the divisor atoms and packets. The von Mangoldt
source in the packet Gram and the zero-certificate split compute the same
complete Pareto projection error.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.Analysis.FiniteHilbertGram

/-- All nontrivial divisors, including mixed conductors and prime powers. -/
def packetIndex (L : ℕ) : Finset ℕ := L.divisors.filter (fun d => 1 < d)

theorem mem_packetIndex {L d : ℕ} :
    d ∈ packetIndex L ↔ d ∈ L.divisors ∧ 1 < d :=
  Finset.mem_filter

def packetFamily (L : ℕ) (q : packetIndex L) : ThresholdHilbert :=
  ramanujanPacketHilbert q.val

private theorem rawResidueAtom_eq_normalized (d : ℕ) (hd : 1 < d) :
    rawResidueAtom (d - 2) = (d : ℝ) • normalizedResidueHilbert d (by omega) := by
  have h : d - 2 + 2 = d := by omega
  unfold rawResidueAtom CoefficientStabilization.residueAtom
  simp only [h]

theorem packet_mem_trial (L q : ℕ) (hq : q ∈ packetIndex L) :
    ramanujanPacketHilbert q ∈ trialSpace L := by
  obtain ⟨hqL, hq⟩ := mem_packetIndex.mp hq
  rw [ramanujanPacketHilbert_eq_divisor_sum q hq]
  apply Submodule.sum_mem
  intro d hd
  obtain ⟨hdq, hd⟩ := Finset.mem_filter.mp hd
  rw [rawResidueAtom_eq_normalized d hd]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (atom_mem_trial L d (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hqL).2)
      (by omega) ((Nat.dvd_of_mem_divisors hdq).trans (Nat.dvd_of_mem_divisors hqL))))

/-- The full legal space and its Ramanujan parametrization are identical. -/
theorem packetSpan_eq_trialSpace (L : ℕ) :
    synthesisSpan (packetFamily L) = trialSpace L := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact packet_mem_trial L q.val q.property
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    have hdpos := Nat.pos_of_mem_divisors d.property
    change normalizedResidueHilbert d.val hdpos ∈ synthesisSpan (packetFamily L)
    by_cases hd1 : d.val = 1
    · have hzero : normalizedResidueHilbert d.val hdpos = 0 := by
        apply hilbertSequence_injective
        funext n
        rw [normalizedResidueHilbert_sequence]
        change ArithmeticCumulative.residueFraction d.val n =
          hilbertSequenceLinear (0 : ThresholdHilbert) n
        rw [map_zero]
        simp [ArithmeticCumulative.residueFraction, hd1, Nat.mod_one]
      rw [hzero]
      exact Submodule.zero_mem _
    have hd : 1 < d.val := by omega
    have hraw : rawResidueAtom (d.val - 2) ∈ synthesisSpan (packetFamily L) := by
      rw [rawResidueAtom_eq_packet_divisor_sum d.val hd]
      apply Submodule.sum_mem
      intro q hq
      obtain ⟨hqd, hq⟩ := Finset.mem_filter.mp hq
      have hqL : q ∈ packetIndex L := mem_packetIndex.mpr
        ⟨Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hqd).trans
          (Nat.dvd_of_mem_divisors d.property), (Nat.mem_divisors.mp d.property).2⟩, hq⟩
      exact Submodule.subset_span ⟨⟨q, hqL⟩, rfl⟩
    rw [rawResidueAtom_eq_normalized d.val hd] at hraw
    have hdn : (d.val : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    simpa only [smul_smul, inv_mul_cancel₀ hdn, one_smul] using
      (synthesisSpan (packetFamily L)).smul_mem (d.val : ℝ)⁻¹ hraw

theorem packetFamily_independent (L : ℕ) : LinearIndependent ℝ (packetFamily L) := by
  let e (q : packetIndex L) : Fin L := ⟨q.val - 2, by
    obtain ⟨hq, hq1⟩ := mem_packetIndex.mp q.property
    have hqL := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hq).2)
      (Nat.dvd_of_mem_divisors hq)
    omega⟩
  have he : Function.Injective e := by
    intro q r h
    have hqr : q.val - 2 = r.val - 2 := congrArg Fin.val h
    have hq := (mem_packetIndex.mp q.property).2
    have hr := (mem_packetIndex.mp r.property).2
    exact Subtype.ext (by omega)
  have heq : (fun i : Fin L => ramanujanPacketHilbert (i.val + 2)) ∘ e = packetFamily L := by
    funext q
    have hq := (mem_packetIndex.mp q.property).2
    change ramanujanPacketHilbert (q.val - 2 + 2) = ramanujanPacketHilbert q.val
    rw [show q.val - 2 + 2 = q.val by omega]
  rw [← heq]
  exact (finitePacket_independent L).comp e he

/-- The actual complete-Pareto Gram and its sparse von Mangoldt source. -/
def packetGram (L : ℕ) : Matrix (packetIndex L) (packetIndex L) ℝ :=
  gramMatrix (packetFamily L)

def packetSource (L : ℕ) (q : packetIndex L) : ℝ := ArithmeticFunction.vonMangoldt q.val

theorem packet_cross_one (L : ℕ) : cross (packetFamily L) hilbertOne = packetSource L := by
  funext q
  rw [cross, packetFamily, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
    paretoMean_ramanujanPacket, packetSource]

theorem packetGram_posDef (L : ℕ) : (packetGram L).PosDef :=
  gramMatrix_posDef (packetFamily_independent L)

theorem lcmBest_eq_packetInverse (M : ℕ) :
    lcmBest M = Fintype.linearCombination ℝ (packetFamily (Nat.lcmUpto M))
      ((packetGram (Nat.lcmUpto M))⁻¹.mulVec (packetSource (Nat.lcmUpto M))) := by
  let L := Nat.lcmUpto M
  change (trialSpace L).starProjection hilbertOne = _
  have hv := packetFamily_independent L
  rw [packetGram, ← packet_cross_one, ← inverseCoeff_eq_inv_mulVec hv]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← packetSpan_eq_trialSpace]
    exact synthesis_mem _ _
  · intro v hv'
    rw [← packetSpan_eq_trialSpace, synthesisSpan, ← Fintype.range_linearCombination] at hv'
    obtain ⟨c, rfl⟩ := hv'
    exact residual_orthogonal hv hilbertOne c

theorem lcm_error_eq_one_sub_packet_inverse (M : ℕ) :
    ‖hilbertOne - lcmBest M‖ ^ 2 =
      1 - dotProduct (packetSource (Nat.lcmUpto M))
        ((packetGram (Nat.lcmUpto M))⁻¹.mulVec (packetSource (Nat.lcmUpto M))) := by
  have h := residual_matrix_value (packetFamily_independent (Nat.lcmUpto M)) hilbertOne
  rw [packet_cross_one, hilbertOne_norm_sq, ← packetGram, ← lcmBest_eq_packetInverse] at h
  exact h

/-- The packet Schur complement splits into the multiples, zero, and legal remainder terms. -/
theorem lcm_packet_inverse_zero_split {ι : Type*} [Fintype ι] (M : ℕ) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    1 - dotProduct (packetSource (Nat.lcmUpto M))
      ((packetGram (Nat.lcmUpto M))⁻¹.mulVec (packetSource (Nat.lcmUpto M))) =
      classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
        certificateEnergy (lcmResidueIndex M) z + lcmRemainder z M := by
  rw [← lcm_error_eq_one_sub_packet_inverse, lcm_best_error_eq M z hs hs1 hz]

/-- The divisor change of basis in weighted nonzero residue coordinates. -/
def packetClassVector (N q : ℕ) : EuclideanSpace ℝ (Fin N) :=
  ∑ d ∈ packetIndex q, ((ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ)) • atomVector N d

theorem packetClassVector_prime (N p : ℕ) (hp : p.Prime) :
    packetClassVector N p = (p : ℝ) • atomVector N p := by
  have h : packetIndex p = {p} := by
    ext d
    rw [mem_packetIndex, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hd1⟩
      exact ((Nat.dvd_prime hp).mp (Nat.dvd_of_mem_divisors hd)).resolve_left (by omega)
    · rintro rfl
      exact ⟨Nat.mem_divisors.mpr ⟨dvd_refl _, hp.ne_zero⟩, hp.one_lt⟩
  simp [packetClassVector, h, Nat.div_self hp.pos]

/-- The entire packet signature keeps the same factor of the actual zeta function. -/
theorem inner_row_packet_eq_zeta {ι : Type*} (N q : ℕ) (hq : q ∣ N + 1)
    (z : ι → ℂ) (i : ι × Bool) (hs : 0 < (z i.1).re) (hs1 : z i.1 ≠ 1) :
    inner ℝ (rowVector N z i) (packetClassVector N q) =
      ∑ d ∈ packetIndex q, ((ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ)) *
        part i.2 (riemannZeta (z i.1) * (1 / (d : ℂ) - (d : ℂ) ^ (-z i.1))) := by
  simp only [packetClassVector, inner_sum, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdq, hd1⟩ := mem_packetIndex.mp hd
  rw [inner_row_atom_eq_zeta N d (by omega) ((Nat.dvd_of_mem_divisors hdq).trans hq) z i hs hs1]

theorem zero_row_orthogonal_packet {ι : Type*} (N q : ℕ) (hq : q ∣ N + 1)
    (z : ι → ℂ) (i : ι × Bool) (hs : 0 < (z i.1).re) (hs1 : z i.1 ≠ 1)
    (hz : riemannZeta (z i.1) = 0) :
    inner ℝ (rowVector N z i) (packetClassVector N q) = 0 := by
  rw [inner_row_packet_eq_zeta N q hq z i hs hs1, hz]
  cases i.2 <;> simp [part]

theorem certificate_shift_preserves_packet_pairing {ι : Type*} [Fintype ι]
    (N q : ℕ) (hq : q ∣ N + 1) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0)
    (x : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (packetClassVector N q) (x - certificateVector N z) =
      inner ℝ (packetClassVector N q) x := by
  simp only [packetClassVector, sum_inner, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdq, hd1⟩ := mem_packetIndex.mp hd
  rw [certificate_shift_preserves_atom_pairing N d (by omega)
    ((Nat.dvd_of_mem_divisors hdq).trans hq) z hs hs1 hz x]

end RiemannResearch.RH.Pareto.ResidueMellin
