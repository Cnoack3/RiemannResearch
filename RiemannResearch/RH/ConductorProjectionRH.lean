import RiemannResearch.RH.ConductorProjectionChain
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ThresholdHilbertCocycle
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-!
# Exact full-packet identification and the conductor-gain implication to RH

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
Sections 2 and 7. The packet/residue identification below is actual finite
Möbius inversion. The final implication uses the already proved Mellin
separation/reflection theorem `riemannHypothesis_of_hilbertOne_mem_legalClosure`.

Nonsummability of the actual relative gains is a displayed hypothesis, not
a proved provider. The reverse implication from RH to approximation is not
asserted or assumed here.
-/

open Filter
open scoped BigOperators Topology
noncomputable section
namespace RiemannResearch.RH.Pareto.ConductorProjection

private theorem packet_one_eq_zero : ramanujanPacketHilbert 1 = 0 := by
  apply hilbertSequence_injective
  funext k
  rw [hilbertSequence_ramanujanPacketHilbert]
  cases k <;> simp [ramanujanPacket, residue, hilbertSequence, Nat.mod_one]

private theorem packetSum_mem_full (n : ℕ) :
    (∑ d ∈ n.divisors, ramanujanPacketHilbert d) ∈ fullPacketSpace := by
  apply fullPacketSpace.sum_mem
  intro d hd
  by_cases hd1 : d = 1
  · rw [hd1, packet_one_eq_zero]
    exact fullPacketSpace.zero_mem
  · have hdp := Nat.pos_of_mem_divisors hd
    exact Submodule.subset_span ⟨d, by omega, rfl⟩

/-- Divisor synthesis is an equality in the actual physical coordinates. -/
private theorem packetSum_sequence (n : ℕ) (hn : 0 < n) :
    hilbertSequence (∑ d ∈ n.divisors, ramanujanPacketHilbert d) = residue n := by
  change hilbertSequenceLinear (∑ d ∈ n.divisors, ramanujanPacketHilbert d) = _
  rw [map_sum]
  funext k
  simp only [Finset.sum_apply]
  change (∑ d ∈ n.divisors, hilbertSequence (ramanujanPacketHilbert d) k) = _
  simp only [hilbertSequence_ramanujanPacketHilbert]
  exact ramanujanPacket_divisor_sum n k hn

/-- The complete finite divisor-packet dictionary is exactly the finite
legal dictionary with all positive seeds and all integer dilations. -/
theorem fullPacketSpace_eq_legalSubspace :
    fullPacketSpace = hilbertLegalSubspace (Set.Ici 1) := by
  have hseed : Set.Ici (1 : ℕ) = {n : ℕ | 0 < n} := by
    ext n
    simp only [Set.mem_Ici, Set.mem_ofPred_eq]
    omega
  rw [hseed]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, hq, rfl⟩
    change hilbertSequence (ramanujanPacketHilbert q) ∈
      legalSeedSpan {n : ℕ | 0 < n}
    rw [hilbertSequence_ramanujanPacketHilbert]
    have he : ramanujanPacket q = ∑ d ∈ q.divisors,
        (ArithmeticFunction.moebius (q / d) : ℝ) • residue d := by
      funext k
      simp [ramanujanPacket]
    rw [he]
    apply (legalSeedSpan {n : ℕ | 0 < n}).sum_mem
    intro d hd
    apply (legalSeedSpan {n : ℕ | 0 < n}).smul_mem
    simpa only [dilation_one] using
      (dilation_generator_mem {n : ℕ | 0 < n} (a := d) (m := 1)
        (Nat.pos_of_mem_divisors hd) (by norm_num))
  · have hex : ∀ g ∈ Submodule.span ℝ
        {g : ℕ → ℝ | ∃ n : ℕ, 0 < n ∧ g = residue n},
        ∃ G : ThresholdHilbert, G ∈ fullPacketSpace ∧ hilbertSequence G = g := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨n, hn, rfl⟩ := hg
        exact ⟨∑ d ∈ n.divisors, ramanujanPacketHilbert d,
          packetSum_mem_full n, packetSum_sequence n hn⟩
      | zero =>
        refine ⟨0, fullPacketSpace.zero_mem, ?_⟩
        funext k
        cases k <;> simp [hilbertSequence]
      | add g h hg hh ihg ihh =>
        obtain ⟨G, hG, hseqG⟩ := ihg
        obtain ⟨H, hH, hseqH⟩ := ihh
        refine ⟨G + H, fullPacketSpace.add_mem hG hH, ?_⟩
        change hilbertSequenceLinear (G + H) = g + h
        rw [map_add]
        change hilbertSequence G + hilbertSequence H = g + h
        rw [hseqG, hseqH]
      | smul c g hg ih =>
        obtain ⟨G, hG, hseqG⟩ := ih
        refine ⟨c • G, fullPacketSpace.smul_mem c hG, ?_⟩
        change hilbertSequenceLinear (c • G) = c • g
        rw [map_smul]
        change c • hilbertSequence G = c • g
        rw [hseqG]
    intro F hF
    have hseq : hilbertSequence F ∈ Submodule.span ℝ
        {g : ℕ → ℝ | ∃ n : ℕ, 0 < n ∧ g = residue n} := by
      rw [← legalSeedSpan_positive_eq_residue_span]
      exact hF
    obtain ⟨G, hG, he⟩ := hex (hilbertSequence F) hseq
    have hGF : G = F := hilbertSequence_injective he
    simpa only [hGF] using hG

/-- The arithmetic packet-closure hypothesis has the same actual RH endpoint
as the positive-seed residue closure. -/
theorem riemannHypothesis_of_mem_fullPacketClosure
    (hmem : hilbertOne ∈ fullPacketSpace.topologicalClosure) : RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure (Set.Ici 1)
    (by intro a ha; change 1 ≤ a at ha; omega)
  change hilbertOne ∈ (hilbertLegalSubspace (Set.Ici 1)).topologicalClosure
  rwa [← fullPacketSpace_eq_legalSubspace]

/-- Any sequence of conductor fits with vanishing complete error proves RH.
Neither cofinality nor nesting is needed for this sufficient implication. -/
theorem riemannHypothesis_of_energy_tendsto_zero (Q : ℕ → ℕ)
    (hlim : Tendsto (fun n => energy (Q n)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_legal_paretoError_tendsto (Set.Ici 1)
    (by intro a ha; change 1 ≤ a at ha; omega)
    (fun n => hilbertSequence ((space (Q n)).starProjection hilbertOne))
  · intro n
    have hm : (space (Q n)).starProjection hilbertOne ∈ fullPacketSpace :=
      space_le_full (Q n) ((space (Q n)).starProjection_apply_mem _)
    rw [fullPacketSpace_eq_legalSubspace] at hm
    exact hm
  · have he : (fun n => paretoError
          (hilbertSequence ((space (Q n)).starProjection hilbertOne))) =
        fun n => energy (Q n) := by
      funext n
      rw [← hilbertOne_sub_norm_sq_eq_paretoError]
      rfl
    rwa [he]

/-- The missing cumulative arithmetic estimate, if established for the
actual gains, proves Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_gain_not_summable (Q : ℕ → ℕ)
    (hQ : ∀ n, 0 < Q n) (hstep : ∀ n, Q n ∣ Q (n + 1))
    (hgain : ¬Summable (fun n => relativeGain (Q n) (Q (n + 1)))) :
    RiemannHypothesis :=
  riemannHypothesis_of_energy_tendsto_zero Q
    ((energy_tendsto_zero_iff_gain_not_summable Q hQ hstep).mpr hgain)

/-- Cofinality makes the cumulative-gain condition equivalent to the exact
unrestricted packet approximation statement. This is not an RH converse. -/
theorem gain_not_summable_iff_mem_fullPacketClosure (Q : ℕ → ℕ)
    (hQ : ∀ n, 0 < Q n) (hmono : ∀ m n, m ≤ n → Q m ∣ Q n)
    (hcofinal : ∀ q : ℕ, 0 < q → ∃ n, q ∣ Q n) :
    (¬Summable (fun n => relativeGain (Q n) (Q (n + 1)))) ↔
      hilbertOne ∈ fullPacketSpace.topologicalClosure :=
  (energy_tendsto_zero_iff_gain_not_summable Q hQ
    (fun n => hmono n (n + 1) (Nat.le_succ n))).symm.trans
      (energy_tendsto_zero_iff_mem_closure Q hQ hmono hcofinal)

end RiemannResearch.RH.Pareto.ConductorProjection
