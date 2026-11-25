import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.TwoSeedHeadEnergyGeometry
import RiemannResearch.RH.ParetoCompactHead

/-!
# Finite mixed interpolation on physical Pareto heads

A fresh prime reverses a packet below that prime. This transfers finite
two-seed interpolation to genuine finite windows of mixed conductors.
At a fixed head, the mixed interpolants give a continuous correction
operator and preserve density in each exact-head fiber.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadMixedInterpolation
open FiniteTwoSeedCompletion TwoSeedExactHeadEnergy

/-- The algebraic union of finite mixed conductor windows. -/
abbrev finiteMixedSpan : Submodule ℝ ThresholdHilbert :=
  ⨆ B : ℕ, mixedSpace (Finset.Icc 2 B)

theorem mem_finiteMixedSpan_iff {m : ThresholdHilbert} :
    m ∈ finiteMixedSpan ↔ ∃ B : ℕ, m ∈ mixedSpace (Finset.Icc 2 B) := by
  apply Submodule.mem_iSup_of_directed
  intro i j
  exact ⟨max i j, mixedSpace_mono (Finset.Icc_subset_Icc le_rfl (le_max_left _ _)),
    mixedSpace_mono (Finset.Icc_subset_Icc le_rfl (le_max_right _ _))⟩

/-- The original packet on any head below a fresh prime is the negative
of one mixed packet on the same head. -/
theorem fresh_prime_packet_head (p q n : ℕ) (hp : p.Prime)
    (hq : 1 < q) (hpq : ¬ p ∣ q) (hn : n < p) :
    ramanujanPacket (p * q) n = -ramanujanPacket q n := by
  rw [ramanujanPacket_mul_prime_of_not_dvd p q n hp hq hpq]
  simp [dilation, Nat.div_eq_of_lt hn, ramanujanPacket, residue]

private theorem packet_head_in_mixed_range (N q : ℕ) (hq : 1 < q) :
    ∃ m ∈ finiteMixedSpan, ∀ i : Fin N,
      headRestriction N m i = ramanujanPacket q (i.val + 1) := by
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max N q + 1)
  have hpq : ¬ p ∣ q := fun h => by
    have := Nat.le_of_dvd (by omega : 0 < q) h
    omega
  have hm := mixed_packet_mul_of_coprime_mem_window hp.one_lt hq
    (hp.coprime_iff_not_dvd.mpr hpq) (le_refl (p * q))
  refine ⟨-ramanujanPacketHilbert (p * q),
    finiteMixedSpan.neg_mem (mem_finiteMixedSpan_iff.mpr ⟨p * q, hm⟩), ?_⟩
  intro i
  have hi := i.isLt
  have hn : i.val + 1 < p := by omega
  rw [headRestriction_apply, ← anchoredEvaluationCLM_apply, map_neg, anchoredEvaluationCLM_apply,
    hilbertSequence_ramanujanPacketHilbert, fresh_prime_packet_head p q _ hp hq hpq hn, neg_neg]

private theorem legal_head_in_mixed_range (N : ℕ) (v : ℕ → ℝ)
    (hv : v ∈ legalSeedSpan ({2, 3} : Set ℕ)) :
    ∃ m ∈ finiteMixedSpan, ∀ i : Fin N, headRestriction N m i = v (i.val + 1) := by
  rw [twoSeedSpan_eq_ramanujanSpan] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨q, hq, _, rfl⟩ := hx
      exact packet_head_in_mixed_range N q hq
  | zero =>
      exact ⟨0, finiteMixedSpan.zero_mem, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, hax⟩ := ihx
      obtain ⟨b, hb, hby⟩ := ihy
      exact ⟨a + b, finiteMixedSpan.add_mem ha hb, fun i => by
        simp only [map_add, Pi.add_apply, hax, hby]⟩
  | smul c x hx ih =>
      obtain ⟨a, ha, hax⟩ := ih
      exact ⟨c • a, finiteMixedSpan.smul_mem c ha, fun i => by
        simp only [map_smul, Pi.smul_apply, hax]⟩

/-- The actual finite mixed span realizes arbitrary values on a physical head. -/
theorem exists_mixed_head (N : ℕ) (a : Fin N → ℝ) :
    ∃ m : ThresholdHilbert, m ∈ finiteMixedSpan ∧ headRestriction N m = a := by
  let f : ℕ → ℝ := fun n => if h : n - 1 < N then a ⟨n - 1, h⟩ else 0
  obtain ⟨v, hv, hh⟩ := exists_head f N
  obtain ⟨m, hm, he⟩ := legal_head_in_mixed_range N v (budgetSpan_le_legal N hv)
  refine ⟨m, hm, ?_⟩
  funext i
  have hi := i.isLt
  rw [he, hh _ (by omega) (by omega)]
  simp [f, hi]

theorem exists_finite_window_mixed_head (N : ℕ) (a : Fin N → ℝ) :
    ∃ B : ℕ, ∃ m : ThresholdHilbert,
      m ∈ mixedSpace (Finset.Icc 2 B) ∧ headRestriction N m = a := by
  obtain ⟨m, hm, h⟩ := exists_mixed_head N a
  obtain ⟨B, hB⟩ := mem_finiteMixedSpan_iff.mp hm
  exact ⟨B, m, hB, h⟩

/-- One finite mixed correction prescribes the entire head without changing
the Pareto mean of the starting vector. -/
theorem exists_finite_window_head_preserving_mean (v : ThresholdHilbert) (N : ℕ)
    (a : Fin N → ℝ) :
    ∃ B : ℕ, ∃ m : ThresholdHilbert, m ∈ mixedSpace (Finset.Icc 2 B) ∧
      headRestriction N (v + m) = a ∧
      inner ℝ (v + m) hilbertOne = inner ℝ v hilbertOne := by
  obtain ⟨B, m, hm, hh⟩ := exists_finite_window_mixed_head N (a - headRestriction N v)
  have hz := ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero m).mp
    (mixedSpace_window_le_closure B hm)).2
  refine ⟨B, m, hm, ?_, ?_⟩
  · rw [map_add, hh]
    abel
  · rw [inner_add_left, hz, add_zero]

private def headBasis (N : ℕ) (i : Fin N) : ThresholdHilbert :=
  Classical.choose (exists_mixed_head N (fun j => if i = j then 1 else 0))

private theorem headBasis_spec (N : ℕ) (i : Fin N) :
    headBasis N i ∈ finiteMixedSpan ∧
    headRestriction N (headBasis N i) = fun j => if i = j then 1 else 0 :=
  Classical.choose_spec (exists_mixed_head N (fun j => if i = j then 1 else 0))

/-- A fixed-head continuous correction taking values in the algebraic mixed span. -/
def mixedHeadRepair (N : ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ∑ i : Fin N, (physicalEvaluation i.val).smulRight (headBasis N i)

theorem mixedHeadRepair_apply (N : ℕ) (v : ThresholdHilbert) :
    mixedHeadRepair N v = ∑ i : Fin N, (headRestriction N v i) • headBasis N i := by
  simp [mixedHeadRepair]

theorem mixedHeadRepair_mem (N : ℕ) (v : ThresholdHilbert) :
    mixedHeadRepair N v ∈ finiteMixedSpan := by
  rw [mixedHeadRepair_apply]
  exact finiteMixedSpan.sum_mem (fun i _ => finiteMixedSpan.smul_mem _ (headBasis_spec N i).1)

theorem mixedHeadRepair_restrict (N : ℕ) (v : ThresholdHilbert) :
    headRestriction N (mixedHeadRepair N v) = headRestriction N v := by
  rw [mixedHeadRepair_apply, map_sum]
  funext j
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [(headBasis_spec N _).2]
  simp [mul_ite]

/-- Finite mixed interpolation is dense in each exact finite-head fiber. -/
theorem exists_mixed_near_with_same_head {f : ThresholdHilbert} (hf : f ∈ mixedClosure)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ThresholdHilbert, m ∈ finiteMixedSpan ∧
      headRestriction N m = headRestriction N f ∧ ‖f - m‖ < ε := by
  let L := mixedHeadRepair N
  have hL : 0 < 1 + ‖L‖ := by positivity
  have hf' : f ∈ closure (finiteMixedSpan : Set ThresholdHilbert) := hf
  obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.mp hf' _ (div_pos hε hL)
  refine ⟨g + L (f - g), finiteMixedSpan.add_mem hg (mixedHeadRepair_mem N _), ?_, ?_⟩
  · rw [map_add, mixedHeadRepair_restrict, map_sub]
    abel
  · have he : f - (g + L (f - g)) = (f - g) - L (f - g) := by abel
    have hsmall := (lt_div_iff₀ hL).mp (show ‖f - g‖ < ε / (1 + ‖L‖) by
      simpa only [dist_eq_norm] using hd)
    rw [he]
    calc
      _ ≤ ‖f - g‖ + ‖L (f - g)‖ := norm_sub_le _ _
      _ ≤ ‖f - g‖ + ‖L‖ * ‖f - g‖ := add_le_add le_rfl (L.le_opNorm _)
      _ < ε := by nlinarith

theorem compactHead_eq_of_headRestriction_eq {N : ℕ} {x y : ThresholdHilbert}
    (h : headRestriction N x = headRestriction N y) : compactHead N x = compactHead N y := by
  apply hilbertSequence_injective
  funext n
  rw [compactHead_sequence, compactHead_sequence]
  by_cases hn : n ≤ N
  · rw [if_pos hn, if_pos hn]
    cases n with
    | zero => simp
    | succ k =>
        simpa only [headRestriction_apply] using congrFun h (⟨k, by omega⟩ : Fin N)
  · rw [if_neg hn, if_neg hn]

/-- In every affine translate of the mixed closure, approximation by one
finite conductor window can preserve the physical head exactly. -/
theorem exists_finite_window_near_with_same_head (v : ThresholdHilbert)
    {f : ThresholdHilbert} (hf : f - v ∈ mixedClosure) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∃ m : ThresholdHilbert, m ∈ mixedSpace (Finset.Icc 2 B) ∧
      compactHead N (v + m) = compactHead N f ∧ ‖f - (v + m)‖ < ε := by
  obtain ⟨m, hm, hh, herr⟩ := exists_mixed_near_with_same_head hf N hε
  obtain ⟨B, hB⟩ := mem_finiteMixedSpan_iff.mp hm
  refine ⟨B, m, hB, compactHead_eq_of_headRestriction_eq ?_, ?_⟩
  · rw [map_add, hh, map_sub]
    abel
  · have he : f - (v + m) = (f - v) - m := by abel
    rw [he]
    exact herr

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadMixedInterpolation
