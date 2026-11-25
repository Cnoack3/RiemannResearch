import RiemannResearch.RH.PhysicalHeadSnakeSections
import RiemannResearch.RH.MixedPacketDensityTests

/-! # A square obstruction to multiplication at every positive physical head

For primes `2 < p < q`, the difference of the packets with conductors
`2*p` and `2*q` vanishes below `p` and has value `p` at `p`. Its
pointwise physical square is a genuine Pareto Hilbert vector with strictly
positive mean and zero head. No member of a positive compatible stage can
represent that square.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadPacketSquare
open CoefficientStabilization CenteredMeanSnake.PhysicalHeadSections MixedPacketDensity

/-- A finite mean-zero difference with an exactly prescribed first nonzero site. -/
def packetDifference (p q : ℕ) : ThresholdHilbert :=
  ramanujanPacketHilbert (2*p) - ramanujanPacketHilbert (2*q)

private theorem packetDifference_sequence (p q n : ℕ) :
    hilbertSequence (packetDifference p q) n =
      ramanujanPacket (2*p) n - ramanujanPacket (2*q) n := by
  rw [← anchoredEvaluationCLM_apply, packetDifference, map_sub, anchoredEvaluationCLM_apply,
    anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert,
    hilbertSequence_ramanujanPacketHilbert]

theorem packetDifference_zero_below {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) {n : ℕ} (hn : n < p) :
    hilbertSequence (packetDifference p q) n = 0 := by
  have h2p' : 2 ≠ p := by omega
  have h2q' : 2 ≠ q := by omega
  rw [← anchoredEvaluationCLM_apply, packetDifference, map_sub, anchoredEvaluationCLM_apply,
    anchoredEvaluationCLM_apply, semiprime_packet_sequence Nat.prime_two hp h2p' n,
    semiprime_packet_sequence Nat.prime_two hq h2q' n]
  simp only [residue, Nat.mod_eq_of_lt (show n < 2*p by omega), Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n < 2*q by omega), Nat.mod_eq_of_lt (hn.trans hpq), sub_self]

theorem packetDifference_at_first_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) :
    hilbertSequence (packetDifference p q) p = (p : ℝ) := by
  rw [← anchoredEvaluationCLM_apply, packetDifference, map_sub, anchoredEvaluationCLM_apply,
    anchoredEvaluationCLM_apply, semiprime_packet_sequence Nat.prime_two hp (by omega) p,
    semiprime_packet_sequence Nat.prime_two hq (by omega) p]
  simp only [residue, Nat.mod_eq_of_lt (show p < 2*p by omega), Nat.mod_self, Nat.cast_zero,
    Nat.mod_eq_of_lt (show p < 2*q by omega), Nat.mod_eq_of_lt hpq]
  ring

theorem packetDifference_mem_mixed {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) : packetDifference p q ∈ mixedClosure := by
  have hin {r : ℕ} (hr : r.Prime) (h2r : 2 < r) :
      ramanujanPacketHilbert (2*r) ∈ mixedClosure := by
    have hnot : ¬ r ∣ 2 := fun h => by
      have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega
    exact mixedSpace_window_le_closure (2*r) (mixed_packet_mul_of_coprime_mem_window
      (by decide : 1 < 2) hr.one_lt (hr.coprime_iff_not_dvd.mpr hnot).symm le_rfl)
  exact mixedClosure.sub_mem (hin hp h2p) (hin hq (h2p.trans hpq))

/-- The bounded physical difference has a square that is again square integrable. -/
private theorem square_summable (p q : ℕ) :
    Summable (fun n => positiveWeight n * ((hilbertSequence (packetDifference p q) n)^2)^2) := by
  have h := bounded_sub (ramanujanPacket_abs_le (2*p)) (ramanujanPacket_abs_le (2*q))
  simpa only [pow_two, packetDifference_sequence] using
    weighted_summable_of_bounded (bounded_product (bounded_product h h) (bounded_product h h))

def packetSquare (p q : ℕ) : ThresholdHilbert :=
  sequenceHilbert (fun n => hilbertSequence (packetDifference p q) n ^ 2) (square_summable p q)

theorem packetSquare_sequence (p q n : ℕ) :
    hilbertSequence (packetSquare p q) n = hilbertSequence (packetDifference p q) n ^ 2 := by
  rw [packetSquare, hilbertSequence_sequenceHilbert _ _ (by simp)]

theorem packetSquare_mean (p q : ℕ) :
    inner ℝ (packetSquare p q) hilbertOne = ‖packetDifference p q‖^2 := by
  rw [hilbert_inner_one, hilbert_norm_weighted_sq]
  unfold paretoMean
  simp only [packetSquare_sequence]

theorem packetSquare_mean_pos {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) : 0 < inner ℝ (packetSquare p q) hilbertOne := by
  have hn : packetDifference p q ≠ 0 := by
    intro hz
    have h := packetDifference_at_first_prime hp hq h2p hpq
    rw [hz] at h
    have hh : hilbertSequence (0 : ThresholdHilbert) p = 0 := by
      rw [← anchoredEvaluationCLM_apply, map_zero]
    rw [hh] at h
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) h.symm
  rw [packetSquare_mean]
  exact pow_pos (norm_pos_iff.mpr hn) _

private theorem compactHead_zero_of_sequence {N : ℕ} {x : ThresholdHilbert}
    (h : ∀ n ≤ N, hilbertSequence x n = 0) : compactHead N x = 0 := by
  apply hilbertSequence_injective
  funext n
  rw [compactHead_sequence]
  have h0 : hilbertSequence (0 : ThresholdHilbert) n = 0 := by
    rw [← anchoredEvaluationCLM_apply, map_zero]
  by_cases hn : n ≤ N <;> simp [hn, h0, h n]

theorem packetDifference_headCompatible {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) (hN : N < p) :
    ∃ v : closedSpace, (v : ThresholdHilbert) = packetDifference p q ∧
      v ∈ headCompatible N ∧ legalPacketMean v = 0 := by
  have hm := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp
    (packetDifference_mem_mixed hp hq h2p hpq)
  let v : closedSpace := ⟨packetDifference p q, hm.1⟩
  have hmean : legalPacketMean v = 0 := hm.2
  refine ⟨v, rfl, (mem_headCompatible_iff N v).mpr ?_, hmean⟩
  rw [hmean, zero_smul]
  exact compactHead_zero_of_sequence (fun n hn =>
    packetDifference_zero_below hp hq h2p hpq (hn.trans_lt hN))

/-- The square has zero head and nonzero mean. This excludes stage membership
even if a legal representative of the square were supplied. -/
theorem packetSquare_not_headCompatible {N p q : ℕ} (hN0 : 0 < N)
    (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) (hN : N < p) :
    ¬ ∃ v : closedSpace, (v : ThresholdHilbert) = packetSquare p q ∧ v ∈ headCompatible N := by
  rintro ⟨v, hv, hstage⟩
  have hhead : compactHead N (packetSquare p q) = 0 := by
    apply compactHead_zero_of_sequence
    intro n hn
    rw [packetSquare_sequence, packetDifference_zero_below hp hq h2p hpq (hn.trans_lt hN)]
    norm_num
  have h := (mem_headCompatible_iff N v).mp hstage
  rw [hv, hhead] at h
  have he := congrArg (anchoredEvaluationCLM 1) h
  rw [map_zero, map_smul, smul_eq_mul, anchoredEvaluationCLM_apply, compactHead_sequence,
    if_pos (show 1 ≤ N by omega), hilbertOne_sequence] at he
  have hmean : legalPacketMean v = 0 := by simpa [zeroAnchor] using he.symm
  have hpos := packetSquare_mean_pos hp hq h2p hpq
  change inner ℝ (v : ThresholdHilbert) hilbertOne = 0 at hmean
  rw [hv] at hmean
  exact (ne_of_gt hpos) hmean

/-- Every positive physical stage has a finite mixed witness whose genuine
pointwise square has no representative in that stage. -/
theorem positive_stage_not_closed_under_square (N : ℕ) (hN : 0 < N) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 < p ∧ N < p ∧ p < q ∧
      (∃ v : closedSpace, (v : ThresholdHilbert) = packetDifference p q ∧
        v ∈ headCompatible N ∧ legalPacketMean v = 0) ∧
      (¬ ∃ v : closedSpace, (v : ThresholdHilbert) = packetSquare p q ∧ v ∈ headCompatible N) := by
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max N 2 + 1)
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (p+1)
  have h2p : 2 < p := by omega
  have hNp : N < p := by omega
  have hpq : p < q := by omega
  exact ⟨p, q, hp, hq, h2p, hNp, hpq, packetDifference_headCompatible hp hq h2p hpq hNp,
    packetSquare_not_headCompatible hN hp hq h2p hpq hNp⟩

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadPacketSquare
