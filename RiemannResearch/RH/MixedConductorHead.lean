import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.MixedConductorDilation
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.ParetoPrimePackets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact finite heads in the mixed-conductor space

The mixed-conductor CRT handoff supplies the fresh-prime replacement and the
triangular construction. Any head through H is attained in the mixed window
through s(H+1) for any prime s > H+1. A mixed vector with constant head has
complete squared error at least H+1, by the exact Pareto tail mass.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

private theorem mixed_rawResidue_head (s q H : ℕ)
    (hs : s.Prime) (hq : 0 < q) (hqs : q < s) (hHs : H < s) :
    ∃ c ∈ mixedSpace (Finset.Icc 2 (s * q)),
      ∀ n ≤ H, hilbertSequence c n = residue q n := by
  let F := q.divisors.erase 1
  let K := mixedSpace (Finset.Icc 2 (s * q))
  have hdiv (d : ℕ) (hd : d ∈ F) : 1 < d ∧ d ≤ q ∧ ¬ s ∣ d := by
    obtain ⟨hd1, hdq⟩ := Finset.mem_erase.mp hd
    have hpos := Nat.pos_of_mem_divisors hdq
    have hle := Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hdq)
    exact ⟨by omega, hle, fun hd => by have := Nat.le_of_dvd hpos hd; omega⟩
  refine ⟨-∑ d ∈ F, ramanujanPacketHilbert (s * d), K.neg_mem (K.sum_mem ?_), ?_⟩
  · intro d hd
    obtain ⟨hd1, hdq, hnd⟩ := hdiv d hd
    exact mixed_packet_mul_of_coprime_mem_window
      hs.one_lt hd1 (hs.coprime_iff_not_dvd.mpr hnd) (Nat.mul_le_mul_left _ hdq)
  · intro n hn
    rw [← anchoredEvaluationCLM_apply]
    simp only [map_neg, map_sum, anchoredEvaluationCLM_apply,
      hilbertSequence_ramanujanPacketHilbert, ← Finset.sum_neg_distrib]
    calc
      _ = ∑ d ∈ F, ramanujanPacket d n := by
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨hd1, _, hnd⟩ := hdiv d hd
        rw [ramanujanPacket_mul_prime_of_not_dvd s d n hs hd1 hnd]
        simp [dilation, Nat.div_eq_of_lt (hn.trans_lt hHs), ramanujanPacket, residue]
      _ = _ := by
        have h := Finset.sum_erase_add q.divisors (fun d => ramanujanPacket d n)
          (Nat.mem_divisors.mpr ⟨one_dvd q, hq.ne'⟩)
        have h1 : ramanujanPacket 1 n = 0 := by simp [ramanujanPacket, residue, Nat.mod_one]
        simpa only [F, h1, add_zero, ramanujanPacket_divisor_sum q n hq] using h

/-- The mixed dictionary realizes any finite positive-coordinate head within
an explicit cutoff depending on a fresh prime. -/
theorem exists_mixed_exact_head_at (f : ℕ → ℝ) (H s : ℕ)
    (hs : s.Prime) (hHs : H + 1 < s) :
    ∃ c ∈ mixedSpace (Finset.Icc 2 (s * (H + 1))),
      ∀ n, 0 < n → n ≤ H → hilbertSequence c n = f n := by
  let K := mixedSpace (Finset.Icc 2 (s * (H + 1)))
  have hres (q : ℕ) (hq : 0 < q) (hQ : q ≤ H + 1) :
      ∃ c ∈ K, ∀ n ≤ H, hilbertSequence c n = residue q n := by
    obtain ⟨c, hc, hh⟩ := mixed_rawResidue_head s q H hs hq (hQ.trans_lt hHs) (by omega)
    exact ⟨c, mixedSpace_mono (Finset.Icc_subset_Icc le_rfl
      (Nat.mul_le_mul_left _ hQ)) hc, hh⟩
  have hhead (m : ℕ) (hm : m ≤ H) :
      ∃ c ∈ K, ∀ n, 0 < n → n ≤ m → hilbertSequence c n = f n := by
    induction m with
    | zero =>
      exact ⟨0, K.zero_mem, fun n hpos hn => (by omega : False).elim⟩
    | succ m ih =>
      obtain ⟨c, hc, hc'⟩ := ih (by omega)
      obtain ⟨a, ha, ha'⟩ := hres (m + 2) (by omega) (by omega)
      obtain ⟨b, hb, hb'⟩ := hres (m + 1) (by omega) (by omega)
      let t : ℝ := (f (m + 1) - hilbertSequence c (m + 1)) / ((m + 1 : ℕ) : ℝ)
      refine ⟨c + t • (a - b), K.add_mem hc (K.smul_mem _ (K.sub_mem ha hb)), ?_⟩
      intro n hpos hn
      rw [← anchoredEvaluationCLM_apply]
      simp only [map_add, map_smul, map_sub, smul_eq_mul, anchoredEvaluationCLM_apply]
      rw [ha' n (by omega), hb' n (by omega)]
      by_cases he : n = m + 1
      · subst n
        simp only [residue, Nat.mod_eq_of_lt (show m + 1 < m + 2 by omega), Nat.mod_self,
          Nat.cast_zero, sub_zero, t]
        field_simp
        ring
      · have hlt : n < m + 1 := by omega
        simp [residue, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show n < m + 2 by omega),
          hc' n hpos (by omega)]
  exact hhead H le_rfl

theorem exists_mixed_exact_head (f : ℕ → ℝ) (H : ℕ) :
    ∃ M : ℕ, ∃ c ∈ mixedSpace (Finset.Icc 2 M),
      ∀ n, 0 < n → n ≤ H → hilbertSequence c n = f n := by
  obtain ⟨s, hs, hp⟩ := Nat.exists_infinite_primes (H + 2)
  exact ⟨s * (H + 1), exists_mixed_exact_head_at f H s hp (by omega)⟩

/-- The cost of an exact mixed constant head is paid by the complete tail. -/
theorem mixed_exact_head_error_sq_ge (H : ℕ) {c : ThresholdHilbert}
    (hc : c ∈ mixedClosure)
    (hhead : ∀ n, 0 < n → n ≤ H → hilbertSequence c n = 1) :
    (H : ℝ) + 1 ≤ ‖hilbertOne - c‖ ^ 2 := by
  let e := hilbertOne - c
  have he (n : ℕ) (hn : n < H) : e n = 0 := by
    have he' : hilbertSequence e (n + 1) = 0 := by
      change hilbertSequenceLinear (hilbertOne - c) (n + 1) = 0
      rw [map_sub]
      change hilbertSequence hilbertOne (n + 1) - hilbertSequence c (n + 1) = 0
      rw [hilbertOne_sequence, hhead (n + 1) (by omega) (by omega)]
      simp [zeroAnchor]
    have hs := hilbertSequence_weighted_square e n
    rw [he', zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hs
    simpa only [pow_two, mul_eq_zero, or_self] using hs.symm
  have hm : inner ℝ hilbertOne e = 1 := by
    have h := (mixedClosure.mem_orthogonal hilbertOne).mp one_mem_mixedClosure_orthogonal c hc
    rw [real_inner_comm] at h
    simp only [e, inner_sub_right, h, real_inner_self_eq_norm_sq, hilbertOne_norm_sq, sub_zero]
  have ht : ‖hilbertTailShift hilbertOne H‖ ^ 2 ≤ 1 / ((H : ℝ) + 1) := by
    simpa using hilbertTailShift_norm_sq_le_of_bounded hilbertOne H 1 (by norm_num)
      (fun n hn => by simp [hilbertOne_sequence, zeroAnchor, hn.ne'])
  have hp := hilbertTailShift_inner_sq_le hilbertOne e H he
  rw [hm, one_pow] at hp
  have hb := hp.trans (mul_le_mul_of_nonneg_right ht (sq_nonneg ‖e‖))
  rw [one_div, ← div_eq_inv_mul] at hb
  simpa only [one_mul] using (le_div_iff₀ (by positivity : 0 < (H : ℝ) + 1)).mp hb

end RiemannResearch.RH.Pareto.PrimePowerSchur

namespace RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
open PrimePowerSchur

/-- A mixed correction with exact centered head must carry the entire
canonical dual pairing in the physical tail. -/
theorem centeredInput_exact_head_tail_product_lower (N H : ℕ) {c : ThresholdHilbert}
    (hc : c ∈ mixedClosure) (hhead : ∀ n < H, c n = centeredInput N n) :
    (Chebyshev.psi (N : ℝ)) ^ 2 * (‖normalizedScreenedTwo - hilbertOne‖ ^ 2) ^ 2 ≤
      ‖hilbertTailShift (normalizedScreenedTwo - hilbertOne) H‖ ^ 2 *
        ‖centeredInput N - c‖ ^ 2 := by
  let e := normalizedScreenedTwo - hilbertOne
  have hu : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal (ramanujanPacketHilbert 2))
  have he : e ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.sub_mem hu one_mem_mixedClosure_orthogonal
  have hz : inner ℝ e (centeredInput N - c) = Chebyshev.psi (N : ℝ) * ‖e‖ ^ 2 := by
    rw [real_inner_comm, inner_sub_left, (mixedClosure.mem_orthogonal _).mp he _ hc, sub_zero,
      ← fullScreening_inner_right_of_orthogonal _ _ he, fullScreening_centeredInput,
      real_inner_smul_left]
    exact congrArg (Chebyshev.psi (N : ℝ) * ·) (real_inner_self_eq_norm_sq _)
  have ht := hilbertTailShift_inner_sq_le e (centeredInput N - c) H (fun n hn => by
    change centeredInput N n - c n = 0
    rw [hhead n hn, sub_self])
  rw [hz, mul_pow] at ht
  exact ht

/-- A bounded normalized complete error suffices when the corrected heads
are exact and cofinal. The boundedness hypothesis remains an arithmetic goal. -/
theorem riemannHypothesis_of_bounded_centeredInput_exact_head
    (H : ℕ → ℕ) (c : ℕ → ThresholdHilbert) (hH : Tendsto H atTop atTop)
    (hc : ∀ N, c N ∈ mixedClosure)
    (hhead : ∀ N n, n < H N → c N n = centeredInput N n)
    (A : ℝ) (hA : ∀ N ≥ 2,
      ‖centeredInput N - c N‖ ^ 2 ≤ A * (Chebyshev.psi (N : ℝ)) ^ 2) :
    RiemannHypothesis := by
  let e := normalizedScreenedTwo - hilbertOne
  have hb : ∀ᶠ N in atTop, (‖e‖ ^ 2) ^ 2 ≤ ‖hilbertTailShift e (H N)‖ ^ 2 * A := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hp := sq_pos_of_pos (psi_pos hN)
    have hmul : (Chebyshev.psi (N : ℝ)) ^ 2 * (‖e‖ ^ 2) ^ 2 ≤
        (Chebyshev.psi (N : ℝ)) ^ 2 * (‖hilbertTailShift e (H N)‖ ^ 2 * A) := by
      calc
        _ ≤ ‖hilbertTailShift e (H N)‖ ^ 2 * ‖centeredInput N - c N‖ ^ 2 :=
          centeredInput_exact_head_tail_product_lower N (H N) (hc N) (hhead N)
        _ ≤ ‖hilbertTailShift e (H N)‖ ^ 2 * (A * (Chebyshev.psi (N : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left (hA N hN) (sq_nonneg _)
        _ = _ := by ring
    by_contra! hbad
    exact (not_lt_of_ge hmul) (mul_lt_mul_of_pos_left hbad hp)
  have ht : Tendsto (fun N => ‖hilbertTailShift e (H N)‖ ^ 2 * A) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      ((hilbertTailShift_energy_tendsto_zero e).comp hH).mul_const A
  have he : (‖e‖ ^ 2) ^ 2 = 0 := le_antisymm (ge_of_tendsto ht hb) (sq_nonneg _)
  simp only [pow_two, mul_eq_zero, or_self] at he
  exact riemannHypothesis_of_normalizedScreenedTwo (sub_eq_zero.mp (norm_eq_zero.mp he))

end RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
