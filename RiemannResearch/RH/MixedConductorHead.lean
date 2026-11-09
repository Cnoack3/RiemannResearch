import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.MixedConductorDilation
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.ParetoHeadMeanEnergy
import RiemannResearch.RH.ThresholdJointAdjointTail
import Mathlib.Tactic.Abel
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
open CoefficientStabilization PsiNormalizedRamanujan

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

/-- Exact head and zero mean force the sharp universal tail cost and retain
the remaining norm as a separate square. -/
theorem mixed_exactHead_one_error (H : ℕ) {c : ThresholdHilbert} (hc : c ∈ mixedClosure)
    (hhead : ∀ n, 0 < n → n ≤ H → hilbertSequence c n = 1) :
    ‖hilbertOne - c‖ ^ 2 = (H : ℝ) + 1 +
      ‖hilbertOne - c - ((H : ℝ) + 1) • paretoTail H‖ ^ 2 := by
  let f := hilbertOne - c
  have hzero (k : ℕ) (hk : k < H) : hilbertGibbsPhysical f k = 0 := by
    rw [hilbertGibbsPhysical_eq, show f = hilbertOne - c from rfl, hilbertSequence_sub,
      Pi.sub_apply, hilbertOne_sequence, hhead (k + 1) (by omega) (by omega)]
    simp [zeroAnchor]
  have hm : inner ℝ f hilbertOne = 1 := by
    change inner ℝ (hilbertOne - c) hilbertOne = 1
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
      mixedClosure.inner_right_of_mem_orthogonal hc one_mem_mixedClosure_orthogonal, sub_zero]
  have hheadMean : paretoHeadMean H f = 0 := by
    unfold paretoHeadMean
    exact Finset.sum_eq_zero (fun k hk => by rw [hzero k (Finset.mem_range.mp hk), mul_zero])
  have hheadVec : paretoHead H f = 0 := by
    unfold paretoHead
    exact Finset.sum_eq_zero (fun k hk => by rw [hzero k (Finset.mem_range.mp hk), zero_smul])
  have hsum : (∑ k ∈ Finset.range H, paretoWeight k * hilbertGibbsPhysical f k ^ 2) = 0 :=
    Finset.sum_eq_zero (fun k hk => by rw [hzero k (Finset.mem_range.mp hk)]; simp)
  have h := paretoHeadMean_energy_identity H f
  rw [hsum, hm, hheadMean, paretoHeadMeanMinimizer, hheadVec, hm, hheadMean] at h
  simpa only [sub_zero, one_pow, mul_one, zero_add] using h

/-- The cost of an exact mixed constant head is paid by the complete tail. -/
theorem mixed_exact_head_error_sq_ge (H : ℕ) {c : ThresholdHilbert}
    (hc : c ∈ mixedClosure)
    (hhead : ∀ n, 0 < n → n ≤ H → hilbertSequence c n = 1) :
    (H : ℝ) + 1 ≤ ‖hilbertOne - c‖ ^ 2 := by
  rw [mixed_exactHead_one_error H hc hhead]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- For an exact finite head, the remaining norm is exactly the complete
physical Pareto tail of the signed residual. -/
theorem exactHead_error_eq_tail (H : ℕ) (z c : ThresholdHilbert)
    (h : ∀ n, 0 < n → n ≤ H → hilbertSequence c n = hilbertSequence z n) :
    ‖z - c‖ ^ 2 = hilbertTailEnergy (z - c) (H + 1) := by
  have hz : (∑ k ∈ Finset.range (H + 1),
      positiveWeight k * hilbertSequence (z - c) k ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    · rw [hilbertSequence_sub, Pi.sub_apply, h k (by omega) (by
        have := Finset.mem_range.mp hk
        omega)]
      simp
  simpa only [hz, zero_add] using (hilbert_head_add_tailEnergy (z - c) (H + 1)).symm

theorem exactHead_tail_eq_covariance_add (N M H : ℕ) {c : ThresholdHilbert}
    (hc : c ∈ mixedSpace (window M))
    (h : ∀ n, 0 < n → n ≤ H → hilbertSequence c n = hilbertSequence (centeredInput N) n) :
    hilbertTailEnergy (centeredInput N - c) (H + 1) =
      offDiagonalCovarianceMass N M +
        ‖(mixedSpace (window M)).starProjection (centeredInput N) - c‖ ^ 2 := by
  let K := mixedSpace (window M)
  let z := centeredInput N
  have ho : inner ℝ (z - K.starProjection z) (K.starProjection z - c) = 0 :=
    K.inner_left_of_mem_orthogonal (K.sub_mem (K.starProjection_apply_mem z) hc)
      (K.sub_starProjection_mem_orthogonal z)
  have he : z - c = (z - K.starProjection z) + (K.starProjection z - c) := by abel
  change hilbertTailEnergy (z - c) (H + 1) = ‖z - K.starProjection z‖ ^ 2 + _
  rw [← exactHead_error_eq_tail H z c h, he, norm_add_sq_real, ho]
  ring

/-- Complete error for the one-dilation correction x - D_m x. -/
theorem centered_dilationCorrection_error_exact (m : ℕ) (hm : 0 < m)
    (x : ThresholdHilbert) :
    ‖(x - inner ℝ x hilbertOne • hilbertOne) - (x - hilbertDilation m hm x)‖ ^ 2 =
      (m : ℝ) * ‖x‖ ^ 2 - (inner ℝ x hilbertOne) ^ 2 := by
  let b := inner ℝ x hilbertOne
  have he : (x - b • hilbertOne) - (x - hilbertDilation m hm x) =
      hilbertDilation m hm x - b • hilbertOne := by abel
  have hm' : inner ℝ (hilbertDilation m hm x) hilbertOne = b := by
    simp only [b, hilbert_inner_one, hilbertDilation_mean]
  change ‖(x - b • hilbertOne) - (x - hilbertDilation m hm x)‖ ^ 2 = _
  rw [he, norm_sub_sq_real, real_inner_smul_right, hm', norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, hilbertOne_norm_sq, hilbertDilation_norm_sq]
  change _ = (m : ℝ) * ‖x‖ ^ 2 - b ^ 2
  ring

/-- A fixed input has the same complete tail obstruction for every exact head. -/
theorem mixed_exactHead_dual_tail_floor (z : ThresholdHilbert) (H : ℕ)
    {c : ThresholdHilbert} (hc : c ∈ mixedClosure) (hhead : ∀ n < H, c n = z n) :
    (‖fullScreening z‖ ^ 2) ^ 2 ≤
      ‖hilbertTailShift (fullScreening z) H‖ ^ 2 * ‖z - c‖ ^ 2 := by
  have ho := fullScreening_mem_orthogonal z
  have hp : inner ℝ (fullScreening z) (z - c) = ‖fullScreening z‖ ^ 2 := by
    rw [real_inner_comm, inner_sub_left, mixedClosure.inner_right_of_mem_orthogonal hc ho,
      sub_zero, ← fullScreening_inner_right_of_orthogonal z _ ho, real_inner_self_eq_norm_sq]
  have h := hilbertTailShift_inner_sq_le (fullScreening z) (z - c) H (fun n hn => by
    change z n - c n = 0
    rw [hhead n hn, sub_self])
  rwa [hp] at h

/-- A cofinal family of exact mixed heads for one fixed input only needs a
uniform complete energy bound. -/
theorem mem_mixedClosure_of_bounded_exact_heads (z : ThresholdHilbert)
    (H : ℕ → ℕ) (c : ℕ → ThresholdHilbert) (hH : Tendsto H atTop atTop)
    (hc : ∀ N, c N ∈ mixedClosure) (hhead : ∀ N n, n < H N → c N n = z n)
    (A : ℝ) (hA : ∀ N, ‖z - c N‖ ^ 2 ≤ A) : z ∈ mixedClosure := by
  let e := fullScreening z
  have hbound : ∀ᶠ N in atTop, (‖e‖ ^ 2) ^ 2 ≤ ‖hilbertTailShift e (H N)‖ ^ 2 * A :=
    Eventually.of_forall fun N =>
      (mixed_exactHead_dual_tail_floor z (H N) (hc N) (hhead N)).trans
        (mul_le_mul_of_nonneg_left (hA N) (sq_nonneg _))
  have ht : Tendsto (fun N => ‖hilbertTailShift e (H N)‖ ^ 2 * A) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      ((hilbertTailShift_energy_tendsto_zero e).comp hH).mul_const A
  have he : (‖e‖ ^ 2) ^ 2 = 0 := le_antisymm (ge_of_tendsto ht hbound) (sq_nonneg _)
  have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp (sq_eq_zero_iff.mp he))
  change z - mixedClosure.starProjection z = 0 at hz
  exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm

/-- Fixed-conductor RH criterion with bounded complete error and exact heads. -/
theorem riemannHypothesis_of_bounded_fixedTwo_exact_heads
    (H : ℕ → ℕ) (c : ℕ → ThresholdHilbert) (hH : Tendsto H atTop atTop)
    (hc : ∀ N, c N ∈ mixedClosure)
    (hhead : ∀ N n, n < H N →
      c N n = (ramanujanPacketHilbert 2 - Real.log 2 • hilbertOne) n)
    (A : ℝ) (hA : ∀ N,
      ‖ramanujanPacketHilbert 2 - Real.log 2 • hilbertOne - c N‖ ^ 2 ≤ A) :
    RiemannHypothesis := by
  have hz := mem_mixedClosure_of_bounded_exact_heads _ H c hH hc hhead A hA
  have hconst := closedSpace.sub_mem (packet_mem_closedSpace 2 (by decide))
    (mixedClosure_le_closedSpace hz)
  have he : ramanujanPacketHilbert 2 - (ramanujanPacketHilbert 2 - Real.log 2 • hilbertOne) =
      Real.log 2 • hilbertOne := by abel
  rw [he] at hconst
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hmem : hilbertOne ∈ closedSpace := by
    simpa only [smul_smul, inv_mul_cancel₀ hlog, one_smul] using
      closedSpace.smul_mem (Real.log 2)⁻¹ hconst
  exact riemannHypothesis_of_normalizedScreenedTwo
    (one_mem_closedSpace_iff_normalizedScreenedTwo.mp hmem)

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
