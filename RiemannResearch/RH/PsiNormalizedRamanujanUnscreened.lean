import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import RiemannResearch.RH.MixedConductorCovariance
import RiemannResearch.RH.PrimePowerPacketSummation
import RiemannResearch.RH.ThresholdJointAdjointTail
import RiemannResearch.RH.NearbyDilationGram
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unscreened psi input by prime towers

Source: user-provided Mixed Conductor CRT research handoff, Section 3.
Each prime tower telescopes before taking any Pareto norm.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
open PrimePowerSchur RiemannResearch.LinearAlgebra

def unnormalizedInput (N : ℕ) : ThresholdHilbert :=
  primeCombination (window N) (fun _ => 1)

theorem unnormalizedInput_inner_one (N : ℕ) :
    inner ℝ (unnormalizedInput N) hilbertOne = Chebyshev.psi (N : ℝ) := by
  have hpacket (q : ℕ) :
      inner ℝ (ramanujanPacketHilbert q) hilbertOne = ArithmeticFunction.vonMangoldt q := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket]
  simp only [unnormalizedInput, primeCombination, finiteSchurCombination, one_smul, sum_inner,
    hpacket, prime_source_eq_psi]

/-- Sum once per prime at its largest power in the input window. -/
theorem unnormalizedInput_sequence_primeTowers (N n : ℕ) :
    hilbertSequence (unnormalizedInput N) n =
      ∑ p ∈ N.primesLE, residue (p ^ Nat.log p N) n := by
  classical
  rw [unnormalizedInput, primeCombination, finiteSchurCombination, ← anchoredEvaluationCLM_apply,
    map_sum]
  simp only [one_smul, anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert]
  rw [Finset.sum_coe_sort (primeConductors (window N)) (fun q => ramanujanPacket q n)]
  symm
  calc
    _ = ∑ a ∈ N.primesLE.sigma (fun p => Finset.range (Nat.log p N)),
        ramanujanPacket (a.1 ^ (a.2 + 1)) n := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro p hp
      exact (sum_ramanujanPacket_prime_powers p _ n (Nat.prime_of_mem_primesLE hp)).symm
    _ = _ := by
      apply Finset.sum_bij (fun a _ => a.1 ^ (a.2 + 1))
      · rintro ⟨p, j⟩ hj
        obtain ⟨hp, hj⟩ := Finset.mem_sigma.mp hj
        obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hp
        have hj' := Finset.mem_range.mp hj
        have hN : N ≠ 0 := by have := hp.pos; omega
        have hpj := Nat.le_of_dvd (pow_pos hp.pos (j + 1)) (dvd_pow_self p (by omega : j + 1 ≠ 0))
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le.trans hpj,
          Nat.pow_le_of_le_log hN (by omega)⟩, hp.isPrimePow.pow (by omega)⟩
      · rintro ⟨p, j⟩ hp ⟨r, i⟩ hr he
        have hp := Nat.prime_of_mem_primesLE (Finset.mem_sigma.mp hp).1
        have hr := Nat.prime_of_mem_primesLE (Finset.mem_sigma.mp hr).1
        change p ^ (j + 1) = r ^ (i + 1) at he
        have hpr := congrArg Nat.minFac he
        change (p ^ (j + 1)).minFac = (r ^ (i + 1)).minFac at hpr
        rw [hp.pow_minFac (by omega), hr.pow_minFac (by omega)] at hpr
        change p = r at hpr
        subst r
        have hji := congrArg (fun q : ℕ => q.factorization p) he
        change (p ^ (j + 1)).factorization p = (p ^ (i + 1)).factorization p at hji
        rw [Nat.factorization_pow_self hp, Nat.factorization_pow_self hp] at hji
        have hi : j = i := by omega
        subst i
        rfl
      · intro q hq
        obtain ⟨hq, hpow⟩ := Finset.mem_filter.mp hq
        obtain ⟨hq2, hqN⟩ := Finset.mem_Icc.mp hq
        obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff q).mp hpow
        have hpj := Nat.le_of_dvd (pow_pos hp.pos j) (dvd_pow_self p (by omega : j ≠ 0))
        have hjN : j ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hqN
        refine ⟨⟨p, j - 1⟩, Finset.mem_sigma.mpr
          ⟨Nat.mem_primesLE.mpr ⟨hpj.trans hqN, hp⟩, Finset.mem_range.mpr (by
            change j - 1 < Nat.log p N
            omega)⟩, ?_⟩
        change p ^ (j - 1 + 1) = p ^ j
        rw [Nat.sub_add_cancel (by omega : 1 ≤ j)]
      · intro a _
        rfl

theorem unnormalizedInput_pointwise_bounds (N n : ℕ) :
    0 ≤ hilbertSequence (unnormalizedInput N) n ∧
    hilbertSequence (unnormalizedInput N) n ≤ (N.primeCounting : ℝ) * (min n N : ℕ) := by
  rw [unnormalizedInput_sequence_primeTowers]
  constructor
  · exact Finset.sum_nonneg (fun p _ => Nat.cast_nonneg (n % (p ^ Nat.log p N)))
  · calc
      _ ≤ ∑ _p ∈ N.primesLE, ((min n N : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpN := Nat.le_of_mem_primesLE hp
        have hp := Nat.prime_of_mem_primesLE hp
        have hN : N ≠ 0 := by have := hp.pos; omega
        unfold residue
        exact_mod_cast le_min (Nat.mod_le n (p ^ Nat.log p N))
          ((Nat.mod_lt n (pow_pos hp.pos (Nat.log p N))).le.trans (Nat.pow_log_le_self p hN))
      _ = _ := by simp [Nat.primesLE_card_eq_primeCounting, nsmul_eq_mul]

/-- Every prime above H contributes n throughout the head n ≤ H. -/
theorem unnormalizedInput_head_lower (N H n : ℕ) (hHN : H ≤ N) (hnH : n ≤ H) :
    ((N.primeCounting : ℝ) - (H.primeCounting : ℝ)) * n ≤
      hilbertSequence (unnormalizedInput N) n := by
  classical
  rw [unnormalizedInput_sequence_primeTowers]
  have hsub : H.primesLE ⊆ N.primesLE := by
    intro p hp
    obtain ⟨h, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨h.trans hHN, hp⟩
  have hcard : ((N.primesLE \ H.primesLE).card : ℝ) =
      (N.primeCounting : ℝ) - (H.primeCounting : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  calc
    _ = ∑ _p ∈ N.primesLE \ H.primesLE, (n : ℝ) := by
      rw [← hcard]
      simp [nsmul_eq_mul]
    _ = ∑ p ∈ N.primesLE \ H.primesLE, residue (p ^ Nat.log p N) n := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpN, hpH⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hpN
      have hpH' : H < p := lt_of_not_ge (fun h => hpH (Nat.mem_primesLE.mpr ⟨h, hp⟩))
      have hlog := Nat.log_pos hp.one_lt hpN
      have hpow := Nat.le_of_dvd (pow_pos hp.pos (Nat.log p N)) (dvd_pow_self p hlog.ne')
      rw [residue, Nat.mod_eq_of_lt (hnH.trans_lt (hpH'.trans_le hpow))]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun p _ _ => Nat.cast_nonneg (n % (p ^ Nat.log p N)))

/-- The ratio controlling every fixed unscreened coordinate tends to zero. -/
theorem primeCounting_div_psi_tendsto :
    Tendsto (fun N : ℕ => (N.primeCounting : ℝ) / Chebyshev.psi (N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨c, hc, he⟩ := RiemannResearch.NumberTheory.PrimeNumberTheorem.pi_alt
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hc' : Tendsto (fun N : ℕ => c (N : ℝ)) atTop (𝓝 0) :=
    ((Asymptotics.isLittleO_one_iff ℝ).mp hc).comp hcast
  have hlog : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hcast)
  have hone : Tendsto (fun N : ℕ => 1 + c (N : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hc'
  have ht : Tendsto (fun N : ℕ => (1 + c (N : ℝ)) * (Real.log (N : ℝ))⁻¹ /
      (Chebyshev.psi (N : ℝ) / (N : ℝ))) atTop (𝓝 0) := by
    convert! (hone.mul hlog).div psi_div_nat_tendsto (by norm_num : (1 : ℝ) ≠ 0) using 1
    simp only [mul_zero, zero_div]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have h := he (N : ℝ)
  rw [Nat.floor_natCast] at h
  rw [h]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hlog0 : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast
    (show 1 < N by omega))).ne'
  field_simp [(psi_pos hN).ne']

theorem unscreened_pointwise_tendsto_zero (n : ℕ) :
    Tendsto (fun N : ℕ => hilbertSequence (unnormalizedInput N) n /
      Chebyshev.psi (N : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (N.primeCounting : ℝ) / Chebyshev.psi (N : ℝ) * (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using primeCounting_div_psi_tendsto.mul_const (n : ℝ)
  refine squeeze_zero (fun N => div_nonneg (unnormalizedInput_pointwise_bounds N n).1
    (Chebyshev.psi_nonneg _)) (fun N => ?_) ht
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Chebyshev.psi_nonneg _)
  exact (unnormalizedInput_pointwise_bounds N n).2.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left n N) (Nat.cast_nonneg _))

/-- Complete norm bounds before normalization, with any head H ≤ N. -/
theorem unnormalizedInput_norm_sq_bounds (N H : ℕ) (hHN : H ≤ N) :
    ((H : ℝ) / 2) * ((N.primeCounting : ℝ) - (H.primeCounting : ℝ)) ^ 2 ≤
        ‖unnormalizedInput N‖ ^ 2 ∧
    ‖unnormalizedInput N‖ ^ 2 ≤ 2 * (N : ℝ) * (N.primeCounting : ℝ) ^ 2 := by
  let f := unnormalizedInput N
  let A : ℝ := N.primeCounting
  let B : ℝ := (N.primeCounting : ℝ) - H.primeCounting
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hB : 0 ≤ B := sub_nonneg.mpr (by exact_mod_cast Nat.monotone_primeCounting hHN)
  have hw (n : ℕ) (hn : 0 < n) :
      (1 : ℝ) / 2 ≤ positiveWeight n * (n : ℝ) ^ 2 ∧
        positiveWeight n * (n : ℝ) ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have he : positiveWeight n * (n : ℝ) ^ 2 = (n : ℝ) / ((n : ℝ) + 1) := by
      unfold positiveWeight
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [he]
    exact ⟨(le_div_iff₀ (by positivity)).mpr (by linarith),
      (div_le_iff₀ (by positivity)).mpr (by linarith)⟩
  have hsplit (J : ℕ) :
      (∑ k ∈ Finset.range J, positiveWeight (k + 1) * hilbertSequence f (k + 1) ^ 2) +
        hilbertTailEnergy f (J + 1) = ‖f‖ ^ 2 := by
    have h := hilbert_head_add_tailEnergy f (J + 1)
    rw [Finset.sum_range_succ'] at h
    simpa only [hilbertSequence_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_add]
      using h
  have hnorm₁ (n : ℕ) :
      hilbertSequence f n ≤ A * (n : ℝ) :=
    (unnormalizedInput_pointwise_bounds N n).2.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left n N) hA)
  have hnorm₂ (n : ℕ) :
      hilbertSequence f n ≤ A * (N : ℝ) :=
    (unnormalizedInput_pointwise_bounds N n).2.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right n N) hA)
  have hl : ((H : ℝ) / 2) * B ^ 2 ≤
      ∑ k ∈ Finset.range H, positiveWeight (k + 1) * hilbertSequence f (k + 1) ^ 2 := by
    calc
      _ = ∑ _k ∈ Finset.range H, (1 / 2 : ℝ) * B ^ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn : k + 1 ≤ H := by have := Finset.mem_range.mp hk; omega
        have hf := pow_le_pow_left₀ (mul_nonneg hB (Nat.cast_nonneg (k + 1)))
          (unnormalizedInput_head_lower N H (k + 1) hHN hkn) 2
        calc
          _ ≤ B ^ 2 * (positiveWeight (k + 1) * ((k + 1 : ℕ) : ℝ) ^ 2) := by
            simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left (hw (k + 1) (by omega)).1 (sq_nonneg B)
          _ ≤ _ := by
            simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hf (positiveWeight_nonneg (k + 1))
  have hu : (∑ k ∈ Finset.range N, positiveWeight (k + 1) * hilbertSequence f (k + 1) ^ 2)
      ≤ (N : ℝ) * A ^ 2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range N, A ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hf := pow_le_pow_left₀ (unnormalizedInput_pointwise_bounds N (k + 1)).1
          (hnorm₁ (k + 1)) 2
        calc
          _ ≤ A ^ 2 * (positiveWeight (k + 1) * ((k + 1 : ℕ) : ℝ) ^ 2) := by
            simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hf (positiveWeight_nonneg (k + 1))
          _ ≤ _ := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (hw (k + 1) (by omega)).2 (sq_nonneg A)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have ht : hilbertTailEnergy f (N + 1) ≤ (N : ℝ) * A ^ 2 := by
    have hs := (summable_nat_add_iff (N + 1)).mpr (hilbertSequence_square_summable f)
    have hs' := ((summable_nat_add_iff (N + 1)).mpr positiveWeight_summable).mul_right
      ((A * (N : ℝ)) ^ 2)
    have he : hilbertTailEnergy f (N + 1) ≤
        ∑' k : ℕ, positiveWeight (k + (N + 1)) * (A * (N : ℝ)) ^ 2 := by
      unfold hilbertTailEnergy
      refine Summable.tsum_le_tsum (fun k => ?_) hs hs'
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (unnormalizedInput_pointwise_bounds N (k + (N + 1))).1
          (hnorm₂ (k + (N + 1))) 2) (positiveWeight_nonneg _)
    rw [tsum_mul_right, positiveWeight_tail_tsum (N + 1) (by omega)] at he
    apply he.trans
    have hN : (N : ℝ) ^ 2 / ((N : ℝ) + 1) ≤ N := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    calc
      _ = ((N : ℝ) ^ 2 / ((N : ℝ) + 1)) * A ^ 2 := by
        push_cast
        rw [mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hN (sq_nonneg A)
  change ((H : ℝ) / 2) * B ^ 2 ≤ ‖f‖ ^ 2 ∧ ‖f‖ ^ 2 ≤ 2 * (N : ℝ) * A ^ 2
  constructor
  · linarith only [hl, hsplit H, hilbertTailEnergy_nonneg f (H + 1)]
  · nlinarith only [hu, ht, hsplit N]

/-- The actual unscreened mean-one input, before mixed projection. -/
def unscreenedApproximant (N : ℕ) : ThresholdHilbert :=
  (Chebyshev.psi (N : ℝ))⁻¹ • unnormalizedInput N

theorem unscreenedApproximant_norm_sq (N : ℕ) :
    ‖unscreenedApproximant N‖ ^ 2 = ‖unnormalizedInput N‖ ^ 2 / (Chebyshev.psi (N : ℝ)) ^ 2 := by
  rw [unscreenedApproximant, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, div_eq_mul_inv,
    mul_comm]

/-- The complete unscreened energy is of order N/(log N)^2. -/
theorem unscreenedApproximant_norm_sq_eventually_bounds :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (2048 * Real.log (N : ℝ) ^ 2) ≤ ‖unscreenedApproximant N‖ ^ 2 ∧
      ‖unscreenedApproximant N‖ ^ 2 ≤ 32 * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
  obtain ⟨c, hc, hpi⟩ := RiemannResearch.NumberTheory.PrimeNumberTheorem.pi_alt
  have hc0 : Tendsto c atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp hc
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hhalf : Tendsto (fun N : ℕ => (N : ℝ) / 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [tendsto_atTop.mp hnat (2 * a)] with N hN
    exact (le_div_iff₀ (by norm_num : 0 < (2 : ℝ))).mpr (by linarith)
  have hca : ∀ᶠ N : ℕ in atTop, |c (N : ℝ)| < 1 / 10 := by
    simpa only [Function.comp_apply, Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] using
      (hc0.comp hnat).eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 10))
  have hcb : ∀ᶠ N : ℕ in atTop, |c ((N : ℝ) / 2)| < 1 / 10 := by
    simpa only [Function.comp_apply, Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] using
      (hc0.comp hhalf).eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 10))
  have hlogE : ∀ᶠ N : ℕ in atTop, 4 * Real.log 2 ≤ Real.log (N : ℝ) :=
    tendsto_atTop.mp (Real.tendsto_log_atTop.comp hnat) _
  have hpsiE : ∀ᶠ N : ℕ in atTop, |Chebyshev.psi (N : ℝ) / (N : ℝ) - 1| < 1 / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using
      psi_div_nat_tendsto.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 4, hca, hcb, hlogE, hpsiE] with N hN ha hb hlogE hpsi
  let L := Real.log (N : ℝ)
  let H := ⌊(N : ℝ) / 2⌋₊
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hL : 0 < L := Real.log_pos (by linarith)
  have hH : (H : ℝ) ≤ (N : ℝ) / 2 := Nat.floor_le (by positivity)
  have hHN : H ≤ N := by exact_mod_cast hH.trans (by linarith : (N : ℝ) / 2 ≤ N)
  have hH' : (N : ℝ) / 4 ≤ H := by
    have hh := Nat.lt_floor_add_one ((N : ℝ) / 2)
    change (N : ℝ) / 2 < (H : ℝ) + 1 at hh
    linarith
  have hLhalf : (3 / 4 : ℝ) * L ≤ Real.log ((N : ℝ) / 2) := by
    rw [Real.log_div hN0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    change 4 * Real.log 2 ≤ L at hlogE
    change _ ≤ L - Real.log 2
    linarith
  have hLhalf0 : 0 < Real.log ((N : ℝ) / 2) :=
    lt_of_lt_of_le (by positivity) hLhalf
  have ha' := abs_lt.mp ha
  have hb' := abs_lt.mp hb
  have hpN := hpi (N : ℝ)
  rw [Nat.floor_natCast] at hpN
  change (N.primeCounting : ℝ) = (1 + c (N : ℝ)) * (N : ℝ) / L at hpN
  have hpiLo : (9 / 10 : ℝ) * ((N : ℝ) / L) ≤ (N.primeCounting : ℝ) := by
    rw [hpN, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [ha'.1]) (div_nonneg hN0.le hL.le)
  have hpiUp : (N.primeCounting : ℝ) ≤ 2 * (N : ℝ) / L := by
    rw [hpN]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [ha'.2]) hN0.le) hL.le
  have hpiH : (H.primeCounting : ℝ) ≤ (11 / 15 : ℝ) * ((N : ℝ) / L) := by
    calc
      _ = (1 + c ((N : ℝ) / 2)) * ((N : ℝ) / 2) / Real.log ((N : ℝ) / 2) := hpi _
      _ ≤ (11 / 10 : ℝ) * ((N : ℝ) / 2) / Real.log ((N : ℝ) / 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith [hb'.2]) (by positivity)) hLhalf0.le
      _ ≤ (11 / 10 : ℝ) * ((N : ℝ) / 2) / ((3 / 4 : ℝ) * L) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hLhalf
      _ = _ := by field_simp; ring
  have hdiff : (N : ℝ) / (8 * L) ≤ (N.primeCounting : ℝ) - H.primeCounting := by
    have he : (N : ℝ) / (8 * L) = (1 / 8 : ℝ) * ((N : ℝ) / L) := by
      field_simp
    rw [he]
    linarith [div_nonneg hN0.le hL.le]
  have hpsi' := abs_lt.mp hpsi
  have hpsiLo : (N : ℝ) / 2 ≤ Chebyshev.psi (N : ℝ) := by
    have h : (1 / 2 : ℝ) ≤ Chebyshev.psi (N : ℝ) / (N : ℝ) := by linarith [hpsi'.1]
    simpa only [one_div, inv_mul_eq_div] using (le_div_iff₀ hN0).mp h
  have hpsiUp : Chebyshev.psi (N : ℝ) ≤ 2 * (N : ℝ) :=
    (div_le_iff₀ hN0).mp (by linarith [hpsi'.2])
  have hpsi0 : 0 < Chebyshev.psi (N : ℝ) := psi_pos (by omega)
  have hraw := unnormalizedInput_norm_sq_bounds N H hHN
  rw [unscreenedApproximant_norm_sq]
  change (N : ℝ) / (2048 * L ^ 2) ≤
      ‖unnormalizedInput N‖ ^ 2 / (Chebyshev.psi (N : ℝ)) ^ 2 ∧
    ‖unnormalizedInput N‖ ^ 2 / (Chebyshev.psi (N : ℝ)) ^ 2 ≤ 32 * (N : ℝ) / L ^ 2
  constructor
  · apply (le_div_iff₀ (pow_pos hpsi0 _)).mpr
    calc
      _ ≤ ((N : ℝ) / (2048 * L ^ 2)) * (2 * (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpsi0.le hpsiUp 2) (by positivity)
      _ = ((N : ℝ) / 8) * ((N : ℝ) / (8 * L)) ^ 2 := by field_simp; ring
      _ ≤ ((H : ℝ) / 2) * ((N.primeCounting : ℝ) - H.primeCounting) ^ 2 :=
        mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) hdiff 2)
          (sq_nonneg _) (by positivity)
      _ ≤ _ := hraw.1
  · apply (div_le_iff₀ (pow_pos hpsi0 _)).mpr
    calc
      _ ≤ 2 * (N : ℝ) * (N.primeCounting : ℝ) ^ 2 := hraw.2
      _ ≤ 2 * (N : ℝ) * (2 * (N : ℝ) / L) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hpiUp 2)
          (by positivity)
      _ = (32 * (N : ℝ) / L ^ 2) * ((N : ℝ) / 2) ^ 2 := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpsiLo 2)
        (by positivity)

/-- Exact normalized variance as the raw energy minus the mixed energy and
the unit mean contribution. -/
theorem offDiagonalCovarianceMass_div_psi_sq_eq_removed_energy
    {N : ℕ} (M : ℕ) (hN : 2 ≤ N) :
    offDiagonalCovarianceMass N M / (Chebyshev.psi (N : ℝ)) ^ 2 =
      ‖unscreenedApproximant N‖ ^ 2 -
        ‖(mixedSpace (window M)).starProjection (unscreenedApproximant N)‖ ^ 2 - 1 := by
  let K := mixedSpace (window M)
  let U := unnormalizedInput N
  let b := Chebyshev.psi (N : ℝ)
  have hK : K.starProjection hilbertOne = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff K).mpr (one_mem_mixed_orthogonal _)
  have hZ : (U - b • hilbertOne) - K.starProjection (U - b • hilbertOne) =
      (U - K.starProjection U) - b • hilbertOne := by
    rw [map_sub, map_smul, hK, smul_zero, sub_zero]
    abel
  have hmean : inner ℝ (U - K.starProjection U) hilbertOne = b := by
    rw [inner_sub_left, K.inner_right_of_mem_orthogonal (K.starProjection_apply_mem U)
      (one_mem_mixed_orthogonal _), sub_zero]
    exact unnormalizedInput_inner_one N
  have horth := K.starProjection_inner_eq_zero U (K.starProjection U)
    (K.starProjection_apply_mem U)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at horth
  have hnorm : ‖U - K.starProjection U‖ ^ 2 = ‖U‖ ^ 2 - ‖K.starProjection U‖ ^ 2 := by
    rw [norm_sub_sq_real]
    linarith only [horth]
  have hb : b ≠ 0 := (psi_pos hN).ne'
  change ‖(U - b • hilbertOne) - K.starProjection (U - b • hilbertOne)‖ ^ 2 / b ^ 2 =
    ‖b⁻¹ • U‖ ^ 2 - ‖K.starProjection (b⁻¹ • U)‖ ^ 2 - 1
  rw [hZ, norm_sub_sq_real, real_inner_smul_right, hmean, map_smul, hnorm]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertOne_norm_sq, mul_one, inv_pow]
  field_simp [hb]
  ring

end RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
