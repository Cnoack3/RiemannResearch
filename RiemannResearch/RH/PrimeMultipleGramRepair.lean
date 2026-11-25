import RiemannResearch.RH.CenteredMeanUnitNorm
import RiemannResearch.RH.MixedConductorBilinear
import RiemannResearch.RH.MixedPrimeCorrelationSeries
import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.ParetoConductor241Covariance
import RiemannResearch.RH.ResidueProjectionSchur
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.RamanujanMultipleCapacityLimits
import RiemannResearch.RH.RamanujanUnitMean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prime multiples as finite mean - one Gram repairs

A mixed packet gives a legal one - column correction to any finite normalized fit.
The change of squared norm is exactly its squared pairing divided by its squared norm.
For a fixed fit and a fixed mixed base, this gain along prime multiples has a
harmonic leading term with an absolutely summable error. Refitting adds a
second, nonnegative squared - distance term to each single - column improvement.

Source: the user's finite Gram extension, bilinear pairing, and prime - tower questions.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization RamanujanCanonicalOptimizer PacketGramBoundary

/-- Decrease in the squared norm from optimally moving along one packet. -/
def packetRepairGain (v : ThresholdHilbert) (q : ℕ) : ℝ :=
  (inner ℝ (ramanujanPacketHilbert q) v) ^ 2 / ‖ramanujanPacketHilbert q‖ ^ 2

/-- Subtract the minimizing scalar multiple of the test packet. -/
def packetRepair (v : ThresholdHilbert) (q : ℕ) : ThresholdHilbert :=
  v - (inner ℝ (ramanujanPacketHilbert q) v / ‖ramanujanPacketHilbert q‖ ^ 2) •
    ramanujanPacketHilbert q

private theorem packet_mem_stage (k q : ℕ) (hq : 1 < q) (hqk : q ≤ k + 2) :
    ramanujanPacketHilbert q ∈ finiteSpace (k + 1) := by
  change ramanujanPacketHilbert q ∈ Submodule.span ℝ
    (Set.range (fun i : Fin (k + 1) => residueAtom i.val))
  rw [← finitePacket_span_eq]
  let i : Fin (k + 1) := ⟨q - 2, by omega⟩
  exact Submodule.subset_span ⟨i, congrArg ramanujanPacketHilbert
    (show i.val + 2 = q by dsimp [i]; omega)⟩

private theorem repair_norm (v : ThresholdHilbert) (q : ℕ) :
    ‖packetRepair v q‖ ^ 2 = ‖v‖ ^ 2 - packetRepairGain v q := by
  let y := ramanujanPacketHilbert q
  by_cases hy : y = 0
  · simp [packetRepair, packetRepairGain, ← show y = ramanujanPacketHilbert q from rfl, hy]
  have hys : ‖y‖ ^ 2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hy)).ne'
  change ‖v - (inner ℝ y v / ‖y‖ ^ 2) • y‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ y v) ^ 2 / ‖y‖ ^ 2
  rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm v y, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [hys]
  ring

private theorem repair_mean (v : ThresholdHilbert) {q : ℕ} (hq : 1 < q)
    (hm : ¬ IsPrimePow q) :
    inner ℝ hilbertOne (packetRepair v q) = inner ℝ hilbertOne v := by
  have hz := ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp
    (mixed_packet_mem_closure q hq hm)).2
  have hz' : inner ℝ hilbertOne (ramanujanPacketHilbert q) = 0 := (real_inner_comm ..).trans hz
  rw [packetRepair, inner_sub_right, real_inner_smul_right, hz', mul_zero, sub_zero]

/-- Every arithmetic Fekete slope gives the same pairing on the repaired mean-one lift. -/
theorem repair_fekete_pairing {v h : ThresholdHilbert} (hv : v ∈ closedSpace)
    (hmean : inner ℝ v hilbertOne = 1) (hh : h ∈ mixedClosureᗮ)
    {q a : ℕ} (hq : 1 < q) (hm : ¬ IsPrimePow q) (ha : 1 < a) :
    inner ℝ h (packetRepair v q) =
      RiemannResearch.NumberTheory.powerRate (residuePairing h) a / Real.log (a : ℝ) := by
  have hym := mixed_packet_mem_closure q hq hm
  have hy := ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp hym).1
  have hw : packetRepair v q ∈ closedSpace := closedSpace.sub_mem hv (closedSpace.smul_mem _ hy)
  have he : inner ℝ (packetRepair v q) hilbertOne = 1 :=
    (real_inner_comm ..).trans ((repair_mean v hq hm).trans ((real_inner_comm ..).trans hmean))
  rw [Bilinear.pairing_eq_fekete_rate_at_base hh hw ha, he, mul_one]

/-- Complete finite Gram improvement, including the extra gain from refitting. -/
theorem packet_repair_refit_exact (n k q : ℕ) (hnk : n ≤ k)
    (hq : 1 < q) (hm : ¬ IsPrimePow q) (hqk : q ≤ k + 2) :
    (packetMass (n + 1))⁻¹ - (packetMass (k + 1))⁻¹ =
      packetRepairGain (packetUnitMean n) q +
      ‖packetRepair (packetUnitMean n) q - packetUnitMean k‖ ^ 2 := by
  have hv := RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
    (Nat.add_le_add_right hnk 1) (packetUnitMean_legal n)
  have hw : packetRepair (packetUnitMean n) q ∈ finiteSpace (k + 1) :=
    (finiteSpace _).sub_mem hv ((finiteSpace _).smul_mem _ (packet_mem_stage k q hq hqk))
  have he := packetUnitMean_completion k _ hw
    ((repair_mean _ hq hm).trans (packetUnitMean_signal n))
  rw [repair_norm, packetUnitMean_energy] at he
  linarith only [he]

private theorem finite_unit_detects_mixed (n : ℕ) {v : ThresholdHilbert} (hv : v ∈ finiteSpace n)
    (hmean : inner ℝ v hilbertOne = 1) :
    ∃ q : ℕ, 1 < q ∧ ¬ IsPrimePow q ∧ inner ℝ (ramanujanPacketHilbert q) v ≠ 0 := by
  by_contra! hzero
  let F := innerSL ℝ v
  have hker : mixedClosure ≤ F.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro N
      apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      obtain ⟨hi, hm⟩ := Finset.mem_filter.mp q.property
      change inner ℝ v (ramanujanPacketHilbert q.val) = 0
      exact (real_inner_comm ..).trans (hzero q.val (Finset.mem_Icc.mp hi).1 hm)
    · exact F.isClosed_ker
  have hvV := RamanujanMultipleCapacityLimits.finiteSpace_le_closedSpace n hv
  have huV := screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  have hd := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero (v - normalizedScreenedTwo)).mpr
    ⟨closedSpace.sub_mem hvV huV,
      by rw [inner_sub_left, hmean, normalizedScreenedTwo_mean, sub_self]⟩
  have huO : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal _)
  have he : inner ℝ (v - normalizedScreenedTwo) (v - normalizedScreenedTwo) = 0 := by
    rw [inner_sub_left, show inner ℝ v (v - normalizedScreenedTwo) = 0 from hker hd,
      show inner ℝ normalizedScreenedTwo (v - normalizedScreenedTwo) = 0 from
        (real_inner_comm ..).trans (huO _ hd), sub_self]
  exact normalizedScreenedTwo_not_mem_finiteSpace n
    ((sub_eq_zero.mp (inner_self_eq_zero.mp he)) ▸ hv)

/-- A finite full Gram optimum always detects an unfitted mixed conductor. -/
theorem optimizer_detects_mixed (n : ℕ) :
    ∃ q : ℕ, n + 2 < q ∧ ¬ IsPrimePow q ∧ 0 < packetRepairGain (packetUnitMean n) q := by
  obtain ⟨q, hq, hm, hc⟩ := finite_unit_detects_mixed (n + 1) (packetUnitMean_legal n)
    ((real_inner_comm ..).trans (packetUnitMean_signal n))
  have hfar : n + 2 < q := by
    by_contra! h
    let i : Fin (n + 1) := ⟨q - 2, by omega⟩
    have hi : i.val + 2 = q := by dsimp [i]; omega
    have he := packet_normal (n + 1) i
    rw [hi] at he
    have hz := ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp
      (mixed_packet_mem_closure q hq hm)).2
    rw [← packet_inner_one q] at he
    exact hc (by rw [packetUnitMean, real_inner_smul_right, he, hz, mul_zero])
  have hy : ramanujanPacketHilbert q ≠ 0 := fun h => hc (by simp [h])
  exact ⟨q, hfar, hm, div_pos (sq_pos_of_ne_zero hc) (sq_pos_of_pos (norm_pos_iff.mpr hy))⟩

private theorem score_remainder_bound (p d A x z B K H : ℝ) (hp : 4 ≤ p) (hd : 0 < d)
    (hBeq : B = p * d + d - 2 * z) (hb : p * d / 4 ≤ B) (hx : |x| ≤ K / p) (hz : |z| ≤ H / p) :
    |(x - A) ^ 2 / B - A ^ 2 / (p * d)| ≤
      (4 * (d * K * (2 * |A| + K) + A ^ 2 * (d + 2 * H)) / d ^ 2) / p ^ 2 := by
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hpd := mul_pos hp0 hd
  have hB0 : 0 < B := lt_of_lt_of_le (div_pos hpd (by norm_num)) hb
  have small (w L : ℝ) (hw : |w| ≤ L / p) : |w| ≤ L := calc
    |w| = |w| * 1 := (mul_one _).symm
    _ ≤ |w| * p := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
    _ ≤ L := (le_div_iff₀ hp0).mp hw
  have hpx : |p * x| ≤ K := by
    rw [abs_mul, abs_of_pos hp0, mul_comm]
    exact (le_div_iff₀ hp0).mp hx
  have hK := (abs_nonneg (p * x)).trans hpx
  have tri (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  have hx2 : |x - 2 * A| ≤ 2 * |A| + K := by
    have h := tri x (2 * A)
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    linarith only [h, small x K hx]
  have hz2 : |d - 2 * z| ≤ d + 2 * H := by
    have h := tri d (2 * z)
    rw [abs_of_pos hd, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    linarith only [h, small z H hz]
  have hN1 : |d * (p * x) * (x - 2 * A)| ≤ d * K * (2 * |A| + K) := by
    rw [abs_mul (d * (p * x)) _, abs_mul d (p * x), abs_of_pos hd]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpx hd.le) hx2 (abs_nonneg _) (mul_nonneg hd.le hK)
  have hN2 : |A ^ 2 * (d - 2 * z)| ≤ A ^ 2 * (d + 2 * H) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg A)]
    exact mul_le_mul_of_nonneg_left hz2 (sq_nonneg A)
  let N := d * (p * x) * (x - 2 * A) - A ^ 2 * (d - 2 * z)
  let Q := d * K * (2 * |A| + K) + A ^ 2 * (d + 2 * H)
  have hN : |N| ≤ Q := (tri _ _).trans (add_le_add hN1 hN2)
  have hQ : 0 ≤ Q := (abs_nonneg N).trans hN
  have hden : p ^ 2 * d ^ 2 / 4 ≤ p * d * B := calc
    _ = p * d * (p * d / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hpd.le
  have hid : (x - A) ^ 2 / B - A ^ 2 / (p * d) = N / (p * d * B) := by
    dsimp only [N]
    field_simp [hp0.ne', hd.ne', hB0.ne']
    rw [hBeq]
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hpd hB0)]
  calc
    _ ≤ Q / (p * d * B) := (div_le_div_iff_of_pos_right (mul_pos hpd hB0)).mpr hN
    _ ≤ Q / (p ^ 2 * d ^ 2 / 4) := div_le_div_of_nonneg_left hQ (by positivity) hden
    _ = _ := by dsimp only [Q]; field_simp [hp0.ne', hd.ne']

/-- On every frozen finite fit, the prime-multiple gain has exactly the base
packet gain as its harmonic coefficient, with a quadratic remainder. -/
theorem prime_repair_harmonic_remainder (n : ℕ) {v : ThresholdHilbert} (hv : v ∈ finiteSpace n)
    {q : ℕ} (hq : 1 < q) (hm : ¬ IsPrimePow q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, p.Prime → 4 ≤ p → q < p →
      |packetRepairGain v (p * q) - packetRepairGain v q / p| ≤ C / (p : ℝ) ^ 2 := by
  let f := ramanujanPacketHilbert q
  by_cases hf : f = 0
  · refine ⟨0, le_rfl, fun p hp _ hlt => ?_⟩
    have he : ramanujanPacketHilbert (p * q) = 0 := by
      rw [packet_prime_mul_sub_dilation hp hq hlt]
      change hilbertDilationLinear p hp.pos f - f = 0
      rw [hf, map_zero, sub_zero]
    simp [packetRepairGain, he, show ramanujanPacketHilbert q = 0 from hf]
  have hd : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  have hzero := ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero f).mp
    (mixed_packet_mem_closure q hq hm)).2
  obtain ⟨Kv, hKv, hvb⟩ := finite_fit_dilated_pair_bound n hv
  obtain ⟨Kf, hKf, hfb⟩ := finite_fit_dilated_pair_bound (q + 1) (packet_mem_stage q q hq (by omega))
  let K := Kv * ‖f‖
  let H := Kf * ‖f‖
  let A := inner ℝ f v
  let d := ‖f‖ ^ 2
  refine ⟨4 * (d * K * (2 * |A| + K) + A ^ 2 * (d + 2 * H)) / d ^ 2, by dsimp [d,K,H]; positivity, ?_⟩
  intro p hp hp4 hlt
  let x := hilbertDilation p hp.pos f
  let y := ramanujanPacketHilbert (p * q)
  have hy : y = x - f := packet_prime_mul_sub_dilation hp hq hlt
  have hB : ‖y‖ ^ 2 = (p : ℝ) * d + d - 2 * inner ℝ x f := by
    rw [hy, norm_sub_sq_real, hilbertDilation_norm_sq]
    dsimp [d]; ring
  have hlow : (p : ℝ) * d / 4 ≤ ‖y‖ ^ 2 := by
    have hb := prime_multiple_norm_lower hp hp4 hq hlt
    change (p : ℝ) * d ≤ 4 * ‖y‖ ^ 2 at hb
    linarith only [hb]
  have h := score_remainder_bound (p : ℝ) d A (inner ℝ x v) (inner ℝ x f) (‖y‖ ^ 2) K H
    (by exact_mod_cast hp4) hd hB hlow (hvb f hzero p hp.pos) (hfb f hzero p hp.pos)
  have he : inner ℝ y v = inner ℝ x v - A := by rw [hy, inner_sub_left]
  change |(inner ℝ y v) ^ 2 / ‖y‖ ^ 2 - A ^ 2 / d / (p : ℝ)| ≤ _
  rwa [he, div_div, mul_comm d (p : ℝ)]

/-- The entire error after removing the harmonic term is absolutely summable. -/
theorem summable_prime_repair_remainder (n : ℕ) {v : ThresholdHilbert} (hv : v ∈ finiteSpace n)
    {q N : ℕ} (hq : 1 < q) (hm : ¬ IsPrimePow q) (hqN : q < N) (hN : 4 ≤ N) :
    Summable (fun p : {p : ℕ // p.Prime ∧ N ≤ p} =>
      |packetRepairGain v (p.val * q) - packetRepairGain v q / p.val|) := by
  obtain ⟨C, _, hC⟩ := prime_repair_harmonic_remainder n hv hq hm
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  have hsum := (hs.comp_injective
    (Subtype.val_injective (p := fun p : ℕ => p.Prime ∧ N ≤ p))).mul_left C
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ hsum
  intro p
  simpa only [Function.comp_apply, mul_one_div] using
    hC p.val p.property.1 (hN.trans p.property.2) (hqN.trans_le p.property.2)

/-- Every full finite optimum admits a strict repair along every sufficiently
large prime multiple of one unfitted mixed conductor. The full Gram improvement
at the specified cutoff is at least half the base gain divided by the prime. -/
theorem optimizer_prime_repair_gain (n : ℕ) :
    ∃ q N : ℕ, n + 2 < q ∧ ¬ IsPrimePow q ∧ 0 < packetRepairGain (packetUnitMean n) q ∧
      ∀ p : ℕ, p.Prime → N ≤ p →
        packetRepairGain (packetUnitMean n) q / (2 * p) ≤
          (packetMass (n + 1))⁻¹ - (packetMass (p * q - 1))⁻¹ := by
  obtain ⟨q, hfar, hm, ha⟩ := optimizer_detects_mixed n
  have hq : 1 < q := by omega
  let A := packetRepairGain (packetUnitMean n) q
  obtain ⟨C, _, hC⟩ := prime_repair_harmonic_remainder (n + 1) (packetUnitMean_legal n) hq hm
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * C / A)
  refine ⟨q, max (max 4 (q + 1)) M, hfar, hm, ha, ?_⟩
  intro p hp hl
  have hp4 : 4 ≤ p := by omega
  have hlt : q < p := by omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have haR : 0 < A := ha
  have hmR : (M:ℝ) ≤ p := by exact_mod_cast (show M ≤ p by omega)
  have hprod : 2 * C < (p : ℝ) * A :=
    ((div_lt_iff₀ haR).mp hM).trans_le (mul_le_mul_of_nonneg_right hmR haR.le)
  have hsmall : C / (p : ℝ) ^ 2 ≤ A / (2 * (p : ℝ)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hpR) (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_right hprod.le hpR.le]
  have he := (abs_le.mp (hC p hp hp4 hlt)).1
  have hs : A / (2 * (p : ℝ)) ≤ packetRepairGain (packetUnitMean n) (p * q) := by
    change - (C / (p : ℝ) ^ 2) ≤ packetRepairGain (packetUnitMean n) (p * q) - A / p at he
    have hi : A / (p : ℝ) = 2 * (A / (2 * (p : ℝ))) := by ring
    linarith only [he, hsmall, hi]
  have hlarge := Nat.le_mul_of_pos_left q hp.pos
  have hmix : ¬ IsPrimePow (p * q) := fun h => hm (h.dvd (dvd_mul_left q p) (by omega))
  have hr := packet_repair_refit_exact n (p * q - 2) (p * q) (by omega) (by omega) hmix (by omega)
  rw [show p * q - 2 + 1 = p * q - 1 by omega] at hr
  change A / (2 * (p : ℝ)) ≤ _
  have hrem := sq_nonneg ‖packetRepair (packetUnitMean n) (p * q) - packetUnitMean (p * q - 2)‖
  linarith only [hr, hs, hrem]


/-- At a given starting cutoff, the attainable budgets form an open ray whose
endpoint is the squared norm of the actual centered boundary. -/
theorem later_excess_below_iff_boundary_lt (n : ℕ) (t : ℝ) :
    (∃ m : ℕ, n < m ∧ (packetMass (m + 1))⁻¹ - 1 < t) ↔ ‖boundary‖ ^ 2 < t := by
  have hu : ‖normalizedScreenedTwo‖ ^ 2 = 1 + ‖boundary‖ ^ 2 := by
    linarith only [boundary_norm_sq]
  have ht : Tendsto (fun m : ℕ => (packetMass (m + 1))⁻¹) atTop (𝓝 (1 + ‖boundary‖ ^ 2)) := by
    simpa only [← packetUnitMean_energy, packetUnitMeanLimit_eq_screened, hu] using
      (packetUnitMean_tendsto.norm.pow 2)
  constructor
  · rintro ⟨m, _, hm⟩
    have h := (inv_lt_inv₀ packetLimitMass_pos (packetMass_pos (m + 1) (by omega))).2
      (packetMass_lt_limitMass (m + 1))
    rw [← packetUnitMeanLimit_energy, packetUnitMeanLimit_eq_screened, hu] at h
    linarith only [h, hm]
  · intro h
    have he := (tendsto_order.mp ht).2 (1 + t) (by linarith only [h])
    obtain ⟨m, hm, hn⟩ := (he.and (eventually_gt_atTop n)).exists
    exact ⟨m, hn, by linarith only [hm]⟩

/-- The original conductor-two dictionary has a certified fiftyfold reduction
of its excess squared norm at the full dictionary through conductor 241. -/
theorem first_gram_excess_fiftyfold :
    (packetMass 240)⁻¹ - 1 < ((packetMass 1)⁻¹ - 1) / 50 := by
  have hfirst : (1000000 / 693148 : ℝ) ≤ (packetMass 1)⁻¹ := by
    rw [packetMass_eq_captured, ProjectionSchur.captured_one, ← one_div]
    apply (le_div_iff₀ (Real.log_pos (by norm_num))).2
    linarith only [Real.log_two_lt_d9]
  have hcert : (packetMass 240)⁻¹ ≤ (1000000 / 991224 : ℝ) := by
    rw [← one_div]
    apply (div_le_iff₀ (packetMass_pos 240 (by decide))).2
    have he := GroupedResidueMass.Conductor241.energy_le_conductor_241_covariance
    rw [packet_energy_eq_original] at he
    linarith only [he]
  linarith only [hfirst, hcert]

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.packet_repair_refit_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms packet_repair_refit_exact

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.repair_fekete_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms repair_fekete_pairing

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.optimizer_prime_repair_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms optimizer_prime_repair_gain

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.summable_prime_repair_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms summable_prime_repair_remainder

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.first_gram_excess_fiftyfold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms first_gram_excess_fiftyfold

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
