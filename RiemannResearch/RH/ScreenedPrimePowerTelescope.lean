import RiemannResearch.RH.ArithmeticPacketCore
import RiemannResearch.RH.MeanOneSix
import RiemannResearch.RH.MixedConductorCovariance
import RiemannResearch.RH.MixedConductorDilation
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.PrimePowerPacketSummation
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Telescoping integrated Ramanujan packets under Pareto screening

Christian Noack's *The categorical CRT of atoms and carries*, §§3–4, supplies the
prime-power telescope and the target-preserving reduction. The divisor formula
for Ramanujan sums is classical (Ramanujan, 1918, equations (2.6)–(2.7)).
The rank-one input is proved in `MixedConductorRankOne` using logarithmic
rigidity, as discussed in I. Kátai, *On additive functions* (1978), (1.1)–(1.2).
Here the finite telescope is transported into the complete Hilbert space.
Its normalized value under full screening is independent of the conductor.
At finite mixed cutoffs the entire projection remainder survives. Common
multiples of the mixed conductors give an explicit lower bound for that trial.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- A tower through a positive exponent synthesizes the single unscaled residue. -/
theorem primePower_packet_telescope (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    (∑ j ∈ Finset.range a, ramanujanPacketHilbert (p ^ (j + 1))) =
      rawResidueAtom (p ^ a - 2) := by
  have hpa := Nat.one_lt_pow ha.ne' hp.one_lt
  apply hilbertSequence_injective
  funext n
  rw [← anchoredEvaluationCLM_apply, map_sum, rawResidueAtom_sequence,
    show p ^ a - 2 + 2 = p ^ a by omega]
  simpa only [anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert] using
    sum_ramanujanPacket_prime_powers p a n hp

/-- The residue of every modulus has the explicit full-screened logarithmic value. -/
theorem fullScreening_rawResidue_eq_log_smul (d : ℕ) (hd : 1 < d) :
    fullScreening (rawResidueAtom (d - 2)) =
      Real.log (d : ℝ) • normalizedScreenedTwo := by
  have hmem : rawResidueAtom (d - 2) ∈ closedSpace :=
    closedSpace.smul_mem _ (Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨d - 2, rfl⟩))
  have hseq : hilbertSequence (rawResidueAtom (d - 2)) = residue d := by
    funext n
    rw [rawResidueAtom_sequence, show d - 2 + 2 = d by omega]
  rw [fullScreening_eq_mean_smul hmem, hilbert_inner_one, hseq, paretoMean_residue d (by omega)]

/-- Any one positive prime power spans the entire fully screened legal subspace. -/
theorem screenedPrimeClosure_eq_span_primePower (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    screenedPrimeClosure = Submodule.span ℝ {limitScreenedPacket (p ^ a)} := by
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [screenedPrimeClosure_eq_span_two, ← fullScreening_packet,
    fullScreening_packet_eq_mangoldt_smul _ (Nat.one_lt_pow ha.ne' hp.one_lt),
    ArithmeticFunction.vonMangoldt_apply_pow ha.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
  apply le_antisymm <;> apply Submodule.span_le.mpr <;> intro z hz
    <;> rw [Set.mem_singleton_iff.mp hz]
  · exact Submodule.mem_span_singleton.mpr ⟨(Real.log p)⁻¹, by
      rw [smul_smul, inv_mul_cancel₀ hlog, one_smul]⟩
  · exact Submodule.mem_span_singleton.mpr ⟨Real.log p, rfl⟩

/-- Target membership is equivalent to approximating the centered residue of any
one prescribed modulus by mixed packets. At modulus two this is centered parity. -/
theorem one_mem_iff_centered_residue_mem_mixedClosure (d : ℕ) (hd : 1 < d) :
    hilbertOne ∈ closedSpace ↔
      rawResidueAtom (d - 2) - Real.log (d : ℝ) • hilbertOne ∈ mixedClosure := by
  have hlog : Real.log (d : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hd)).ne'
  have hz (z : ThresholdHilbert) : z ∈ mixedClosure ↔ fullScreening z = 0 := by
    change z ∈ mixedClosure ↔ z - mixedClosure.starProjection z = 0
    rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo, hz, map_sub, map_smul,
    fullScreening_rawResidue_eq_log_smul d hd, fullScreening_one, ← smul_sub, smul_eq_zero,
    or_iff_right hlog, sub_eq_zero]

/-- The unit-mean trial obtained by dividing the physical residue by its logarithmic mean. -/
def logNormalizedResidue (d : ℕ) : ThresholdHilbert :=
  (Real.log (d : ℝ))⁻¹ • rawResidueAtom (d - 2)

theorem fullScreening_logNormalizedResidue (d : ℕ) (hd : 1 < d) :
    fullScreening (logNormalizedResidue d) = normalizedScreenedTwo := by
  rw [logNormalizedResidue, map_smul, fullScreening_rawResidue_eq_log_smul d hd,
    smul_smul, inv_mul_cancel₀ (Real.log_pos (by exact_mod_cast hd)).ne', one_smul]

/-- On a finite mixed window, the complete centered Gram form consists of a
rank-one form in the two means and the signed Gram form of the projection tails. -/
theorem finiteScreening_centered_gram (B : ℕ) {x y : ThresholdHilbert}
    (hx : x ∈ closedSpace) (hy : y ∈ closedSpace) :
    let μ := fun z : ThresholdHilbert => inner ℝ z hilbertOne
    let T := fun z : ThresholdHilbert => mixedClosure.starProjection z -
      (mixedSpace (Finset.Icc 2 B)).starProjection z
    inner ℝ (finiteScreening B x - μ x • hilbertOne) (finiteScreening B y - μ y • hilbertOne) =
      μ x * μ y * (limitEnergy / (1 - limitEnergy)) + inner ℝ (T x) (T y) := by
  let K := mixedSpace (Finset.Icc 2 B)
  let μ := fun z : ThresholdHilbert => inner ℝ z hilbertOne
  let T := fun z : ThresholdHilbert => mixedClosure.starProjection z - K.starProjection z
  let e := normalizedScreenedTwo - hilbertOne
  have he : e ∈ mixedClosureᗮ := mixedClosure.orthogonal.sub_mem
    (mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal (ramanujanPacketHilbert 2)))
    one_mem_mixedClosure_orthogonal
  have hinner (z : ThresholdHilbert) : inner ℝ (T z) e = 0 :=
    (mixedClosure.mem_orthogonal _).mp he _ (mixedClosure.sub_mem
      (mixedClosure.starProjection_apply_mem z)
      (mixedSpace_window_le_closure B (K.starProjection_apply_mem z)))
  have hinner' (z : ThresholdHilbert) : inner ℝ e (T z) = 0 :=
    (real_inner_comm _ _).trans (hinner z)
  have split {z : ThresholdHilbert} (hz : z ∈ closedSpace) :
      finiteScreening B z - μ z • hilbertOne = μ z • e + T z := by
    have hs := fullScreening_eq_mean_smul hz
    change z - mixedClosure.starProjection z = μ z • normalizedScreenedTwo at hs
    dsimp only [e, T]
    rw [finiteScreening_apply, smul_sub, ← hs]
    dsimp only [K]
    abel
  change inner ℝ (finiteScreening B x - μ x • hilbertOne)
    (finiteScreening B y - μ y • hilbertOne) = _
  rw [split hx, split hy, inner_add_left, inner_add_right, inner_add_right]
  simp only [real_inner_smul_left, real_inner_smul_right, hinner, hinner', mul_zero, zero_add,
    add_zero, real_inner_self_eq_norm_sq]
  rw [show ‖e‖ ^ 2 = limitEnergy / (1 - limitEnergy) from
    normalizedScreenedTwo_error_sq_eq_limitEnergy]
  change μ y * (μ x * (limitEnergy / (1 - limitEnergy))) + inner ℝ (T x) (T y) =
    μ x * μ y * (limitEnergy / (1 - limitEnergy)) + inner ℝ (T x) (T y)
  ring

/-- Exact error at any finite mixed cutoff, also when the input conductor changes. -/
theorem finiteScreening_logNormalizedResidue_error (B d : ℕ) (hd : 1 < d) :
    ‖hilbertOne - finiteScreening B (logNormalizedResidue d)‖ ^ 2 =
      limitEnergy / (1 - limitEnergy) +
        ‖mixedClosure.starProjection (logNormalizedResidue d) -
          (mixedSpace (Finset.Icc 2 B)).starProjection (logNormalizedResidue d)‖ ^ 2 := by
  rw [finiteScreening_apply, finite_screened_error_eq_full_add_projection_tail,
    fullScreening_logNormalizedResidue d hd, norm_sub_rev hilbertOne normalizedScreenedTwo,
    normalizedScreenedTwo_error_sq_eq_limitEnergy]

/-- Every prescribed sequence of legal moduli has the same target criterion when the
finite mixed cutoff may depend on the modulus and exceed a prescribed lower bound. -/
theorem one_mem_iff_exists_logNormalizedResidue_cutoffs (d lower : ℕ → ℕ)
    (hd : ∀ j, 1 < d j) :
    hilbertOne ∈ closedSpace ↔ ∃ B : ℕ → ℕ, (∀ j, lower j ≤ B j) ∧
      Tendsto (fun j => finiteScreening (B j) (logNormalizedResidue (d j))) atTop
        (𝓝 hilbertOne) := by
  rw [← fullScreening_tendsto_iff_exists_cutoffs (fun j => logNormalizedResidue (d j))
    lower hilbertOne fullScreening_one, one_mem_closedSpace_iff_normalizedScreenedTwo]
  simp_rw [fullScreening_logNormalizedResidue _ (hd _)]
  exact ⟨fun he => he ▸ tendsto_const_nhds, tendsto_nhds_unique tendsto_const_nhds⟩

/-- Every mixed correction in a finite window vanishes at each common multiple
of its conductors, including a correction chosen by orthogonal projection. -/
theorem mixedSpace_evaluation_eq_zero_of_common_multiple (F : Finset ℕ) (n : ℕ)
    (hn : ∀ q ∈ mixedConductors F, q ∣ n)
    {c : ThresholdHilbert} (hc : c ∈ mixedSpace F) : anchoredEvaluationCLM n c = 0 := by
  have hle : mixedSpace F ≤ LinearMap.ker (anchoredEvaluationCLM n).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    change anchoredEvaluationCLM n (ramanujanPacketHilbert q.val) = 0
    rw [anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert]
    have h0 : ramanujanPacket q.val 0 = 0 := by
      rw [← hilbertSequence_ramanujanPacketHilbert, hilbertSequence_zero]
    simpa only [Nat.zero_add, h0] using
      ramanujanPacket_period_of_dvd q.val n (hn q.val q.property) 0
  exact hle hc

private theorem normalizedResidue_error_at_site (F : Finset ℕ) (d n : ℕ) (hd : 1 < d)
    (hn : 0 < n) (hnd : n < d) (hdiv : ∀ q ∈ mixedConductors F, q ∣ n)
    {c : ThresholdHilbert} (hc : c ∈ mixedSpace F) :
    hilbertSequence (hilbertOne - (logNormalizedResidue d - c)) n =
      1 - (n : ℝ) / Real.log (d : ℝ) := by
  rw [← anchoredEvaluationCLM_apply, map_sub, map_sub,
    mixedSpace_evaluation_eq_zero_of_common_multiple F n hdiv hc, sub_zero,
    logNormalizedResidue, map_smul, smul_eq_mul, anchoredEvaluationCLM_apply,
    anchoredEvaluationCLM_apply, hilbertOne_sequence, rawResidueAtom_sequence,
    show d - 2 + 2 = d by omega]
  simp [zeroAnchor, hn.ne', residue, Nat.mod_eq_of_lt hnd, div_eq_inv_mul]

/-- The selected physical sites and their complete complement partition the error. -/
theorem logNormalizedResidue_error_partition (F T : Finset ℕ) (d : ℕ) (hd : 1 < d)
    {c : ThresholdHilbert} (hc : c ∈ mixedSpace F)
    (hT : ∀ n ∈ T, 0 < n ∧ n < d ∧ ∀ q ∈ mixedConductors F, q ∣ n) :
    let e := hilbertOne - (logNormalizedResidue d - c)
    ‖e‖ ^ 2 = (∑ n ∈ T, positiveWeight n * (1 - (n : ℝ) / Real.log d) ^ 2) +
      ∑' n : ↥((↑T : Set ℕ)ᶜ), positiveWeight n.val * hilbertSequence e n.val ^ 2 := by
  let e := hilbertOne - (logNormalizedResidue d - c)
  change ‖e‖ ^ 2 = _
  rw [hilbert_norm_weighted_sq, ← (hilbertSequence_square_summable e).sum_add_tsum_compl (s := T)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnd, hdiv⟩ := hT n hn
  rw [show hilbertSequence e n = 1 - (n : ℝ) / Real.log d from
    normalizedResidue_error_at_site F d n hd hn0 hnd hdiv hc]

private theorem scaled_site_cost_lower (n : ℕ) (t : ℝ) (hn : 0 < n)
    (ht : 0 < t) (hnt : 2 * t ≤ n) :
    1 / (8 * t ^ 2) ≤ positiveWeight n * (1 - (n : ℝ) / t) ^ 2 := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : 0 < (n : ℝ) := by positivity
  have hsq : ((n : ℝ) / 2) ^ 2 ≤ ((n : ℝ) - t) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
  have hnum : (n : ℝ) * ((n : ℝ) + 1) ≤ 8 * ((n : ℝ) - t) ^ 2 := by
    nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hn1)]
  have he : positiveWeight n * (1 - (n : ℝ) / t) ^ 2 =
      ((n : ℝ) - t) ^ 2 / (((n : ℝ) * (n + 1)) * t ^ 2) := by
    unfold positiveWeight
    field_simp
    ring
  rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right hnum (sq_nonneg t)]

/-- Each common multiple from twice the logarithmic mean up to the conductor
contributes at least the displayed amount, for every mixed fit in the window. -/
theorem logNormalizedResidue_error_ge_common_multiples (F T : Finset ℕ) (d : ℕ)
    (hd : 1 < d) {c : ThresholdHilbert} (hc : c ∈ mixedSpace F)
    (hT : ∀ n ∈ T, 0 < n ∧ n < d ∧ 2 * Real.log (d : ℝ) ≤ n ∧
      ∀ q ∈ mixedConductors F, q ∣ n) :
    (T.card : ℝ) / (8 * (Real.log (d : ℝ)) ^ 2) ≤
      ‖hilbertOne - (logNormalizedResidue d - c)‖ ^ 2 := by
  have hlog := Real.log_pos (show (1 : ℝ) < d by exact_mod_cast hd)
  rw [logNormalizedResidue_error_partition F T d hd hc
    (fun n hn => ⟨(hT n hn).1, (hT n hn).2.1, (hT n hn).2.2.2⟩)]
  apply le_trans _ (le_add_of_nonneg_right (tsum_nonneg (fun _ =>
    mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))))
  calc
    _ = ∑ _n ∈ T, 1 / (8 * (Real.log (d : ℝ)) ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_div]
    _ ≤ _ := Finset.sum_le_sum (fun n hn =>
      scaled_site_cost_lower n _ (hT n hn).1 hlog (hT n hn).2.2.1)

/-- The complete Pareto Gram entries for the first mixed conductor. -/
theorem packet_two_six_inner_and_norm :
    inner ℝ (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 6) =
      Real.log 2 - Real.pi / (2 * Real.sqrt 3) ∧
    ‖ramanujanPacketHilbert 6‖ ^ 2 = Real.pi / Real.sqrt 3 := by
  have hm : ramanujanPacketHilbert 6 ∈ mixedSpace (Finset.Icc 2 6) :=
    mixed_packet_mul_of_coprime_mem_window (a := 2) (b := 3)
      (by decide) (by decide) (by decide) (by decide)
  have hzero := ((mixedSpace (Finset.Icc 2 6)).mem_orthogonal hilbertOne).mp
    (one_mem_mixed_orthogonal _) _ hm
  rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket]
    at hzero
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  constructor
  · rw [hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert,
      hilbertSequence_ramanujanPacketHilbert,
      packet_inner_eq_differenceCotangentCore 6 2 6 (by decide) (by decide) (by decide)
        (by decide) (by decide), MeanOneSix.packet_core_table 2 6 (by decide) (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, hzero,
      show Nat.totient 6 = 2 by decide]
    norm_num [MeanOneSix.coreTable]
    field_simp [hs]
    ring
  · rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted,
      hilbertSequence_ramanujanPacketHilbert,
      packet_inner_eq_differenceCotangentCore 6 6 6 (by decide) (by decide) (by decide)
        (by decide) (by decide), MeanOneSix.packet_core_table 6 6 (by decide) (by decide), hzero]
    simp [MeanOneSix.coreTable, div_eq_mul_inv]

/-- The exact first mixed fit for the unit-mean conductor-two trial.
The last square gives the excess error of every other coefficient. -/
theorem conductor_six_mixed_fit_error (t : ℝ) :
    let l := Real.log 2
    let b := l - Real.pi / (2 * Real.sqrt 3)
    let h := Real.pi / Real.sqrt 3
    ‖hilbertOne - l⁻¹ • (ramanujanPacketHilbert 2 - t • ramanujanPacketHilbert 6)‖ ^ 2 =
      (l - l ^ 2 - b ^ 2 / h + h * (t - b / h) ^ 2) / l ^ 2 := by
  let l := Real.log 2
  let b := l - Real.pi / (2 * Real.sqrt 3)
  let h := Real.pi / Real.sqrt 3
  let y := ramanujanPacketHilbert 2 - t • ramanujanPacketHilbert 6
  have hl : l ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hh : h ≠ 0 := div_ne_zero Real.pi_ne_zero
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hsource : inner ℝ (ramanujanPacketHilbert 6) hilbertOne = 0 :=
    ((mixedSpace (Finset.Icc 2 6)).mem_orthogonal hilbertOne).mp (one_mem_mixed_orthogonal _)
      _ (mixed_packet_mul_of_coprime_mem_window (a := 2) (b := 3)
          (by decide) (by decide) (by decide) (by decide))
  have hmean : inner ℝ hilbertOne y = l := by
    rw [real_inner_comm]
    change inner ℝ (ramanujanPacketHilbert 2 - t • ramanujanPacketHilbert 6) hilbertOne = _
    rw [inner_sub_left, real_inner_smul_left, hsource, mul_zero, sub_zero, hilbert_inner_one,
      hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    rfl
  have he : ‖y‖ ^ 2 = l - 2 * t * b + t ^ 2 * h := by
    dsimp only [y]
    rw [norm_sub_sq_real, real_inner_smul_right, packet_two_six_inner_and_norm.1,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, packet_two_six_inner_and_norm.2,
      ramanujanPacketHilbert_two_norm_sq]
    dsimp only [l, b, h]
    ring
  change ‖hilbertOne - l⁻¹ • y‖ ^ 2 = _
  rw [norm_sub_sq_real, hilbertOne_norm_sq, real_inner_smul_right, hmean, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, he]
  change 1 - 2 * (l⁻¹ * l) + (l⁻¹) ^ 2 * (l - 2 * t * b + t ^ 2 * h) =
    (l - l ^ 2 - b ^ 2 / h + h * (t - b / h) ^ 2) / l ^ 2
  field_simp [hl, hh]
  ring

private theorem mixedSpace_six_eq_span :
    mixedSpace (Finset.Icc 2 6) = Submodule.span ℝ {ramanujanPacketHilbert 6} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    obtain ⟨hwin, hmix⟩ := Finset.mem_filter.mp q.property
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hwin
    have hq : q.val = 6 := by
      by_contra hn
      have hcases : q.val = 2 ∨ q.val = 3 ∨ q.val = 4 ∨ q.val = 5 := by omega
      rcases hcases with he | he | he | he <;> rw [he] at hmix
      · exact hmix Nat.prime_two.isPrimePow
      · exact hmix Nat.prime_three.isPrimePow
      · exact hmix ((isPrimePow_nat_iff 4).mpr ⟨2, 2, Nat.prime_two, by decide, by decide⟩)
      · exact hmix (show Nat.Prime 5 by decide).isPrimePow
    change ramanujanPacketHilbert q.val ∈ _
    rw [hq]
    exact Submodule.subset_span (Set.mem_singleton _)
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact mixed_packet_mul_of_coprime_mem_window (a := 2) (b := 3)
      (by decide) (by decide) (by decide) (by decide)

/-- The exact first nonzero mixed capture in the fixed-conductor criterion. -/
theorem fixedTwo_mixed_capture_at_six :
    ‖(mixedSpace (Finset.Icc 2 6)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 =
      (Real.log 2 - Real.pi / (2 * Real.sqrt 3)) ^ 2 / (Real.pi / Real.sqrt 3) := by
  let K := mixedSpace (Finset.Icc 2 6)
  let b := Real.log 2 - Real.pi / (2 * Real.sqrt 3)
  let h := Real.pi / Real.sqrt 3
  have hh : h ≠ 0 := div_ne_zero Real.pi_ne_zero
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have h6 : ramanujanPacketHilbert 6 ∈ K :=
    mixed_packet_mul_of_coprime_mem_window (a := 2) (b := 3)
      (by decide) (by decide) (by decide) (by decide)
  have hmem : K.starProjection (ramanujanPacketHilbert 2) ∈
      Submodule.span ℝ {ramanujanPacketHilbert 6} := by
    rw [← mixedSpace_six_eq_span]
    exact K.starProjection_apply_mem _
  obtain ⟨t, he⟩ := Submodule.mem_span_singleton.mp hmem
  have ho := (K.mem_orthogonal _).mp
    (K.sub_starProjection_mem_orthogonal (ramanujanPacketHilbert 2)) _ h6
  have hcross : inner ℝ (ramanujanPacketHilbert 6) (ramanujanPacketHilbert 2) = b :=
    (real_inner_comm _ _).trans packet_two_six_inner_and_norm.1
  rw [inner_sub_right, ← he, real_inner_smul_right, hcross, real_inner_self_eq_norm_sq,
    packet_two_six_inner_and_norm.2, sub_eq_zero] at ho
  have hcoeff : t = b / h := (eq_div_iff hh).mpr ho.symm
  change ‖K.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 = b ^ 2 / h
  rw [← he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, packet_two_six_inner_and_norm.2,
    hcoeff]
  change (b / h) ^ 2 * h = b ^ 2 / h
  field_simp [hh]

end RiemannResearch.RH.Pareto.PrimePowerSchur
