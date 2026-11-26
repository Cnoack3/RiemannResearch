import RiemannResearch.CategoryTheory.QPrimeParsevalTower
import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ScreenedSectionDescent
import RiemannResearch.RH.MixedConductorBilinear
import RiemannResearch.RH.QPhysicalQuotientMetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Odd conditional means of the Pareto screened section

The two physical laws give the odd event different masses. Transporting the
conditional mean requires the density on the odd sites. The native mixed
Parseval residual measures the same unit obstruction through the quotient.
Source: the user's Q prime Parseval tower handoff and odd conditional mean question.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.RH RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability RiemannResearch.RH.ZetaTwoParitySignal
open RiemannResearch.RH.ZetaTwoParetoTransfer RiemannResearch.RH.QParetoEquivalence
open RiemannResearch.RH.QPhysicalQuotientMetric
open RiemannResearch.RH.Pareto RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
open RiemannResearch.CategoryTheory.PhysicalParityObject
open RiemannResearch.CategoryTheory.QPrimeParsevalTower
open MeasureChange (qMixed qParity centeredParity)

namespace RiemannResearch.CategoryTheory.OddConditionalUnit

/-- The user's P-to-Q integration weight dP/dQ on physical Q sequences. -/
abbrev B : QHilbert →L[ℝ] QHilbert := QDensityMetricInverse.inverse

theorem B_physical (f : QHilbert) (n : ℕ) :
    qSequence (B f) n = (zetaTwo * (n : ℝ) / ((n : ℝ) + 1)) * qSequence f n :=
  QDensityMetricInverse.qSequence_inverse f n

/-- Pairing for the reweighted physical law, with the density in one argument. -/
def densityInner (x y : QHilbert) : ℝ := inner ℝ x (B y)

theorem densityInner_eq_pareto (x y : QHilbert) :
    densityInner x y = inner ℝ (paretoEquiv x) (paretoEquiv y) :=
  (QDensityMetricInverse.pareto_inner_inverse x y).symm

/-- Conditional expectation on the odd positive integers under the Pareto law. -/
def paretoOddMean (f : ThresholdHilbert) : ℝ :=
  inner ℝ f (ramanujanPacketHilbert 2) / Real.log 2

/-- Conditional expectation on the same event under the inverse-square law. -/
def nativeOddMean (f : QHilbert) : ℝ := inner ℝ f qOdd / (3/4 : ℝ)

private theorem log_ne_zero : Real.log 2 ≠ 0 :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

theorem pareto_odd_mass : inner ℝ (ramanujanPacketHilbert 2) hilbertOne = Real.log 2 := by
  rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
    ramanujanPacket_prime_eq_residue 2 (by decide), paretoMean_residue 2 (by decide)]
  norm_num

theorem nativeOddMean_one : nativeOddMean qOne = 1 := by
  rw [nativeOddMean, ← qEven_add_qOdd, inner_add_left, qEven_inner_qOdd,
    real_inner_self_eq_norm_sq, qOdd_norm_sq]
  norm_num

theorem paretoOddMean_screened : paretoOddMean normalizedScreenedTwo =
    ‖normalizedScreenedTwo‖ ^ 2 := by
  have hu : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    (Submodule.starProjection_apply_eq_zero_iff _).mp mixed_starProjection_screenedTwo
  have h := Bilinear.pairing_factorization_of_rigidity hu
    (packet_mem_closedSpace 2 (by decide))
  rw [real_inner_self_eq_norm_sq, pareto_odd_mass] at h
  rw [paretoOddMean, h, mul_div_cancel_right₀ _ log_ne_zero]

/-- The excess over one is the whole squared physical defect. -/
theorem paretoOddMean_excess : paretoOddMean normalizedScreenedTwo - 1 =
    ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  rw [paretoOddMean_screened, norm_sub_sq_real, hilbertOne_norm_sq, normalizedScreenedTwo_mean]
  ring

theorem rh_iff_paretoOddMean_unit :
    RiemannHypothesis ↔ paretoOddMean normalizedScreenedTwo = 1 := by
  rw [paretoOddMean_screened, ← real_inner_self_eq_norm_sq]
  exact ScreenedSectionDescent.inner_self_eq_one_iff_rh.symm

theorem paretoEquiv_qOdd : paretoEquiv qOdd = ramanujanPacketHilbert 2 := by
  apply paretoEquiv.symm.injective
  rw [paretoEquiv.symm_apply_apply]
  apply qSequence_injective
  rw [qSequence_qOdd_mod, paretoEquiv_symm_apply, toQ_sequence,
    hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_prime_eq_residue 2 (by decide)]
  rfl

/-- Exact change of the odd marginal for every physical vector. -/
theorem weighted_odd_moment (x : QHilbert) :
    (3/4 : ℝ) * nativeOddMean (B x) =
      Real.log 2 * paretoOddMean (paretoEquiv x) := by
  have h := QDensityMetricInverse.pareto_inner_inverse qOdd x
  change inner ℝ (paretoEquiv qOdd) (paretoEquiv x) =
    inner ℝ qOdd (B x) at h
  rw [paretoEquiv_qOdd, ← real_inner_comm (ramanujanPacketHilbert 2) (paretoEquiv x),
    ← real_inner_comm qOdd (B x)] at h
  unfold nativeOddMean paretoOddMean
  field_simp [log_ne_zero]
  linarith only [h]

/-- Conditional Q mean of the density on odd sites. -/
theorem odd_density_mass :
    nativeOddMean (B qOne) = 4 * Real.log 2 / 3 := by
  have h := weighted_odd_moment qOne
  have hone : paretoEquiv qOne = hilbertOne := toPareto_qOne
  rw [hone, paretoOddMean, ← real_inner_comm hilbertOne (ramanujanPacketHilbert 2), pareto_odd_mass,
    div_self log_ne_zero, mul_one] at h
  linarith

theorem rh_iff_weighted_odd_mean :
    RiemannHypothesis ↔ nativeOddMean (B transportedCarry) =
      nativeOddMean (B qOne) := by
  have h := weighted_odd_moment transportedCarry
  rw [show paretoEquiv transportedCarry = normalizedScreenedTwo from
    paretoEquiv.apply_symm_apply _] at h
  rw [rh_iff_paretoOddMean_unit, odd_density_mass]
  constructor
  · intro hu
    rw [hu, mul_one] at h
    linarith
  · intro hu
    rw [hu] at h
    apply mul_left_cancel₀ log_ne_zero
    linarith only [h]

/-- The plain native mean has an additional signed reciprocal moment. -/
theorem nativeOddMean_excess :
    nativeOddMean transportedCarry - 1 =
      (4 * Real.log 2 / (3 * zetaTwo)) * ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 +
        nativeOddMean (QShiftedReciprocal.B (transportedCarry - qOne)) := by
  have h := weighted_odd_moment (transportedCarry - qOne)
  have hone : paretoEquiv qOne = hilbertOne := toPareto_qOne
  have hP : paretoOddMean (paretoEquiv (transportedCarry - qOne)) =
      ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
    rw [map_sub, transportedCarry, paretoEquiv.apply_symm_apply, hone, ← paretoOddMean_excess]
    unfold paretoOddMean
    rw [inner_sub_left, ← real_inner_comm hilbertOne (ramanujanPacketHilbert 2), pareto_odd_mass,
      sub_div, div_self log_ne_zero]
  rw [hP] at h
  have hn := nativeOddMean_one
  unfold nativeOddMean at h hn ⊢
  change (3/4 : ℝ) * (inner ℝ (zetaTwo • ((transportedCarry - qOne) -
    QShiftedReciprocal.B (transportedCarry - qOne))) qOdd / (3/4 : ℝ)) = _ at h
  rw [real_inner_smul_left, inner_sub_left, inner_sub_left] at h
  field_simp [zetaTwo_pos.ne']
  nlinarith only [h, hn, congrArg (fun t : ℝ => zetaTwo * t) hn]

/-- The native Parseval energy lost at the mixed quotient controls the Pareto
odd-mean excess on both sides with the physical density constants. -/
theorem odd_excess_prime_remainder :
    let remaining := ‖qParity‖ ^ 2 - ∑' k, ‖(layer native k).starProjection qParity‖ ^ 2
    zetaTwo / 2 * remaining ≤ paretoOddMean normalizedScreenedTwo - 1 ∧
      paretoOddMean normalizedScreenedTwo - 1 ≤ zetaTwo * remaining := by
  have hq := physical_quotient_norm_sq_comparison mixedClosure qParity
  have hp : ‖mixedClosure.mkQ centeredParity‖ = ‖CenteredMeanSnake.boundary‖ :=
    norm_supportCocone_parity 0
  have hb := CenteredMeanSnake.boundary_norm_sq
  have hsum := (layer_energy_hasSum native qParity).tsum_eq
  rw [terminal_native] at hsum
  change zetaTwo / 2 * ‖qMixed.mkQ qParity‖ ^ 2 ≤ ‖mixedClosure.mkQ (paretoEquiv qParity)‖ ^ 2 ∧
    ‖mixedClosure.mkQ (paretoEquiv qParity)‖ ^ 2 ≤ zetaTwo * ‖qMixed.mkQ qParity‖ ^ 2 at hq
  rw [paretoEquiv.apply_symm_apply, hp, hb, ← paretoOddMean_screened] at hq
  dsimp only
  rw [hsum, sub_sub_cancel]
  exact hq

/-- Ordinary Q conditioning after weighting the numerator and the event mass by B. -/
def densityOddMean (x : QHilbert) : ℝ := nativeOddMean (B x) / nativeOddMean (B qOne)

theorem densityOddMean_eq_pareto (x : QHilbert) :
    densityOddMean x = paretoOddMean (paretoEquiv x) := by
  rw [densityOddMean, odd_density_mass]
  apply (div_eq_iff (div_ne_zero (mul_ne_zero (by norm_num) log_ne_zero) (by norm_num))).2
  linarith only [weighted_odd_moment x]

theorem densityOddMean_screened :
    densityOddMean transportedCarry = densityInner transportedCarry transportedCarry := by
  rw [densityOddMean_eq_pareto, densityInner_eq_pareto, transportedCarry,
    paretoEquiv.apply_symm_apply, paretoOddMean_screened, real_inner_self_eq_norm_sq]

/-- All terms live in Q. The excess of the normalized odd moment is the exact B-weighted
squared norm of the physical difference from one. -/
theorem densityOddMean_excess :
    densityOddMean transportedCarry - 1 =
      densityInner (transportedCarry - qOne) (transportedCarry - qOne) := by
  have hu : paretoEquiv transportedCarry = normalizedScreenedTwo := paretoEquiv.apply_symm_apply _
  have h1 : paretoEquiv qOne = hilbertOne := toPareto_qOne
  rw [densityOddMean_eq_pareto, densityInner_eq_pareto, map_sub, hu, h1, paretoOddMean_excess,
    real_inner_self_eq_norm_sq]

theorem rh_iff_densityOddMean_unit :
    RiemannHypothesis ↔ densityOddMean transportedCarry = 1 := by
  rw [densityOddMean_eq_pareto, transportedCarry, paretoEquiv.apply_symm_apply]
  exact rh_iff_paretoOddMean_unit

theorem rh_iff_B_odd_moment :
    RiemannHypothesis ↔ nativeOddMean (B transportedCarry) = 4 * Real.log 2 / 3 := by
  simpa only [odd_density_mass] using rh_iff_weighted_odd_mean

/-- The physical screened section has unit unconditional Q mean after weighting by B. -/
theorem B_screened_mean : inner ℝ (B transportedCarry) qOne = 1 := by
  rw [← real_inner_comm (B transportedCarry) qOne]
  change densityInner qOne transportedCarry = 1
  rw [densityInner_eq_pareto, show paretoEquiv qOne = hilbertOne from toPareto_qOne,
    transportedCarry, paretoEquiv.apply_symm_apply,
    ← real_inner_comm hilbertOne normalizedScreenedTwo, normalizedScreenedTwo_mean]

private theorem parity_norm_sq : ‖ramanujanPacketHilbert 2‖ ^ 2 = Real.log 2 := by
  rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted, ← pareto_odd_mass,
    hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
    ramanujanPacket_prime_eq_residue 2 (by decide)]
  unfold paretoInner paretoMean
  apply tsum_congr
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Pareto.residue, h]

theorem density_target_energy : densityInner qParity qParity = (Real.log 2)⁻¹ - 1 := by
  rw [densityInner_eq_pareto, paretoEquiv.apply_symm_apply, real_inner_self_eq_norm_sq,
    centeredParity, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, parity_norm_sq,
    hilbertOne_norm_sq, real_inner_smul_left, pareto_odd_mass]
  field_simp [log_ne_zero]
  ring

/-- Exact loss for any physical mixed trial in the full-density pairing. -/
theorem density_trial_error {m : QHilbert} (hm : m ∈ qMixed) :
    let fit := qParity - (transportedCarry - qOne)
    densityInner (qParity-m) (qParity-m) =
      (densityOddMean transportedCarry - 1) + densityInner (fit-m) (fit-m) := by
  dsimp only
  have hu := CenteredMeanSnake.normalizedScreenedTwo_eq_projected_packet
  rw [Submodule.starProjection_orthogonal_val, smul_sub] at hu
  have hu' : paretoEquiv transportedCarry = normalizedScreenedTwo :=
    paretoEquiv.apply_symm_apply _
  have h1 : paretoEquiv qOne = hilbertOne := toPareto_qOne
  have hfit : paretoEquiv (qParity - (transportedCarry-qOne)) ∈ mixedClosure := by
    rw [map_sub, map_sub, hu', h1, paretoEquiv.apply_symm_apply, centeredParity, hu]
    have he : (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne -
        ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2 -
          (Real.log 2)⁻¹ • mixedClosure.starProjection (ramanujanPacketHilbert 2) - hilbertOne) =
        (Real.log 2)⁻¹ • mixedClosure.starProjection (ramanujanPacketHilbert 2) := by abel
    rw [he]
    exact mixedClosure.smul_mem _ (mixedClosure.starProjection_apply_mem _)
  have hm' : paretoEquiv m ∈ mixedClosure := hm
  have hr := mixedClosure.sub_mem hfit hm'
  have ho := CenteredMeanSnake.screenedTwo_sub_one_mem_orthogonals.2 _ hr
  have he : paretoEquiv (qParity-m) = paretoEquiv (qParity - (transportedCarry-qOne)-m) +
      (normalizedScreenedTwo-hilbertOne) := by
    rw [map_sub, map_sub, map_sub, map_sub, hu', h1]
    abel
  rw [densityInner_eq_pareto, real_inner_self_eq_norm_sq, he, norm_add_sq_real,
    map_sub (f := paretoEquiv) (qParity-(transportedCarry-qOne)) m, ho,
    densityOddMean_eq_pareto, hu', paretoOddMean_excess, densityInner_eq_pareto,
    real_inner_self_eq_norm_sq, map_sub (f := paretoEquiv) (qParity-(transportedCarry-qOne)) m]
  ring

/-- Evaluating the native prime-stage residuals with B is itself an RH test. -/
theorem rh_iff_density_prime_residual :
    RiemannHypothesis ↔ Filter.Tendsto
      (fun b => let e := qParity - (stage native b).starProjection qParity
                densityInner e e) Filter.atTop (nhds 0) := by
  let S := terminal native
  let r := qParity - S.starProjection qParity
  have hm : qParity ∈ S ↔ RiemannHypothesis := by
    change qParity ∈ terminal native ↔ RiemannHypothesis
    rw [terminal_native]
    exact (Submodule.Quotient.mk_eq_zero qMixed).symm.trans
      MeasureChange.q_terminal_parity_zero_iff_rh
  have hz : densityInner r r = 0 ↔ RiemannHypothesis := by
    rw [densityInner_eq_pareto, inner_self_eq_zero]
    constructor
    · intro h
      have hr : r = 0 := paretoEquiv.injective (h.trans paretoEquiv.map_zero.symm)
      exact hm.mp (S.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm)
    · intro h
      change paretoEquiv (qParity - S.starProjection qParity) = 0
      rw [S.starProjection_eq_self_iff.mpr (hm.mpr h), sub_self, map_zero]
  have hE : Filter.Tendsto (fun b => qParity - (stage native b).starProjection qParity)
      Filter.atTop (nhds r) :=
    (tendsto_const_nhds (x := qParity)).sub (projection_tendsto native qParity)
  have hc : Continuous (fun y : QHilbert => densityInner y y) := continuous_id.inner B.continuous
  have hlim : Filter.Tendsto
      (fun b => densityInner (qParity - (stage native b).starProjection qParity)
        (qParity - (stage native b).starProjection qParity)) Filter.atTop
      (nhds (densityInner r r)) := by
    simpa only [Function.comp_def] using hc.continuousAt.tendsto.comp hE
  constructor
  · intro h
    simpa only [hz.mpr h] using hlim
  · intro h
    exact hz.mp (tendsto_nhds_unique hlim h)

/--
info: 'RiemannResearch.CategoryTheory.OddConditionalUnit.rh_iff_densityOddMean_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_densityOddMean_unit

/--
info: 'RiemannResearch.CategoryTheory.OddConditionalUnit.rh_iff_B_odd_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_B_odd_moment

/--
info: 'RiemannResearch.CategoryTheory.OddConditionalUnit.rh_iff_density_prime_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_density_prime_residual

end RiemannResearch.CategoryTheory.OddConditionalUnit
