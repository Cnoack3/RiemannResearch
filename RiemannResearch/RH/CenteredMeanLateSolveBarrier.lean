import RiemannResearch.RH.CenteredMeanDriftCutoffs
import RiemannResearch.RH.CanonicalMobiusStretchedCorrection
import RiemannResearch.RH.CanonicalMobiusMovingCutoff

/-!
# Finite-stage lower obstruction for a physical Gram drift

Once the later dictionary contains the canonical Möbius exact head, its
projection residual obeys a finite-stage tail product inequality. The signed
decomposition of that residual into the constant, the base error and the
two-solve change makes the later cutoff explicit. Along any cofinal physical
schedule, a single sufficiently late solve at each index detects a nonzero
centered boundary.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer RiemannResearch.Analysis

/-- The exact signed tail splits into a marked constant, the base error
and the normalized change of actual solve. -/
theorem lateSolve_residualTail_identity (B A N : ℕ) :
    let m := packetMass (A + 1)
    hilbertTailShift (hilbertOne - projection (A + 1)) N =
      (1 - m) • hilbertTailShift hilbertOne N -
        m • hilbertTailShift (packetUnitMean B - hilbertOne) N +
        m • hilbertTailShift (packetUnitMean B - packetUnitMean A) N := by
  dsimp only
  have hm : packetMass (A + 1) • packetUnitMean A = projection (A + 1) := by
    rw [packetUnitMean, smul_smul, mul_inv_cancel₀ (packetMass_pos _ (Nat.succ_pos _)).ne',
      one_smul, packetCandidate_eq_projection]
  rw [← hm]
  ext j
  let m := packetMass (A + 1)
  change hilbertOne (j + N) - m * packetUnitMean A (j + N) =
    (1 - m) * hilbertOne (j + N) - m * (packetUnitMean B (j + N) - hilbertOne (j + N)) +
      m * (packetUnitMean B (j + N) - packetUnitMean A (j + N))
  ring

private theorem lateSolve_tail_le_weighted_costs (B A N : ℕ) (hBA : B ≤ A) :
    let m := packetMass (A + 1)
    ‖hilbertTailShift (hilbertOne - projection (A + 1)) N‖ ^ 2 ≤
      3 * ((1 - m) ^ 2 * (1 / ((N : ℝ) + 1)) +
        m ^ 2 * (finiteSectionTailCost B N + finiteSectionTailDrift B A N)) := by
  let m := packetMass (A + 1)
  let x := hilbertTailShift hilbertOne N
  let y := hilbertTailShift (packetUnitMean B - hilbertOne) N
  let z := hilbertTailShift (packetUnitMean B - packetUnitMean A) N
  have hm : 0 ≤ m := (packetMass_bounds _).1
  have he : 0 ≤ 1 - m := sub_nonneg.mpr (packetMass_bounds _).2.le
  have ht : ‖(1 - m) • x - m • y + m • z‖ ≤ (1 - m) * ‖x‖ + m * ‖y‖ + m * ‖z‖ := by
    calc
      _ ≤ ‖(1 - m) • x - m • y‖ + ‖m • z‖ := norm_add_le _ _
      _ ≤ ‖(1 - m) • x‖ + ‖m • y‖ + ‖m • z‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg he, abs_of_nonneg hm]
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ (1 - m) * ‖x‖ + m * ‖y‖ + m * ‖z‖)).mpr ht
  dsimp only
  rw [lateSolve_residualTail_identity B A N, ← tailShift_one_norm_sq,
    finiteSectionTailCost_eq, finiteSectionTailDrift_eq B A N hBA]
  change ‖(1 - m) • x - m • y + m • z‖ ^ 2 ≤
    3 * ((1 - m) ^ 2 * ‖x‖ ^ 2 + m ^ 2 * (‖y‖ ^ 2 + ‖z‖ ^ 2))
  nlinarith only [hs, sq_nonneg ((1 - m) * ‖x‖ - m * ‖y‖),
    sq_nonneg ((1 - m) * ‖x‖ - m * ‖z‖), sq_nonneg (m * ‖y‖ - m * ‖z‖)]

/-- A uniform upper envelope for the finite projection tail in terms of the base and drift. -/
theorem lateSolve_tail_le_three_costs (B A N : ℕ) (hBA : B ≤ A) :
    ‖hilbertTailShift (hilbertOne - projection (A + 1)) N‖ ^ 2 ≤
      3 * (1 / ((N : ℝ) + 1) + finiteSectionTailCost B N + finiteSectionTailDrift B A N) := by
  let m := packetMass (A + 1)
  have hm := packetMass_bounds (A + 1)
  have hM : m ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hm.2.le hm.1
    dsimp only [m]
    nlinarith only [h, hm.2]
  have hE : (1 - m) ^ 2 ≤ 1 := by
    dsimp only [m]
    nlinarith only [mul_nonneg hm.1 (sub_nonneg.mpr hm.2.le), hm.1]
  have ht : 0 ≤ finiteSectionTailCost B N := by rw [finiteSectionTailCost_eq]; positivity
  have hd : 0 ≤ finiteSectionTailDrift B A N := by
    rw [finiteSectionTailDrift_eq B A N hBA]
    positivity
  apply (lateSolve_tail_le_weighted_costs B A N hBA).trans
  change 3 * ((1 - m) ^ 2 * _ + m ^ 2 * _) ≤ _
  linarith only [mul_le_mul_of_nonneg_right hE (by positivity : 0 ≤ 1 / ((N : ℝ) + 1)),
    mul_le_mul_of_nonneg_right hM (add_nonneg ht hd)]

/-- Every sufficiently large dictionary obeys a finite quantitative obstruction.
The exact canonical Möbius head at `N` supplies the complete multiplier. -/
theorem lateSolve_gain_product_lower (B A N : ℕ) (hBA : B ≤ A) (hNA : N ≤ A + 1) :
    let m := packetMass (A + 1)
    (1 - m) ^ 2 ≤ 3 * ((1 - m) ^ 2 * (1 / ((N : ℝ) + 1)) +
      m ^ 2 * (finiteSectionTailCost B N + finiteSectionTailDrift B A N)) *
        ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 := by
  have hl := projection_error_sq_le_canonicalResidual_tail N (A + 1) hNA
  change (energy (A + 1)) ^ 2 ≤ _ at hl
  rw [packet_energy_eq_original] at hl
  exact hl.trans (mul_le_mul_of_nonneg_right (lateSolve_tail_le_weighted_costs B A N hBA)
    (sq_nonneg _))

/-- The scaled physical tail of the constant is at most one. -/
theorem scaled_constant_tail_le_one (b : ℝ) (hb : 0 < b) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * sectionTailDamping b N * (1 / ((N : ℝ) + 1)) ≤ 1 := by
  have hs : sectionTailDamping b N ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hlog := Real.log_nonneg (by exact_mod_cast hN : 1 ≤ (N : ℝ))
    have hsix : 6 ≤ 6 + Real.log (N : ℝ) := by linarith
    have hφ : 0 ≤ logProductPower (1 / 11) (6 + Real.log (N : ℝ)) :=
      Real.rpow_nonneg (mul_nonneg (by linarith)
        ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_log_of_six_le hsix))) _
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) hφ
  rw [← mul_div_assoc, mul_one]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) N)]

/-- The exponent used by both the late-solve criterion and its Burnol obstruction
is half the exponent supplied by the canonical Möbius PNT estimate. -/
def lateSolveExponent : {b : ℝ // 0 < b} :=
  ⟨projection_error_eventual_stretched_tail_bound.choose / 2,
    half_pos projection_error_eventual_stretched_tail_bound.choose_spec.1⟩

private theorem eventually_one_le_stretched_scale (a : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ) * sectionTailDamping a N := by
  have hL := MovingCovariance.logScale_tendsto
  have hφ := (tendsto_logProductPower_div_self (1 / 11) (by norm_num) (by norm_num)).comp hL
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually (eventually_ge_atTop (6 : ℝ)),
    hφ.eventually_lt_const (by positivity : (0 : ℝ) < 1 / (2 * a))] with N hn hlogN hp
  let L := MovingCovariance.logScale N
  change 6 ≤ Real.log (N : ℝ) at hlogN
  have hLp : 0 < L := by change 0 < 6 + Real.log (N : ℝ); linarith only [hlogN]
  change logProductPower (1 / 11) L / L < 1 / (2 * a) at hp
  have h₁ := (div_lt_div_iff₀ hLp (by positivity : 0 < 2 * a)).mp hp
  have h₂ : a * logProductPower (1 / 11) L ≤ Real.log (N : ℝ) := by
    change _ < 1 * (6 + Real.log (N : ℝ)) at h₁
    linarith only [h₁, hlogN]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have he := Real.exp_le_exp.mpr (neg_le_neg h₂)
  have hinv : (N : ℝ)⁻¹ ≤ sectionTailDamping a N := by
    simpa only [Real.exp_neg, Real.exp_log hNr, neg_mul, sectionTailDamping, L,
      MovingCovariance.logScale] using he
  simpa only [mul_inv_cancel₀ hNr.ne'] using mul_le_mul_of_nonneg_left hinv hNr.le

/-- The actual finite mass loss imposes a uniform quantitative lower bound on
the scaled base and drift cost through the unconditional canonical Möbius PNT estimate. -/
theorem lateSolve_mass_loss_upper :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ B A : ℕ, B ≤ A → n ≤ A + 1 →
      (1 - packetMass (A + 1)) ^ 2 ≤ D * (1 + (n : ℝ) * sectionTailDamping lateSolveExponent.val n *
        (finiteSectionTailCost B n + finiteSectionTailDrift B A n)) *
          sectionTailDamping lateSolveExponent.val n := by
  let a := projection_error_eventual_stretched_tail_bound.choose
  have ha : 0 < a := projection_error_eventual_stretched_tail_bound.choose_spec.1
  obtain ⟨C, hC, hprov⟩ := projection_error_eventual_stretched_tail_bound.choose_spec.2
  let b := a / 2
  have hb : 0 < b := by dsimp [b]; linarith
  refine ⟨3 * (8 + C), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hprov,
    eventually_one_le_stretched_scale a ha] with n hn1 hP hWa
  intro B A hBA hNA
  let m := A + 1
  let e := energy m
  let r := ‖hilbertTailShift (hilbertOne - projection m) n‖ ^ 2
  let d := sectionTailDamping b n
  let w := (n : ℝ) * d
  let S := w * (finiteSectionTailCost B n + finiteSectionTailDrift B A n)
  have hwd : (n : ℝ) * sectionTailDamping a n = w * d := by
    have hd : sectionTailDamping a n = d * d := by
      simp only [d, sectionTailDamping, ← Real.exp_add]
      congr 1
      dsimp only [b]
      ring
    rw [hd]
    dsimp only [w]
    ring
  have hD : 0 ≤ d := (Real.exp_pos _).le
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hD
  have htail := mul_le_mul_of_nonneg_left (lateSolve_tail_le_three_costs (B) (A) n hBA) hw
  have hconst := scaled_constant_tail_le_one b hb n hn1
  have hr : w * r ≤ 3 * (1 + S) := by
    change w * r ≤ _ at htail
    change w * (1 / ((n : ℝ) + 1)) ≤ 1 at hconst
    change w * r ≤ 3 * (1 + w * _)
    linarith only [htail, hconst]
  have hstage := hP m hNA
  change e ^ 2 ≤ r * (8 + C * (n : ℝ) * sectionTailDamping a n) at hstage
  rw [mul_assoc C (n : ℝ)] at hstage
  have hfac : 8 + C * ((n : ℝ) * sectionTailDamping a n) ≤
      (8 + C) * ((n : ℝ) * sectionTailDamping a n) := by
    linarith only [hWa]
  have het := hstage.trans (mul_le_mul_of_nonneg_left hfac (sq_nonneg _))
  rw [hwd] at het
  have heUpper : e ^ 2 ≤ (1 + S) * (3 * (8 + C)) * d := by
    have hz := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 8 + C)) hD
    linarith only [het, hz]
  change energy (A + 1) ^ 2 ≤ _ at heUpper
  rw [packet_energy_eq_original] at heUpper
  apply heUpper.trans_eq
  dsimp only [S, w, d, b, a, lateSolveExponent]
  ring

/-- A nonzero centered boundary forces the scaled sum of the base error and
actual later-solve drift to diverge along every cofinal physical sequence whose
later dictionary contains the exact Möbius head. The threshold is explicit. -/
theorem lateSolve_cost_barrier :
    ∀ B A N : ℕ → ℕ, Tendsto N atTop atTop →
      (∀ᶠ j : ℕ in atTop, B j ≤ A j ∧ N j ≤ A j + 1) →
      boundary ≠ 0 → Tendsto (fun j : ℕ => (N j : ℝ) * sectionTailDamping lateSolveExponent.val (N j) *
        (finiteSectionTailCost (B j) (N j) + finiteSectionTailDrift (B j) (A j) (N j)))
        atTop atTop := by
  obtain ⟨D, hD, hcost⟩ := lateSolve_mass_loss_upper
  intro B A N hN hlate hbd
  have hE : limitEnergy ≠ 0 := fun h =>
    hbd (boundary_eq_zero_iff_one_mem.mpr (limitEnergy_zero_iff_mem.mp h))
  have hA : Tendsto (fun j => A j + 1) atTop atTop :=
    tendsto_atTop_mono' _ (hlate.mono fun _ h => h.2) hN
  have hlow := ((energy_tendsto.comp hA).pow 2).eventually_const_lt
    (half_lt_self (sq_pos_of_ne_zero hE))
  let S := fun j : ℕ => (N j : ℝ) * sectionTailDamping lateSolveExponent.val (N j) *
    (finiteSectionTailCost (B j) (N j) + finiteSectionTailDrift (B j) (A j) (N j))
  let q := fun j : ℕ => D * sectionTailDamping lateSolveExponent.val (N j)
  have hq : Tendsto q atTop (𝓝 0) := by
    simpa only [q, Function.comp_def, mul_zero] using
      (((sectionTailDamping_tendsto lateSolveExponent.val lateSolveExponent.property).comp hN).const_mul D)
  have hp : ∀ᶠ j : ℕ in atTop, limitEnergy ^ 2 / 2 ≤ (1 + S j) * q j := by
    filter_upwards [hlow, hlate, hN.eventually hcost] with j hj hlatej hcj
    change limitEnergy ^ 2 / 2 < energy (A j + 1) ^ 2 at hj
    rw [packet_energy_eq_original] at hj
    apply (hj.le.trans (hcj (B j) (A j) hlatej.1 hlatej.2)).trans_eq
    dsimp only [S, q]
    ring
  have ht : Tendsto (fun j => 1 + S j) atTop atTop :=
    tendsto_atTop_of_pos_le_mul_tendsto_zero (half_pos (sq_pos_of_ne_zero hE))
      (Eventually.of_forall fun j => mul_nonneg hD.le (Real.exp_pos _).le) hq hp
  apply tendsto_atTop.mpr
  intro t
  filter_upwards [ht.eventually (eventually_ge_atTop (1 + t))] with j hj
  change 1 + t ≤ 1 + S j at hj
  change t ≤ S j
  linarith only [hj]

/-- One sufficiently late Gram solve per physical cutoff suffices when its
complete change and the base tail have a common cofinal scaled budget. The
chosen later cutoff may grow arbitrarily fast relative to the physical cutoff. -/
theorem riemannHypothesis_of_bounded_lateSolve_cost (B A N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hlate : ∀ᶠ j : ℕ in atTop, B j ≤ A j ∧ N j ≤ A j + 1)
    (C : ℝ) (hC : ∃ᶠ j : ℕ in atTop, (N j : ℝ) * sectionTailDamping lateSolveExponent.val (N j) *
      (finiteSectionTailCost (B j) (N j) + finiteSectionTailDrift (B j) (A j) (N j)) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_boundary_eq_zero
  by_contra hbd
  have ht := lateSolve_cost_barrier B A N hN hlate hbd
  obtain ⟨j, hj, hj'⟩ := (hC.and_eventually (ht.eventually_gt_atTop C)).exists
  exact (not_lt_of_ge hj) hj'

/-- info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection.riemannHypothesis_of_bounded_lateSolve_cost'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_bounded_lateSolve_cost

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
