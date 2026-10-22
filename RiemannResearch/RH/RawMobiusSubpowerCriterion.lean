import RiemannResearch.RH.RawMobiusFiniteWindowCriterion
import RiemannResearch.RH.ExactHeadMovingHardyRH
import RiemannResearch.RH.ParetoPrimeSourceDivergence

/-!
# Cofinal subpower finite raw Mobius budgets imply RH

This connects the actual finite-window budget to the already established
exact-head zero obstruction. No sign-crossing hypothesis is needed. The
subpower estimate for this arithmetic budget remains an explicit open input.

Source: the user's Nyman--Beurling research request, September 24, 2026.
The proof combines the local finite-window identity with the local weighted
Mellin exact-head obstruction. No external Nyman--Beurling converse,
sign-change theorem, or asymptotic cancellation estimate is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open WeightedMellin

def rawMobiusSquareBudget (N : ℕ) : ℝ :=
  (N : ℝ)*(mobiusReciprocalSum N)^2 + rawMobiusMiddleEnergy N (N^2)

theorem rawMobiusSquareBudget_nonneg (N : ℕ) :
    0 ≤ rawMobiusSquareBudget N :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
    (rawMobiusMiddleEnergy_nonneg N (N^2))

private theorem norm_add_sq_budget (f g : ThresholdHilbert) :
    ‖f+g‖^2 ≤ 2*‖f‖^2+2*‖g‖^2 := by
  have hh := mul_self_le_mul_self (norm_nonneg (f+g)) (norm_add_le f g)
  nlinarith [sq_nonneg (‖f‖-‖g‖)]

/-- The boundary correction is controlled by the finite reciprocal head. -/
theorem canonicalMobius_correction_norm_sq_le_head (N : ℕ) (hN : 0 < N) :
    ‖(((N+1 : ℕ) : ℝ)*mobiusReciprocalSum N) •
      normalizedResidueHilbert (N+1) (Nat.succ_pos N)‖^2 ≤
      4*(N : ℝ)*(mobiusReciprocalSum N)^2 := by
  have hden : (0 : ℝ) < ((N+1 : ℕ) : ℝ) := by positivity
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc
    _ ≤ (((N+1 : ℕ) : ℝ)*mobiusReciprocalSum N)^2 *
        (2/((N+1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (normalizedResidue_norm_sq_le (N+1) (Nat.succ_pos N)) (sq_nonneg _)
    _ = 2*((N+1 : ℕ) : ℝ)*(mobiusReciprocalSum N)^2 := by
      field_simp [hden.ne']
    _ ≤ _ := by
      push_cast
      nlinarith [sq_nonneg (mobiusReciprocalSum N)]

/-- Full norm of the legal exact-head family is bounded by finite arithmetic data. -/
theorem canonicalMobius_norm_sq_le_raw_square_budget (N : ℕ) (hN : 0 < N) :
    ‖canonicalMobiusHilbert N‖^2 ≤ 12*rawMobiusSquareBudget N+8 := by
  let U := hilbertOne-rawMobiusHilbert N
  let c := (((N+1 : ℕ) : ℝ)*mobiusReciprocalSum N) •
    normalizedResidueHilbert (N+1) (Nat.succ_pos N)
  have hraw := norm_add_sq_budget hilbertOne (-U)
  have hid : hilbertOne + -U = rawMobiusHilbert N := by dsimp [U]; abel
  rw [hid, norm_neg, hilbertOne_norm_sq] at hraw
  have hc := canonicalMobius_correction_norm_sq_le_head N hN
  change ‖c‖^2 ≤ _ at hc
  have hcan := norm_add_sq_budget (rawMobiusHilbert N) c
  rw [← canonicalMobiusHilbert_eq_raw_add] at hcan
  have hU := rawMobius_energy_le_square_window N hN
  change ‖U‖^2 ≤ _ at hU
  have hm := rawMobiusMiddleEnergy_nonneg N (N^2)
  unfold rawMobiusSquareBudget
  nlinarith

/-- At the critical exponent the continuous physical energy is the Pareto norm. -/
theorem complexPhysicalStep_critical_energy (f : ThresholdHilbert) :
    energy (complexPhysicalStep f) 1 = ‖f‖^2 := by
  rw [← mellinWeightedStep_energy]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  change ‖complexPhysicalStep f x‖^2 * x^(-(1 : ℝ)-1) =
    ‖mellinWeightedStep f x‖^2
  rw [mellinWeightedStep_norm_sq]
  simp only [complexPhysicalStep, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num [Real.rpow_neg hx0.le]
  ring

/-- A hypothetical zero forces a positive-power lower bound on the finite budget. -/
theorem rawMobiusSquareBudget_lower_of_zeta_zero
    (N : ℕ) (hN : 3 ≤ N) (s : ℂ)
    (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ((2*s.re-1)/(4*‖s‖^2))*((N : ℝ)+1)^(2*s.re-1) ≤
      12*rawMobiusSquareBudget N+8 := by
  have hlegal : canonicalMobiusHilbert N ∈ hilbertLegalClosure {n : ℕ | 0 < n} :=
    CoefficientStabilization.closedSpace_le_legalClosure
      (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N)
  have hnull := paretoMellin_zero_on_legalClosure_of_zeta
    {n : ℕ | 0 < n} (fun _ hn => hn) s hs hs1 hz hlegal
  have hl := exactHead_weightedEnergy_lower_of_mellin_zero
    (canonicalMobiusHilbert N) N hN
    (fun k hk hkN => canonicalMobiusHilbert_exact N k hk hkN)
    1 (by norm_num) s hs (by linarith) hnull
  rw [complexPhysicalStep_critical_energy] at hl
  exact hl.trans (canonicalMobius_norm_sq_le_raw_square_budget N (by omega))

/-- A separate cofinal set may be used for each positive exponent. The actual
    arithmetic subpower bounds are the explicit unresolved hypothesis. -/
theorem riemannHypothesis_of_frequently_subpower_raw_square_budget
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      rawMobiusSquareBudget N ≤ C*((N : ℝ)+1)^ε) :
    RiemannHypothesis := by
  have hright (s : ℂ) (hz : riemannZeta s = 0)
      (hs0 : 0 < s.re) (hs1 : s.re < 1) : s.re ≤ 1/2 := by
    by_contra hh
    have hs : (1/2 : ℝ) < s.re := lt_of_not_ge hh
    have hsne : s ≠ 1 := by intro he; simp [he] at hs1
    have hsne0 : s ≠ 0 := by intro he; simp [he] at hs0
    let ε : ℝ := (2*s.re-1)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    let c : ℝ := (2*s.re-1)/(4*‖s‖^2)
    have hc : 0 < c := by
      dsimp [c]
      exact div_pos (by linarith)
        (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hsne0) 2))
    obtain ⟨C,hC⟩ := hsub ε hε
    have hbase : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
      tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
    have hpow : Tendsto (fun N : ℕ => ((N : ℝ)+1)^ε) atTop atTop :=
      (tendsto_rpow_atTop hε).comp hbase
    obtain ⟨N,hCN,hN,hlarge⟩ :=
      (hC.and_eventually ((eventually_ge_atTop 3).and
        (hpow.eventually_gt_atTop ((12*|C|+8)/c+1)))).exists
    let q : ℝ := ((N : ℝ)+1)^ε
    have hq : 0 < q := Real.rpow_pos_of_pos (by positivity) _
    have hq1 : 1 ≤ q := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) N]) hε.le
    have hsplit : ((N : ℝ)+1)^(2*s.re-1) = q^2 := by
      rw [pow_two, ← Real.rpow_add (by positivity : 0 < (N : ℝ)+1)]
      congr 1
      dsimp [ε]
      ring
    have hl := rawMobiusSquareBudget_lower_of_zeta_zero N hN s hs hsne hz
    change c * ((N : ℝ)+1)^(2*s.re-1) ≤ _ at hl
    rw [hsplit] at hl
    have hupper : rawMobiusSquareBudget N ≤ |C| *q :=
      hCN.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq.le)
    have hlinear : c*q^2 ≤ (12*|C|+8)*q := by nlinarith
    have hlarge' : (12*|C|+8)/c+1 < q := hlarge
    have hmul : 12*|C|+8+c < c*q := by
      have hm := mul_lt_mul_of_pos_left hlarge' hc
      field_simp [hc.ne'] at hm
      nlinarith
    nlinarith [mul_pos hc hq]
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hr := Zeta23.zeta_reflect_zero ρ ⟨hz,h0,h1⟩
  have hrbound := hright (Zeta23.reflect ρ) hr.1 hr.2.1 hr.2.2
  have hbnd := hright ρ hz h0 h1
  simp [Zeta23.reflect] at hrbound
  linarith

end RiemannResearch.RH.Pareto
