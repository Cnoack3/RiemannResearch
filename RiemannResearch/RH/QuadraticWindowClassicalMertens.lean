import RiemannResearch.RH.CanonicalMobiusLogEnvelopeEnergy
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensClassicalContour
import RiemannResearch.Analysis.MertensEntropyOptimum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Classical Mertens cancellation on quadratic Pareto windows

The checked classical contour bound supplies both arithmetic inputs of the
quadratic-window test at each strictly interior exponential coefficient.
The entropy estimate controls the loss in the reciprocal partial sum.

Source: the arithmetic argument in QCanonicalMobiusCostRates. The Pareto window
uses both the reciprocal charge and the entire ordinary Mertens tail.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimeNumberTheorem RiemannResearch.Analysis

/-- Every positive coefficient below the repository's classical contour endpoint
works for the simultaneous ordinary-tail and reciprocal estimate. -/
theorem mobius_quadratic_window_rates_of_classical_contour (c : ℝ) (hc : 0 < c)
    (hce : c < Quantitative.MobiusContour.contourEndpoint) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      let ε := C * Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))
      (∀ t : ℕ, N ≤ t →
        |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ ε * (t : ℝ)) ∧
      |mobiusReciprocalSum N| ≤ ε := by
  obtain ⟨b,hcb,hbe⟩ := exists_between hce
  have hb : 0 < b := hc.trans hcb
  obtain ⟨T,hT⟩ := eventually_atTop.mp (M_sqrt_log_eventually_of_lt_contourEndpoint b hb hbe)
  have htop : Tendsto (fun N : ℕ => b * Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul_atTop hb
  have hTH : ∀ᶠ N : ℕ in atTop, T ≤ (N:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  let K := (b/(b-c))*Real.exp (-(c/b))
  let C := max 1 (5*K)
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  filter_upwards [hTH, htop.eventually (eventually_ge_atTop 6), eventually_ge_atTop (1:ℕ)]
    with N hNT hlarge hN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  let u := Real.sqrt (Real.log (N:ℝ))
  let e := Real.exp (-b*u)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have he : 0 < e := Real.exp_pos _
  have heone : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hesmall : e*(1+Real.log (1/e)) ≤ 1/2 := by
    simpa only [e, neg_mul] using exponential_entropy_small (b*u) hlarge
  have htail (y : ℝ) (hy : (N:ℝ) ≤ y) : |M y| ≤ e*y := by
    have hmono : u ≤ Real.sqrt (Real.log y) := Real.sqrt_le_sqrt (Real.log_le_log hNR hy)
    have hexp : Real.exp (-b*Real.sqrt (Real.log y)) ≤ e := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ ≤ y * Real.exp (-b*Real.sqrt (Real.log y)) := hT y (hNT.trans hy)
      _ ≤ y * e := mul_le_mul_of_nonneg_left hexp (hNR.le.trans hy)
      _ = _ := mul_comm _ _
  have hcoef : e ≤ C * Real.exp (-c*u) := by
    have h1 : e ≤ Real.exp (-c*u) := Real.exp_le_exp.mpr (by nlinarith)
    calc
      _ ≤ 1 * Real.exp (-c*u) := by simpa using h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  change (∀ t : ℕ, N ≤ t → _ ≤ C * Real.exp (-c*u) * (t:ℝ)) ∧ _ ≤ C * Real.exp (-c*u)
  constructor
  · intro t ht
    have hi := M_nat_difference 0 t (Nat.zero_le t)
    have hset : Finset.Ioc 0 t = Finset.Icc 1 t := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    have hz : M (0:ℝ) = 0 := by
      have hI : Finset.Iic (0:ℕ) = {0} := by ext k; simp
      simp [M, hI]
    rw [hset, Nat.cast_zero, hz, sub_zero] at hi
    rw [← hi]
    exact (htail t (by exact_mod_cast ht)).trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))
  · have hm := (canonicalMobius_energy_of_uniform_mertens_log N hN e he heone hesmall htail).1
    have hopt : e*(1+Real.log (1/e)) ≤ K*Real.exp (-c*u) :=
      exponential_entropy_le_optimal_rate b c u hb hcb
    calc
      _ ≤ 5 * (e * (1 + Real.log (1/e))) := hm
      _ ≤ 5 * (K * Real.exp (-c*u)) := mul_le_mul_of_nonneg_left hopt (by norm_num)
      _ = 5*K * Real.exp (-c*u) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end RiemannResearch.RH.Pareto
