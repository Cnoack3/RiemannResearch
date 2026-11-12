import RiemannResearch.RH.QCanonicalMobiusCost
import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.RH.CanonicalMobiusLogEnvelopeEnergy
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensClassicalContour
import RiemannResearch.Analysis.MertensEntropyOptimum

/-!
# Classical Mertens savings in the complete legal cost

Source: the user's request to improve the explicit-family cost using previous
research. The repository's proved classical Mertens contour bound is combined
with its signed Mobius energy transfer. Every positive rate below the certified
contour endpoint survives. All logarithmic-power savings also hold. These
remain square-root-power cost bounds; no RH-strength energy provider is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QCanonicalMobiusCost
open Pareto ZetaTwoHilbert ZetaTwoProbability QParetoEquivalence
open QReciprocalMetric QReciprocalCostEquivalence QExactHeadCost QMobiusExactHead

open RiemannResearch.Analysis

theorem balanced_cost_eventual_stretched :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℕ in atTop,
      cost ((H : ℝ)^2)⁻¹ qOne (exactHead H) ≤
        12/(zetaTwo*(H : ℝ)^2) + C/(H : ℝ) *
          Real.exp (-a*logProductPower (1 / 11) (6+Real.log (H : ℝ))) := by
  obtain ⟨a,ha,C,hC,hE⟩ := canonicalMobius_eventual_stretched_bounds
  refine ⟨a,ha,(4/zetaTwo)*C,by positivity [zetaTwo_pos],?_⟩
  filter_upwards [hE, eventually_ge_atTop (1 : ℕ)] with H he hH
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ (4/zetaTwo)*((H : ℝ)^2)⁻¹*‖canonicalMobiusHilbert H‖ ^ 2 :=
      balanced_cost_source_upper H hH
    _ ≤ (4/zetaTwo)*((H : ℝ)^2)⁻¹*
        (3+C*(H : ℝ)*Real.exp (-a*logProductPower (1 / 11) (6+Real.log (H : ℝ)))) :=
      mul_le_mul_of_nonneg_left he.2 (by positivity [zetaTwo_pos])
    _ = _ := by field_simp; ring

theorem balanced_cost_eventual_log_power (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℕ in atTop,
      cost ((H : ℝ)^2)⁻¹ qOne (exactHead H) ≤
        12/(zetaTwo*(H : ℝ)^2) +
          C/((H : ℝ)*(6+Real.log (H : ℝ))^k) := by
  obtain ⟨a,ha,C,hC,hE⟩ := balanced_cost_eventual_stretched
  obtain ⟨B,hB,hpow⟩ := logProductExp_le_inverse_nat_power a (1 / 11) ha (by norm_num) k
  refine ⟨C*B,mul_nonneg hC hB,?_⟩
  filter_upwards [hE, eventually_ge_atTop (1 : ℕ)] with H he hH
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hp := hpow (6+Real.log (H : ℝ)) (by linarith [Real.log_nonneg hHR])
  calc
    _ ≤ 12/(zetaTwo*(H : ℝ)^2) +
        C/(H : ℝ)*Real.exp (-a*logProductPower (1 / 11) (6+Real.log (H : ℝ))) := he
    _ ≤ 12/(zetaTwo*(H : ℝ)^2) + C/(H : ℝ)*(B/(6+Real.log (H : ℝ))^k) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (div_nonneg hC (Nat.cast_nonneg H)))
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Every positive coefficient below the certified classical endpoint survives
in the complete cost. No Mertens or RH hypothesis remains. -/
theorem balanced_cost_eventual_sqrt_log (c : ℝ) (hc : 0 < c)
    (hcE : c < Quantitative.MobiusContour.contourEndpoint) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℕ in atTop,
      cost ((H : ℝ)^2)⁻¹ qOne (exactHead H) ≤
        12/(zetaTwo*(H : ℝ)^2) +
          C/(H : ℝ)*Real.exp (-c*Real.sqrt (Real.log (H : ℝ))) := by
  obtain ⟨b,hcb,hbE⟩ := exists_between hcE
  have hb : 0 < b := hc.trans hcb
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (M_sqrt_log_eventually_of_lt_contourEndpoint b hb hbE)
  have htop : Tendsto (fun H : ℕ => b*Real.sqrt (Real.log (H : ℝ))) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul_atTop hb
  have hTH : ∀ᶠ H : ℕ in atTop, T ≤ (H : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun H : ℕ => (H : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  let K := (b/(b-c))*Real.exp (-(c/b))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(1040/zetaTwo)*K,by positivity [zetaTwo_pos],?_⟩
  filter_upwards [hTH, htop.eventually (eventually_ge_atTop 6),
    eventually_ge_atTop (1 : ℕ)] with H hTH hlarge hH
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  let u := Real.sqrt (Real.log (H : ℝ))
  let ε := Real.exp (-b*u)
  have hε : 0 < ε := Real.exp_pos _
  have hεone : ε ≤ 1 := Real.exp_le_one_iff.mpr (by dsimp [u]; nlinarith [Real.sqrt_nonneg (Real.log (H : ℝ))])
  have hsmall : ε*(1+Real.log (1/ε)) ≤ 1/2 := by
    simpa only [ε, neg_mul] using exponential_entropy_small (b*u) hlarge
  have hM (y : ℝ) (hy : (H : ℝ) ≤ y) : |M y| ≤ ε*y := by
    have hy0 : 0 ≤ y := hHR.le.trans hy
    have hmono : u ≤ Real.sqrt (Real.log y) :=
      Real.sqrt_le_sqrt (Real.log_le_log hHR hy)
    have he : Real.exp (-b*Real.sqrt (Real.log y)) ≤ ε := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ ≤ y*Real.exp (-b*Real.sqrt (Real.log y)) := hT y (hTH.trans hy)
      _ ≤ y*ε := mul_le_mul_of_nonneg_left he hy0
      _ = _ := by ring
  have hE := (canonicalMobius_energy_of_uniform_mertens_log H hH ε hε hεone hsmall hM).2
  have he : ε*(1+Real.log (1/ε)) ≤ K*Real.exp (-c*u) :=
    exponential_entropy_le_optimal_rate b c u hb hcb
  have hEu : ‖canonicalMobiusHilbert H‖ ^ 2/(H : ℝ) ≤
      3/(H : ℝ)+260*(K*Real.exp (-c*u)) := by linarith
  have hEfull := (div_le_iff₀ hHR).mp hEu
  calc
    _ ≤ (4/zetaTwo)*((H : ℝ)^2)⁻¹*‖canonicalMobiusHilbert H‖ ^ 2 :=
      balanced_cost_source_upper H hH
    _ ≤ (4/zetaTwo)*((H : ℝ)^2)⁻¹*
        ((3/(H : ℝ)+260*(K*Real.exp (-c*u)))*(H : ℝ)) :=
      mul_le_mul_of_nonneg_left hEfull (by positivity [zetaTwo_pos])
    _ = _ := by dsimp [u]; field_simp; ring

theorem balanced_cost_global_sqrt_log (c : ℝ) (hc : 0 < c)
    (hcE : c < Quantitative.MobiusContour.contourEndpoint) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, 0 < H →
      cost ((H : ℝ)^2)⁻¹ qOne (exactHead H) ≤
        12/(zetaTwo*(H : ℝ)^2) +
          C/(H : ℝ)*Real.exp (-c*Real.sqrt (Real.log (H : ℝ))) := by
  obtain ⟨C,hC,he⟩ := balanced_cost_eventual_sqrt_log c hc hcE
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let L : ℝ := max 1 (N : ℝ)
  let B : ℝ := max C ((16/zetaTwo)*Real.exp (c*Real.sqrt (Real.log L)))
  have hCB : C ≤ B := le_max_left _ _
  have hbase : (16/zetaTwo)*Real.exp (c*Real.sqrt (Real.log L)) ≤ B :=
    le_max_right _ _
  refine ⟨B,hC.trans hCB,?_⟩
  intro H hH
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hexp : 0 ≤ Real.exp (-c*Real.sqrt (Real.log (H : ℝ))) := (Real.exp_pos _).le
  by_cases hNH : N ≤ H
  · exact (hN H hNH).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCB hHR.le) hexp))
  · have hHL : (H : ℝ) ≤ L := by
      have hHN : (H : ℝ) ≤ N := by exact_mod_cast (show H ≤ N by omega)
      exact hHN.trans (le_max_right _ _)
    have hu : Real.sqrt (Real.log (H : ℝ)) ≤ Real.sqrt (Real.log L) :=
      Real.sqrt_le_sqrt (Real.log_le_log hHR hHL)
    have hh : 1 ≤ Real.exp (c*Real.sqrt (Real.log L)) *
        Real.exp (-c*Real.sqrt (Real.log (H : ℝ))) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    have h16 : 0 ≤ 16/zetaTwo := by positivity [zetaTwo_pos]
    have hgain : 16/zetaTwo ≤ B*Real.exp (-c*Real.sqrt (Real.log (H : ℝ))) := by
      have h1 := mul_le_mul_of_nonneg_left hh h16
      have h2 := mul_le_mul_of_nonneg_right hbase hexp
      nlinarith only [h1,h2]
    calc
      _ ≤ 16/(zetaTwo*(H : ℝ)) := balanced_cost_explicit H hH
      _ = (16/zetaTwo)/(H : ℝ) := by ring
      _ ≤ (B*Real.exp (-c*Real.sqrt (Real.log (H : ℝ))))/(H : ℝ) :=
        div_le_div_of_nonneg_right hgain hHR.le
      _ ≤ _ := by
        have hz : 0 ≤ 12/(zetaTwo*(H : ℝ)^2) := by positivity [zetaTwo_pos]
        rw [mul_div_right_comm]
        linarith

theorem legalFamily_global_sqrt_log (c : ℝ) (hc : 0 < c)
    (hcE : c < Quantitative.MobiusContour.contourEndpoint) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      cost (QReciprocalRegularizedCriterion.regularizationScale j) qOne (legalFamily j) ≤
        12/(zetaTwo*(stage j : ℝ)^2) +
          C/(stage j : ℝ)*Real.exp (-c*Real.sqrt (Real.log (stage j : ℝ))) := by
  obtain ⟨C,hC,h⟩ := balanced_cost_global_sqrt_log c hc hcE
  refine ⟨C,hC,fun j => ?_⟩
  simpa only [legalFamily, regularizationScale_eq] using h (stage j) (stage_pos j)

theorem legalFamily_eventual_log_power (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop,
      cost (QReciprocalRegularizedCriterion.regularizationScale j) qOne (legalFamily j) ≤
        12/(zetaTwo*(stage j : ℝ)^2) +
          C/((stage j : ℝ)*(6+Real.log (stage j : ℝ))^k) := by
  obtain ⟨C,hC,h⟩ := balanced_cost_eventual_log_power k
  refine ⟨C,hC,?_⟩
  simpa only [legalFamily, regularizationScale_eq] using stage_tendsto.eventually h

end RiemannResearch.RH.QCanonicalMobiusCost
