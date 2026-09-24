import RiemannResearch.RH.ExactHeadWeightedEnergy
import RiemannResearch.RH.CanonicalMobiusQuantitativeEnergy

/-!
# Unconditional moving Hardy half-planes to the left of the endpoint

Source: the user's September 24, 2026 request to combine quantitative arithmetic
and weighted-energy bridges. The explicit arithmetic ceiling supplies every
premise in the final moving-Hardy theorem. Its boundaries tend to one from
below, not to one half. The RH-strength moving bound therefore remains open.
The finite scheduling family also retains an arbitrary theta in [0,1].
-/

noncomputable section

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set Filter WeightedMellin
open scoped Topology

/-- An explicit moving energy exponent, determined by a normalized critical
residual-energy budget. Its associated Hardy boundary is half this value. -/
def mobiusBudgetExponent (q : ℕ → ℝ) (N : ℕ) : ℝ :=
  2 + (1 / 2 : ℝ) * Real.log (q N) / Real.log ((N : ℝ) + 1)

/-- Any vanishing numerical ceiling for normalized critical residual energy
supplies a uniform vanishing bound on every line in a moving half-plane. -/
theorem canonicalMobiusResidual_moving_budget
    {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0))
    (hql : ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1)⁻¹ ≤ q N)
    (hbudget : ∀ᶠ N : ℕ in atTop,
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤ ((N : ℝ) + 1) * q N) :
    ∀ᶠ N : ℕ in atTop,
      (1 ≤ mobiusBudgetExponent q N ∧ mobiusBudgetExponent q N ≤ 2) ∧
      energy (complexPhysicalStep (hilbertOne - canonicalMobiusHilbert N))
          (mobiusBudgetExponent q N) ≤ Real.sqrt (q N) ∧
      ∀ σ : ℝ, mobiusBudgetExponent q N / 2 < σ →
        (∫ w : ℝ, ‖paretoMellin (hilbertOne - canonicalMobiusHilbert N)
          (verticalPoint σ w)‖ ^ 2) ≤ Real.sqrt (q N) := by
  have hqu : ∀ᶠ N : ℕ in atTop, q N < 1 := hq.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hql, hbudget, hqu, eventually_ge_atTop (1 : ℕ)] with N hlow hE hup hN
  have hb : 1 < (N : ℝ) + 1 := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpos : 0 < q N := lt_of_lt_of_le (inv_pos.mpr (by positivity)) hlow
  have hu := log_schedule_mem_Icc hb hpos hlow hup.le
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  change 1 ≤ mobiusBudgetExponent q N ∧ mobiusBudgetExponent q N ≤ 2 at hu
  have hc : ((N : ℝ) + 1) ^ (1 - mobiusBudgetExponent q N) *
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤ Real.sqrt (q N) := by
    have h := cutoff_power_times_energy_le (θ := (1 / 2 : ℝ)) hb hpos hE
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at h
    exact h
  refine ⟨hu, ?_, ?_⟩
  · exact (canonicalMobiusResidual_weightedEnergy_le N _ hu.1).trans hc
  · intro σ hσ
    exact (canonicalMobiusResidual_hardyLine_le N _ σ hu.1 hσ).trans hc

/-- Energy tends to zero at the explicit moving exponent. This theorem has
only a vanishing normalized-energy budget, not an RH-strength assumption. -/
theorem canonicalMobiusResidual_moving_energy_tendsto
    {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0))
    (hql : ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1)⁻¹ ≤ q N)
    (hbudget : ∀ᶠ N : ℕ in atTop,
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤ ((N : ℝ) + 1) * q N) :
    Tendsto (fun N => energy
      (complexPhysicalStep (hilbertOne - canonicalMobiusHilbert N))
      (mobiusBudgetExponent q N)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N => Real.sqrt (q N)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hq
  apply squeeze_zero' _ ((canonicalMobiusResidual_moving_budget hq hql hbudget).mono
    (fun N hN => hN.2.1)) hs
  apply Filter.Eventually.of_forall
  intro N
  unfold energy
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _)

/-- Every selection of lines inside the moving half-planes has vanishing
complete Hardy line integral. The bound is uniform over the line choice. -/
theorem canonicalMobiusResidual_moving_lines_tendsto
    {q σ : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0))
    (hql : ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1)⁻¹ ≤ q N)
    (hbudget : ∀ᶠ N : ℕ in atTop,
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤ ((N : ℝ) + 1) * q N)
    (hσ : ∀ᶠ N : ℕ in atTop, mobiusBudgetExponent q N / 2 < σ N) :
    Tendsto (fun N => ∫ w : ℝ,
      ‖paretoMellin (hilbertOne - canonicalMobiusHilbert N)
        (verticalPoint (σ N) w)‖ ^ 2) atTop (𝓝 0) := by
  have hs : Tendsto (fun N => Real.sqrt (q N)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have hle : ∀ᶠ N : ℕ in atTop,
      (∫ w : ℝ, ‖paretoMellin (hilbertOne - canonicalMobiusHilbert N)
        (verticalPoint (σ N) w)‖ ^ 2) ≤ Real.sqrt (q N) := by
    filter_upwards [canonicalMobiusResidual_moving_budget hq hql hbudget, hσ] with N hN hNσ
    exact hN.2.2 _ hNσ
  exact squeeze_zero' (Filter.Eventually.of_forall
    (fun N => integral_nonneg (fun w => sq_nonneg _))) hle hs

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set Filter WeightedMellin
open scoped Topology

/-- A logarithmic floor on the numerical budget makes the explicit moving
Hardy boundary tend to the known endpoint 1 from the left. -/
theorem mobiusBudgetExponent_tendsto_two {q : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 0))
    (hql : ∀ᶠ N : ℕ in atTop, (Real.log ((N : ℝ) + 1))⁻¹ ≤ q N) :
    Tendsto (mobiusBudgetExponent q) atTop (𝓝 2) := by
  have hbtop : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  have hltop : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hbtop
  have hlogdiv : Tendsto (fun N : ℕ =>
      Real.log (Real.log ((N : ℝ) + 1)) / Real.log ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hltop
  have hqu : ∀ᶠ N : ℕ in atTop, q N < 1 := hq.eventually (gt_mem_nhds zero_lt_one)
  have hbds : ∀ᶠ N : ℕ in atTop,
      0 ≤ -Real.log (q N) / Real.log ((N : ℝ) + 1) ∧
      -Real.log (q N) / Real.log ((N : ℝ) + 1) ≤
        Real.log (Real.log ((N : ℝ) + 1)) / Real.log ((N : ℝ) + 1) := by
    filter_upwards [hql, hqu, eventually_ge_atTop (1 : ℕ)] with N hlow hup hN
    have hb : 1 < (N : ℝ) + 1 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hl : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos hb
    have hq0 : 0 < q N := lt_of_lt_of_le (inv_pos.mpr hl) hlow
    have hlogq : Real.log (q N) ≤ 0 := Real.log_nonpos hq0.le hup.le
    have hlo : -Real.log (Real.log ((N : ℝ) + 1)) ≤ Real.log (q N) := by
      simpa only [Real.log_inv] using Real.log_le_log (inv_pos.mpr hl) hlow
    refine ⟨div_nonneg (by linarith) hl.le, ?_⟩
    exact div_le_div_of_nonneg_right (by linarith) hl.le
  have hr : Tendsto (fun N : ℕ => -Real.log (q N) / Real.log ((N : ℝ) + 1))
      atTop (𝓝 0) :=
    squeeze_zero' (hbds.mono (fun N hN => hN.1)) (hbds.mono (fun N hN => hN.2)) hlogdiv
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).sub
    (hr.const_mul (1 / 2 : ℝ))
  convert h using 1
  · funext N
    unfold mobiusBudgetExponent
    ring
  · norm_num

theorem mobiusBudgetHardyBoundary_tendsto_one {q : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 0))
    (hql : ∀ᶠ N : ℕ in atTop, (Real.log ((N : ℝ) + 1))⁻¹ ≤ q N) :
    Tendsto (fun N => mobiusBudgetExponent q N / 2) atTop (𝓝 1) := by
  simpa using (mobiusBudgetExponent_tendsto_two hq hql).div_const 2

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set Filter WeightedMellin
open scoped Topology

theorem canonicalMobiusResidualCeiling_log_lower (C : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    (Real.log ((N : ℝ) + 1))⁻¹ ≤ canonicalMobiusResidualCeiling C N := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hLp : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  have hLL : 0 ≤ Real.log (Real.log (N : ℝ) + 3) :=
    Real.log_nonneg (by linarith)
  have hlogmono : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hinv : (Real.log ((N : ℝ) + 1))⁻¹ ≤ 1 / Real.log (N : ℝ) := by
    rw [← one_div]
    apply (div_le_div_iff₀ hLp hL).2
    simpa using hlogmono
  have hr : 1 / Real.log (N : ℝ) ≤ canonicalMobiusEnergyRate N := by
    unfold canonicalMobiusEnergyRate
    exact div_le_div_of_nonneg_right (by linarith) hL.le
  have hr0 := canonicalMobiusEnergyRate_nonneg N hN
  have hB : 4 * canonicalMobiusEnergyRate N ≤ canonicalMobiusEnergyCeiling C N := by
    unfold canonicalMobiusEnergyCeiling
    have h0 : 0 ≤ 3 / (N : ℝ) := by positivity
    nlinarith [mul_nonneg (sq_nonneg (2 + 4 * C)) hr0,
      mul_nonneg (sq_nonneg (2 + 4 * C)) (sq_nonneg (canonicalMobiusEnergyRate N))]
  have hq : canonicalMobiusEnergyRate N ≤ canonicalMobiusResidualCeiling C N := by
    unfold canonicalMobiusResidualCeiling
    have h0 : 0 ≤ 3 / (N : ℝ) := by positivity
    linarith
  exact hinv.trans (hr.trans hq)

/-- Fully unconditional explicit moving half-planes strictly to the left of
Re(s)=1, with uniform vanishing residual line energy. Their boundary tends to
1, not to the critical line 1/2. -/
theorem canonicalMobiusResidual_explicit_moving_hardy :
    ∃ C : ℝ, 0 ≤ C ∧
      Tendsto (mobiusBudgetExponent (canonicalMobiusResidualCeiling C)) atTop (𝓝 2) ∧
      Tendsto (fun N => mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N / 2)
        atTop (𝓝 1) ∧
      ∀ᶠ N : ℕ in atTop,
        (1 < mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N ∧
          mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N < 2) ∧
        energy (complexPhysicalStep (hilbertOne - canonicalMobiusHilbert N))
          (mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N) ≤
            Real.sqrt (canonicalMobiusResidualCeiling C N) ∧
        ∀ σ : ℝ, mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N / 2 < σ →
          (∫ w : ℝ, ‖paretoMellin (hilbertOne - canonicalMobiusHilbert N)
            (verticalPoint σ w)‖ ^ 2) ≤ Real.sqrt (canonicalMobiusResidualCeiling C N) := by
  obtain ⟨C, hC, hb⟩ := canonicalMobiusResidual_eventual_explicit_ceiling
  have hq := canonicalMobiusResidualCeiling_tendsto_zero C
  have hlow : ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1)⁻¹ ≤ canonicalMobiusResidualCeiling C N := by
    simpa only [one_div] using hb.mono (fun N hN => hN.1)
  have hE := hb.mono (fun N hN => hN.2)
  have hloglow : ∀ᶠ N : ℕ in atTop,
      (Real.log ((N : ℝ) + 1))⁻¹ ≤ canonicalMobiusResidualCeiling C N :=
    (eventually_ge_atTop (2 : ℕ)).mono (fun N hN => canonicalMobiusResidualCeiling_log_lower C N hN)
  have hu := mobiusBudgetExponent_tendsto_two hq hloglow
  have hu1 := mobiusBudgetHardyBoundary_tendsto_one hq hloglow
  refine ⟨C, hC, hu, hu1, ?_⟩
  have huLower : ∀ᶠ N : ℕ in atTop,
      1 < mobiusBudgetExponent (canonicalMobiusResidualCeiling C) N :=
    hu.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hqUpper : ∀ᶠ N : ℕ in atTop, canonicalMobiusResidualCeiling C N < 1 :=
    hq.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [canonicalMobiusResidual_moving_budget hq hlow hE, huLower, hqUpper,
    hlow, eventually_ge_atTop (1 : ℕ)] with N hM huN hqN hlN hN
  have hbN : 1 < (N : ℝ) + 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hl : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos hbN
  have hpos : 0 < canonicalMobiusResidualCeiling C N :=
    lt_of_lt_of_le (inv_pos.mpr (by positivity)) hlN
  have hneg : Real.log (canonicalMobiusResidualCeiling C N) < 0 := Real.log_neg hpos hqN
  have hd : (1 / 2 : ℝ) * Real.log (canonicalMobiusResidualCeiling C N) /
      Real.log ((N : ℝ) + 1) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hneg) hl
  refine ⟨⟨huN, ?_⟩, hM.2⟩
  unfold mobiusBudgetExponent
  linarith

end RiemannResearch.RH.Pareto


namespace RiemannResearch.RH.Pareto
open MeasureTheory Set Filter WeightedMellin
open scoped Topology

/-- The arithmetic ceiling controls the actual approximant line integrals,
simultaneously at every intermediate energy exponent. -/
theorem canonicalMobius_eventual_intermediate_hardy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ u σ : ℝ, 1 ≤ u → u/2 < σ →
      (∫ w : ℝ, ‖paretoMellin (canonicalMobiusHilbert N) (verticalPoint σ w)‖^2) ≤
        (1-((N : ℝ)+1)^(-u))/u + ((N : ℝ)+1)^(1-u) *
          ((N : ℝ)*canonicalMobiusEnergyCeiling C N-1+1/((N : ℝ)+1)) := by
  obtain ⟨C,hC,hE⟩ := canonicalMobiusHilbert_eventual_optimized_energy
  refine ⟨C,hC,?_⟩
  filter_upwards [hE, eventually_ge_atTop (2 : ℕ)] with N he hN
  intro u σ hu hσ
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  change ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤ canonicalMobiusEnergyCeiling C N at he
  have hfull : ‖canonicalMobiusHilbert N‖^2 ≤ (N : ℝ)*canonicalMobiusEnergyCeiling C N := by
    have h := (div_le_iff₀ hNR).mp he
    nlinarith
  have h := canonicalMobius_hardy_line_sharp N hu hσ
  rw [complexPhysicalStep_critical_energy] at h
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left
  · linarith
  · exact Real.rpow_nonneg (by positivity) _

/-- Full finite scheduling family; choosing theta below one trades the
leftward boundary shift against the remaining positive power of q. -/
theorem canonicalMobiusResidual_scheduled_line_bound
    (N : ℕ) (hN : 0 < N) (q θ σ : ℝ) (hq : 0 < q)
    (hql : ((N : ℝ)+1)⁻¹ ≤ q) (hqu : q ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbudget : ‖hilbertOne-canonicalMobiusHilbert N‖^2 ≤ ((N : ℝ)+1)*q)
    (hσ : (2+θ*Real.log q/Real.log ((N : ℝ)+1))/2 < σ) :
    (∫ w : ℝ, ‖paretoMellin (hilbertOne-canonicalMobiusHilbert N)
      (verticalPoint σ w)‖^2) ≤ q^(1-θ) := by
  have hb : 1 < (N : ℝ)+1 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hu := log_schedule_mem_Icc hb hq hql hqu hθ0 hθ1
  exact (canonicalMobiusResidual_hardyLine_le N _ σ hu.1 hσ).trans
    (cutoff_power_times_energy_le hb hq hbudget)

end RiemannResearch.RH.Pareto
