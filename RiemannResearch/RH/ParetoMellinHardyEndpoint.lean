import RiemannResearch.RH.CanonicalMobiusExactCellEndpoint
import RiemannResearch.Analysis.WeightedMellinHardy
import RiemannResearch.RH.ParetoMellinFunctional

/-!
# Exact Mellin and Hardy identification at the endpoint

The actual step-function Mellin transform, complete continuous weighted energy,
and Hardy H2 norm at Re(s)=1 are identified here. Source: the endpoint argument
in HardyEndpointCompactness20260924.md, using the project's WeightedMellinHardy
Plancherel theorem. This completes the analytic identification required there.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- The actual complex-valued physical step profile. -/
def complexPhysicalStep (f : ThresholdHilbert) (x : ℝ) : ℂ :=
  (hilbertSequence f ⌊x⌋₊ : ℂ)

theorem complexPhysicalStep_measurable (f : ThresholdHilbert) :
    Measurable (complexPhysicalStep f) :=
  Complex.continuous_ofReal.measurable.comp
    ((measurable_of_countable (hilbertSequence f)).comp Nat.measurable_floor)

theorem complexPhysicalStep_finiteEnergy (f : ThresholdHilbert) :
    WeightedMellin.FiniteEnergy (complexPhysicalStep f) 1 := by
  refine ⟨complexPhysicalStep_measurable f, ?_⟩
  apply (paretoStepEnergy_integrable _ (hilbertSequence_square_summable f)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hp : x ^ (-(1 : ℝ) - 1) = 1 / x ^ 2 := by
    norm_num [Real.rpow_neg hx0.le]
  simp only [complexPhysicalStep, Complex.norm_real, Real.norm_eq_abs, sq_abs, hp]
  ring

theorem complexPhysicalStep_endpoint_finiteEnergy (f : ThresholdHilbert) :
    WeightedMellin.FiniteEnergy (complexPhysicalStep f) 2 :=
  WeightedMellin.finiteEnergy_mono (complexPhysicalStep_finiteEnergy f) (by norm_num)

theorem complexPhysicalStep_transform (f : ThresholdHilbert) :
    WeightedMellin.transform (complexPhysicalStep f) = paretoMellin f := by
  funext s
  exact (paretoMellin_eq_step_integral f s).symm

private theorem complexPhysicalStep_endpoint_density (f : ThresholdHilbert)
    {x : ℝ} (hx : 0 < x) :
    ‖complexPhysicalStep f x‖ ^ 2 * x ^ (-(2 : ℝ) - 1) =
      hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 3 := by
  have hp : x ^ (-(2 : ℝ) - 1) = 1 / x ^ 3 := by
    norm_num [Real.rpow_neg hx.le]
  simp only [complexPhysicalStep, Complex.norm_real, Real.norm_eq_abs, sq_abs, hp]
  ring

private def endpointStepCell (n : ℕ) : Set ℝ :=
  Ico ((n : ℝ) + 1) ((n : ℝ) + 2)

private theorem endpointStepCell_floor (n : ℕ) {x : ℝ}
    (hx : x ∈ endpointStepCell n) : ⌊x⌋₊ = n + 1 := by
  apply Nat.floor_eq_on_Ico
  simpa only [endpointStepCell, Nat.cast_add, Nat.cast_one, add_assoc,
    one_add_one_eq_two] using hx

private theorem endpointStepCell_disjoint :
    Pairwise (Function.onFun Disjoint endpointStepCell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact hij (Nat.add_right_cancel
    ((endpointStepCell_floor i hxi).symm.trans (endpointStepCell_floor j hxj)))

private theorem endpointStepCell_union : (⋃ n, endpointStepCell n) = Ici (1 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    change (n : ℝ) + 1 ≤ x ∧ x < (n : ℝ) + 2 at hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact le_trans (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hn.1
  · intro hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx
    have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx)
    let n := ⌊x⌋₊ - 1
    have hn : n + 1 = ⌊x⌋₊ := Nat.sub_add_cancel hf
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hlo := Nat.floor_le hx0
    have hhi := Nat.lt_floor_add_one x
    rw [← hn] at hlo hhi
    simpa only [endpointStepCell, Set.mem_Ico, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two] using And.intro hlo hhi

private theorem integral_inv_cube_endpointStepCell (n : ℕ) :
    (∫ x in endpointStepCell n, 1 / x ^ 3) = exactEndpointCellWeight (n + 1) := by
  have hab : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
  have hz : (0 : ℝ) ∉ Set.uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    rw [Set.uIcc_of_le hab]
    intro h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [h.1]
  have hp := integral_zpow (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (n := (-3 : ℤ)) (Or.inr ⟨by norm_num, hz⟩)
  have hfun : (fun x : ℝ => 1 / x ^ 3) = (fun x : ℝ => x ^ (-3 : ℤ)) := by
    funext x
    simp
  unfold endpointStepCell
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hfun, hp]
  rw [exactEndpointCellWeight_eq_sub (n + 1) (by omega)]
  norm_num
  ring

private theorem integral_endpoint_density_cell (f : ThresholdHilbert) (n : ℕ) :
    (∫ x in endpointStepCell n, hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 3) =
      exactEndpointCellWeight (n + 1) * hilbertSequence f (n + 1) ^ 2 := by
  calc
    _ = ∫ x in endpointStepCell n, hilbertSequence f (n + 1) ^ 2 * (1 / x ^ 3) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      dsimp only
      rw [endpointStepCell_floor n hx]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_inv_cube_endpointStepCell]
      ring

/-- Exact complete continuous endpoint energy: every infinite cell is retained. -/
theorem complexPhysicalStep_endpoint_energy (f : ThresholdHilbert) :
    WeightedMellin.energy (complexPhysicalStep f) 2 = exactEndpointCellEnergy f := by
  have hi : IntegrableOn (fun x : ℝ => hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 3)
      (Ioi 1) := by
    apply (complexPhysicalStep_endpoint_finiteEnergy f).2.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact complexPhysicalStep_endpoint_density f (lt_trans zero_lt_one hx)
  have hi' : IntegrableOn (fun x : ℝ => hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 3)
      (⋃ n, endpointStepCell n) := by
    rw [endpointStepCell_union, integrableOn_Ici_iff_integrableOn_Ioi]
    exact hi
  calc
    WeightedMellin.energy (complexPhysicalStep f) 2 =
        ∫ x in Ioi (1 : ℝ), hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 3 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact complexPhysicalStep_endpoint_density f (lt_trans zero_lt_one hx)
    _ = ∑' n, exactEndpointCellWeight (n + 1) *
        hilbertSequence f (n + 1) ^ 2 := by
      rw [← integral_Ici_eq_integral_Ioi, ← endpointStepCell_union,
        integral_iUnion (s := endpointStepCell) (fun _ => measurableSet_Ico)
          endpointStepCell_disjoint hi']
      simp_rw [integral_endpoint_density_cell]
    _ = exactEndpointCellEnergy f := by
      unfold exactEndpointCellEnergy
      rw [(exactEndpointCellEnergy_summable f).tsum_eq_zero_add]
      simp [exactEndpointCellWeight]

/-- Actual analyticity, line L2 membership, and uniform line-energy bound. -/
theorem paretoMellin_hardy_endpoint (f : ThresholdHilbert) :
    WeightedMellin.HardyH2 (paretoMellin f) 1 := by
  have hh := WeightedMellin.energy_to_hardy (complexPhysicalStep_endpoint_finiteEnergy f)
  simpa only [complexPhysicalStep_transform, show (2 : ℝ) / 2 = 1 by norm_num] using hh

/-- Exact Hardy norm identity, not a supplied Plancherel hypothesis. -/
theorem paretoMellin_hardy_endpoint_isLUB (f : ThresholdHilbert) :
    IsLUB {v : ℝ | ∃ σ : ℝ, 1 < σ ∧
      v = ∫ w : ℝ, ‖paretoMellin f (WeightedMellin.verticalPoint σ w)‖ ^ 2}
      (exactEndpointCellEnergy f) := by
  have hh := WeightedMellin.hardy_energy_isLUB
    (complexPhysicalStep_endpoint_finiteEnergy f)
  simpa only [complexPhysicalStep_transform, complexPhysicalStep_endpoint_energy,
    show (2 : ℝ) / 2 = 1 by norm_num] using hh

/-- Exact cell-energy convergence implies actual uniform Hardy-norm convergence. -/
theorem paretoMellin_hardy_endpoint_tendsto_of_cellEnergy
    (f : ℕ → ThresholdHilbert)
    (ht : Tendsto (fun N => exactEndpointCellEnergy (f N)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ, 1 < σ →
      (∫ w : ℝ, ‖paretoMellin (f N)
        (WeightedMellin.verticalPoint σ w)‖ ^ 2) < ε := by
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with N hN
  intro σ hσ
  exact lt_of_le_of_lt
    ((paretoMellin_hardy_endpoint_isLUB _).1 ⟨σ, hσ, rfl⟩) hN

/-- The corrected residual converges in the actual half-plane Hardy norm. -/
theorem canonicalMobiusResidual_hardy_endpoint :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ, 1 < σ →
      (∫ w : ℝ, ‖paretoMellin (hilbertOne - canonicalMobiusHilbert N)
        (WeightedMellin.verticalPoint σ w)‖ ^ 2) < ε :=
  paretoMellin_hardy_endpoint_tendsto_of_cellEnergy _
    canonicalMobiusResidual_exactEndpointCellEnergy_tendsto_zero

end RiemannResearch.RH.Pareto
