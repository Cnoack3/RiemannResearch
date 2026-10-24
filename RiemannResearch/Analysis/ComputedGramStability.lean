import RiemannResearch.Analysis.FiniteGramBackwardError
import RiemannResearch.Analysis.FiniteGramMetricComparison
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified computation of complete Gram defects

Source: user-requested fifth Ramanujan transfer program, 24 October 2026.
These are standard finite-dimensional perturbation and duality arguments.
The exact source and metric identity precedes every estimate. Computed
errors are measured in an actual independent computed dictionary Gram.
A relative bilinear form certificate is an explicit numerical hypothesis;
it is not an RH, density, or arithmetic saturation assertion.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ComputedGramStability
open FiniteHilbertGram FiniteGramCapacity FiniteHilbertConstraints FiniteGramBackwardError

variable {ι H K : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

def gramGapSource (v : ι → H) (w : ι → K) (a : ι → ℝ) : ι → ℝ := gram v a - gram w a

def metricGap (v : ι → H) (w : ι → K) (a : ι → ℝ) : ℝ :=
  ‖Fintype.linearCombination ℝ v a‖ ^ 2 - ‖Fintype.linearCombination ℝ w a‖ ^ 2

/-- Simultaneous source and matrix resolvent identity, with their signs retained. -/
theorem inverseSource_difference_exact {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w) (b c : ι → ℝ) :
    inverseSource hv b - inverseSource hw c =
      inverseSource hv (b - c - gramGapSource v w (inverseSource hw c)) := by
  have hb : gram v (inverseSource hv b) = b := funext (inverseSource_normal hv b)
  have hc : gram w (inverseSource hw c) = c := funext (inverseSource_normal hw c)
  have hr : gram v (inverseSource hv
      (b - c - gramGapSource v w (inverseSource hw c))) =
      b - c - gramGapSource v w (inverseSource hw c) :=
    funext (inverseSource_normal hv _)
  apply gram_injective hv
  rw [map_sub, hb, hr]
  unfold gramGapSource
  rw [hc]
  abel

/-- Complete inverse-Gram identity for distinct sources and distinct metrics. -/
theorem capacity_source_metric_exact {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w) (b c : ι → ℝ) :
    capacity hv b = capacity hw c +
      2 * (∑ i, inverseSource hw c i * (b i - c i)) -
      metricGap v w (inverseSource hw c) +
      ‖Fintype.linearCombination ℝ v (inverseSource hv b - inverseSource hw c)‖ ^ 2 := by
  have h := capacity_completion hv b (inverseSource hw c)
  have hn : ‖Fintype.linearCombination ℝ w (inverseSource hw c)‖ ^ 2 = capacity hw c :=
    (capacity_eq_norm_sq hw c).symm
  have hp : (∑ i, inverseSource hw c i * b i) =
      capacity hw c + ∑ i, inverseSource hw c i * (b i - c i) := by
    unfold capacity
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hd : minimumVector hv b - Fintype.linearCombination ℝ v (inverseSource hw c) =
      Fintype.linearCombination ℝ v (inverseSource hv b - inverseSource hw c) := by
    change Fintype.linearCombination ℝ v (inverseSource hv b) -
      Fintype.linearCombination ℝ v (inverseSource hw c) = _
    exact (map_sub (Fintype.linearCombination ℝ v) _ _).symm
  rw [hp, hd] at h
  unfold metricGap
  linarith

theorem gramGapSource_pairing (v : ι → H) (w : ι → K) (a c : ι → ℝ) :
    (∑ i, c i * gramGapSource v w a i) =
      inner ℝ (Fintype.linearCombination ℝ v c) (Fintype.linearCombination ℝ v a) -
      inner ℝ (Fintype.linearCombination ℝ w c) (Fintype.linearCombination ℝ w a) := by
  rw [inner_synthesis_left, inner_synthesis_left, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change c i *
    (inner ℝ (v i) (Fintype.linearCombination ℝ v a) -
      inner ℝ (w i) (Fintype.linearCombination ℝ w a)) = _
  ring

/-- A dual quadratic certificate characterizes the inverse-Gram energy exactly. -/
theorem capacity_le_iff_dual_bound {w : ι → K} (hw : LinearIndependent ℝ w)
    (b : ι → ℝ) (η : ℝ) (hη : 0 ≤ η) :
    capacity hw b ≤ η ↔ ∀ c : ι → ℝ,
      (∑ i, c i * b i) ^ 2 ≤ η * ‖Fintype.linearCombination ℝ w c‖ ^ 2 := by
  constructor
  · intro h c
    exact (source_sq_le_capacity_mul_energy hw b c).trans
      (mul_le_mul_of_nonneg_right h (sq_nonneg _))
  · intro h
    have hn : ‖Fintype.linearCombination ℝ w (inverseSource hw b)‖ ^ 2 = capacity hw b :=
      (capacity_eq_norm_sq hw b).symm
    have hh := h (inverseSource hw b)
    change (capacity hw b) ^ 2 ≤ η *
      ‖Fintype.linearCombination ℝ w (inverseSource hw b)‖ ^ 2 at hh
    rw [hn] at hh
    by_cases hz : capacity hw b = 0
    · simpa only [hz] using hη
    · have hp : 0 < capacity hw b := lt_of_le_of_ne (capacity_nonneg hw b) (Ne.symm hz)
      nlinarith

/-- The relative certificate controls the full signed bilinear discrepancy. -/
def RelativeFormBound (v : ι → H) (w : ι → K) (ε : ℝ) : Prop :=
  ∀ a c : ι → ℝ,
    |inner ℝ (Fintype.linearCombination ℝ v a) (Fintype.linearCombination ℝ v c) -
      inner ℝ (Fintype.linearCombination ℝ w a) (Fintype.linearCombination ℝ w c)| ≤
      ε * ‖Fintype.linearCombination ℝ w a‖ * ‖Fintype.linearCombination ℝ w c‖

theorem relative_energy_bounds (v : ι → H) (w : ι → K) (ε : ℝ)
    (hrel : RelativeFormBound v w ε) (a : ι → ℝ) :
    (1 - ε) * ‖Fintype.linearCombination ℝ w a‖ ^ 2 ≤
      ‖Fintype.linearCombination ℝ v a‖ ^ 2 ∧
    ‖Fintype.linearCombination ℝ v a‖ ^ 2 ≤
      (1 + ε) * ‖Fintype.linearCombination ℝ w a‖ ^ 2 := by
  have h := hrel a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h₁ := (abs_le.mp h).1
  have h₂ := (abs_le.mp h).2
  constructor <;> nlinarith

/-- Relative form control gives a quadratic, rather than linear, action-error bound. -/
theorem gramGapSource_capacity_bound {v : ι → H} {w : ι → K}
    (hw : LinearIndependent ℝ w) (ε : ℝ) (hε : 0 ≤ ε)
    (hrel : RelativeFormBound v w ε) (a : ι → ℝ) :
    capacity hw (gramGapSource v w a) ≤ ε ^ 2 * ‖Fintype.linearCombination ℝ w a‖ ^ 2 := by
  apply (capacity_le_iff_dual_bound hw _ _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
  intro c
  rw [gramGapSource_pairing]
  have h := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (mul_nonneg hε (norm_nonneg _)) (norm_nonneg _))).mpr (hrel c a)
  simpa only [sq_abs, mul_pow, mul_assoc, mul_left_comm, mul_comm] using h

def computedResidual (w : ι → K) (b a : ι → ℝ) : ι → ℝ := gram w a - b

def computedDefectEnergy {w : ι → K} (hw : LinearIndependent ℝ w)
    (v : ι → H) (x : H) (a : ι → ℝ) : ℝ := capacity hw (normalDefect v x a)

theorem computedDefectEnergy_inverseGram [DecidableEq ι] {w : ι → K}
    (hw : LinearIndependent ℝ w) (v : ι → H) (x : H) (a : ι → ℝ) :
    computedDefectEnergy hw v x a = dotProduct (normalDefect v x a)
      ((gramMatrix w)⁻¹.mulVec (normalDefect v x a)) := by
  calc
    _ = inverseGramPairing hw (normalDefect v x a) (normalDefect v x a) := by
      simp only [computedDefectEnergy, capacity_eq_norm_sq, inverseGramPairing,
        real_inner_self_eq_norm_sq]
    _ = _ := inverseGramPairing_matrix hw _ _

theorem computed_defect_decomposition (v : ι → H) (w : ι → K)
    (x : H) (b a : ι → ℝ) :
    normalDefect v x a = computedResidual w b a + sourceError v x b + gramGapSource v w a := by
  funext i
  simp only [normalDefect, computedResidual, sourceError, gramGapSource, Pi.add_apply, Pi.sub_apply]
  ring

/-- The computable budget keeps every solver/source/Gram signed cross term. -/
theorem computedDefectEnergy_signed_budget {v : ι → H} {w : ι → K}
    (hw : LinearIndependent ℝ w) (x : H) (b a : ι → ℝ) :
    computedDefectEnergy hw v x a =
      capacity hw (computedResidual w b a) + capacity hw (sourceError v x b) +
      capacity hw (gramGapSource v w a) +
      2 * inverseGramPairing hw (computedResidual w b a) (sourceError v x b) +
      2 * inverseGramPairing hw (computedResidual w b a) (gramGapSource v w a) +
      2 * inverseGramPairing hw (sourceError v x b) (gramGapSource v w a) := by
  rw [computedDefectEnergy, computed_defect_decomposition v w x b a, capacity_three_signed]

/-- The complete computed budget and true defect are uniformly equivalent. -/
theorem computedDefectEnergy_bounds {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) (hrel : RelativeFormBound v w ε)
    (x : H) (a : ι → ℝ) :
    (1 - ε) * defectEnergy hv x a ≤ computedDefectEnergy hw v x a ∧
      computedDefectEnergy hw v x a ≤ (1 + ε) * defectEnergy hv x a := by
  have hpos : 0 < 1 - ε := by linarith
  have hupper := capacity_le_mul_of_energy_le hv hw (by linarith : 0 ≤ 1 + ε)
    (fun c => (relative_energy_bounds v w ε hrel c).2) (normalDefect v x a)
  have he : ∀ c : ι → ℝ, ‖Fintype.linearCombination ℝ w c‖ ^ 2 ≤
      (1 - ε)⁻¹ * ‖Fintype.linearCombination ℝ v c‖ ^ 2 := by
    intro c
    calc
      ‖Fintype.linearCombination ℝ w c‖ ^ 2 =
          (1 - ε)⁻¹ * ((1 - ε) * ‖Fintype.linearCombination ℝ w c‖ ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (relative_energy_bounds v w ε hrel c).1 (inv_nonneg.mpr hpos.le)
  have hbound := capacity_le_mul_of_energy_le hw hv (inv_nonneg.mpr hpos.le)
    he (normalDefect v x a)
  have hlower := mul_le_mul_of_nonneg_left hbound hpos.le
  refine ⟨?_, hupper⟩
  simpa only [defectEnergy, computedDefectEnergy, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt hpos), one_mul] using hlower

/-- A certified interval for the entire trial error, including its optimal residual. -/
theorem residual_error_computed_interval {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) (hrel : RelativeFormBound v w ε)
    (x : H) (a : ι → ℝ) :
    ‖x - Fintype.linearCombination ℝ v (inverseCoeff hv x)‖ ^ 2 +
        computedDefectEnergy hw v x a / (1 + ε) ≤
      ‖x - Fintype.linearCombination ℝ v a‖ ^ 2 ∧
    ‖x - Fintype.linearCombination ℝ v a‖ ^ 2 ≤
      ‖x - Fintype.linearCombination ℝ v (inverseCoeff hv x)‖ ^ 2 +
        computedDefectEnergy hw v x a / (1 - ε) := by
  have hb := computedDefectEnergy_bounds hv hw ε hε hε1 hrel x a
  have hplus : 0 < 1 + ε := by linarith
  have hminus : 0 < 1 - ε := by linarith
  have hlo : computedDefectEnergy hw v x a / (1 + ε) ≤ defectEnergy hv x a := by
    apply (div_le_iff₀ hplus).mpr
    simpa only [mul_comm] using hb.2
  have hhi : defectEnergy hv x a ≤ computedDefectEnergy hw v x a / (1 - ε) := by
    apply (le_div_iff₀ hminus).mpr
    simpa only [mul_comm] using hb.1
  rw [residual_error_defect_identity hv x a]
  constructor <;> linarith

/-- A posteriori bound in the computed metric, keeping source and solver cancellation together. -/
theorem defectEnergy_a_posteriori {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) (hrel : RelativeFormBound v w ε)
    (x : H) (b a : ι → ℝ) :
    defectEnergy hv x a ≤
      (‖minimumVector hw (computedResidual w b a + sourceError v x b)‖ +
        ε * ‖Fintype.linearCombination ℝ w a‖) ^ 2 / (1 - ε) := by
  have hpos : 0 < 1 - ε := by linarith
  have hg := gramGapSource_capacity_bound hw ε hε hrel a
  rw [capacity_eq_norm_sq] at hg
  have hg' : ‖minimumVector hw (gramGapSource v w a)‖ ≤
      ε * ‖Fintype.linearCombination ℝ w a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mp
    simpa only [mul_pow] using hg
  have hn : ‖minimumVector hw (normalDefect v x a)‖ ≤
      ‖minimumVector hw (computedResidual w b a + sourceError v x b)‖ +
        ε * ‖Fintype.linearCombination ℝ w a‖ := by
    rw [computed_defect_decomposition v w x b a, minimumVector_add_source]
    have hnorm := norm_add_le
      (minimumVector hw (computedResidual w b a + sourceError v x b))
      (minimumVector hw (gramGapSource v w a))
    linarith
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _)
    (mul_nonneg hε (norm_nonneg _)))).mpr hn
  have hb := (computedDefectEnergy_bounds hv hw ε hε hε1 hrel x a).1
  have hc : computedDefectEnergy hw v x a ≤
      (‖minimumVector hw (computedResidual w b a + sourceError v x b)‖ +
        ε * ‖Fintype.linearCombination ℝ w a‖) ^ 2 := by
    simpa only [computedDefectEnergy, capacity_eq_norm_sq] using hs
  apply (le_div_iff₀ hpos).mpr
  simpa only [mul_comm] using hb.trans hc

/-- Exact computed normal equations with the true source incur only quadratic metric error. -/
theorem defectEnergy_exact_computed_solve {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) (hrel : RelativeFormBound v w ε)
    (x : H) (a : ι → ℝ) (hsolve : gram w a = cross v x) :
    defectEnergy hv x a ≤ ε ^ 2 * ‖Fintype.linearCombination ℝ w a‖ ^ 2 / (1 - ε) := by
  have h := defectEnergy_a_posteriori hv hw ε hε hε1 hrel x (cross v x) a
  simpa only [computedResidual, sourceError, hsolve, sub_self, zero_add,
    minimumVector, map_zero, norm_zero, zero_add, mul_pow] using h

/-- Uniform relative certification transfers vanishing defects through moving finite dimensions. -/
theorem defectEnergy_tendsto_iff_computed
    {α : Type*} {l : Filter α} {κ : α → Type*} [∀ i, Fintype (κ i)]
    (v : ∀ i, κ i → H) (w : ∀ i, κ i → K)
    (hv : ∀ i, LinearIndependent ℝ (v i)) (hw : ∀ i, LinearIndependent ℝ (w i))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) (hrel : ∀ i, RelativeFormBound (v i) (w i) ε)
    (x : α → H) (a : ∀ i, κ i → ℝ) :
    Tendsto (fun i => defectEnergy (hv i) (x i) (a i)) l (𝓝 0) ↔
      Tendsto (fun i => computedDefectEnergy (hw i) (v i) (x i) (a i)) l (𝓝 0) := by
  have hpos : 0 < 1 - ε := by linarith
  constructor
  · intro h
    apply squeeze_zero (fun i => capacity_nonneg (hw i) _)
      (fun i => (computedDefectEnergy_bounds (hv i) (hw i) ε hε hε1 (hrel i) (x i) (a i)).2)
    simpa only [mul_zero] using h.const_mul (1 + ε)
  · intro h
    have hb : ∀ i, defectEnergy (hv i) (x i) (a i) ≤
        computedDefectEnergy (hw i) (v i) (x i) (a i) / (1 - ε) := by
      intro i
      apply (le_div_iff₀ hpos).mpr
      simpa only [mul_comm] using
        (computedDefectEnergy_bounds (hv i) (hw i) ε hε hε1 (hrel i) (x i) (a i)).1
    apply squeeze_zero (fun i => defectEnergy_nonneg (hv i) (x i) (a i)) hb
    simpa only [zero_div] using h.div_const (1 - ε)

/-- Validated source/solver cancellation and vanishing relative metric action suffice.
The computed coefficient arrays and their dimensions may vary along any filter. -/
theorem defectEnergy_tendsto_zero_of_certified_errors
    {α : Type*} {l : Filter α} {κ : α → Type*} [∀ i, Fintype (κ i)]
    (v : ∀ i, κ i → H) (w : ∀ i, κ i → K)
    (hv : ∀ i, LinearIndependent ℝ (v i)) (hw : ∀ i, LinearIndependent ℝ (w i))
    (ε : ℝ) (hε1 : ε < 1) (δ : α → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hδε : ∀ i, δ i ≤ ε) (hrel : ∀ i, RelativeFormBound (v i) (w i) (δ i))
    (x : α → H) (b a : ∀ i, κ i → ℝ)
    (herr : Tendsto (fun i => ‖minimumVector (hw i)
      (computedResidual (w i) (b i) (a i) + sourceError (v i) (x i) (b i))‖) l (𝓝 0))
    (hmetric : Tendsto (fun i => δ i * ‖Fintype.linearCombination ℝ (w i) (a i)‖)
      l (𝓝 0)) :
    Tendsto (fun i => defectEnergy (hv i) (x i) (a i)) l (𝓝 0) := by
  have hpos : 0 < 1 - ε := by linarith
  have hb : ∀ i, defectEnergy (hv i) (x i) (a i) ≤
      (‖minimumVector (hw i)
        (computedResidual (w i) (b i) (a i) + sourceError (v i) (x i) (b i))‖ +
        δ i * ‖Fintype.linearCombination ℝ (w i) (a i)‖) ^ 2 / (1 - ε) := by
    intro i
    have hi : δ i < 1 := (hδε i).trans_lt hε1
    have h := defectEnergy_a_posteriori (hv i) (hw i) (δ i) (hδ i) hi
      (hrel i) (x i) (b i) (a i)
    have hi' : 0 < 1 - δ i := by linarith
    have ht := (le_div_iff₀ hi').mp h
    have hm : defectEnergy (hv i) (x i) (a i) * (1 - ε) ≤
        defectEnergy (hv i) (x i) (a i) * (1 - δ i) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left (hδε i) 1)
        (defectEnergy_nonneg (hv i) (x i) (a i))
    exact (le_div_iff₀ hpos).mpr (hm.trans ht)
  apply squeeze_zero (fun i => defectEnergy_nonneg (hv i) (x i) (a i)) hb
  simpa only [zero_add, zero_pow (by decide : 2 ≠ 0), zero_div] using
    ((herr.add hmetric).pow 2).div_const (1 - ε)

end RiemannResearch.Analysis.ComputedGramStability
