import RiemannResearch.Analysis.WeightedCoordinateEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Compact weighted observation maps with exact full tail energies

Source: independently assembled standard finite-rank approximation argument,
using Mathlib's `isCompactOperator_of_tendsto`. The weighted squared operator
norm moment is the only summability assumption, and the index type is arbitrary.
The actual Pareto/Q consumers use their complete conductor observation families.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.CompactObservationMap
open WeightedCoordinateEnergy

variable {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

abbrev CoordinateHilbert (ι : Type*) := lp (fun _ : ι => ℝ) 2

theorem coordinateHilbert_norm_sq (v : CoordinateHilbert ι) :
    ‖v‖ ^ 2 = ∑' j, (v j) ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v

/-- Square-root weighted coordinates, with no truncation of the infinite array. -/
def coordinateVector (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (x : H) : CoordinateHilbert ι :=
  ⟨fun j => Real.sqrt (w j) * ℓ j x, by
    apply memℓp_gen
    have he (j : ι) : (Real.sqrt (w j) * ℓ j x) ^ 2 =
        w j * (ℓ j x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hw j)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      sq_abs, he] using observation_summable w ℓ hw hs x⟩

@[simp] theorem coordinateVector_apply (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) (j : ι) :
    coordinateVector w ℓ hw hs x j = Real.sqrt (w j) * ℓ j x := rfl

/-- Its complete norm is precisely the complete observation energy. -/
theorem coordinateVector_norm_sq (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    ‖coordinateVector w ℓ hw hs x‖ ^ 2 = observationEnergy w ℓ x := by
  rw [coordinateHilbert_norm_sq]
  unfold observationEnergy
  apply tsum_congr
  intro j
  simp only [coordinateVector_apply, mul_pow, Real.sq_sqrt (hw j)]

def coordinateLinear (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) :
    H →ₗ[ℝ] CoordinateHilbert ι where
  toFun := coordinateVector w ℓ hw hs
  map_add' x y := by
    ext j
    change Real.sqrt (w j) * ℓ j (x + y) =
      Real.sqrt (w j) * ℓ j x + Real.sqrt (w j) * ℓ j y
    rw [map_add, mul_add]
  map_smul' c x := by
    ext j
    change Real.sqrt (w j) * ℓ j (c • x) = c * (Real.sqrt (w j) * ℓ j x)
    rw [map_smul]
    simp only [smul_eq_mul]
    ring

theorem coordinateVector_norm_le (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    ‖coordinateVector w ℓ hw hs x‖ ≤ Real.sqrt (observationMass w ℓ) * ‖x‖ := by
  have hm : 0 ≤ observationMass w ℓ := tsum_nonneg (fun j => mul_nonneg (hw j) (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hm, coordinateVector_norm_sq]
  exact observationEnergy_le w ℓ hw hs x

/-- The actual weighted observation operator into a complete Hilbert space. -/
def coordinateMap (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) :
    H →L[ℝ] CoordinateHilbert ι :=
  (coordinateLinear w ℓ hw hs).mkContinuous (Real.sqrt (observationMass w ℓ))
    (coordinateVector_norm_le w ℓ hw hs)

@[simp] theorem coordinateMap_apply (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) (j : ι) :
    coordinateMap w ℓ hw hs x j = Real.sqrt (w j) * ℓ j x := rfl

theorem coordinateMap_norm_sq (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    ‖coordinateMap w ℓ hw hs x‖ ^ 2 = observationEnergy w ℓ x :=
  coordinateVector_norm_sq w ℓ hw hs x

variable [DecidableEq ι]

/-- A finite sum of explicit rank-one operators. -/
def finiteMap (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (s : Finset ι) :
    H →L[ℝ] CoordinateHilbert ι :=
  ∑ j ∈ s, (lp.singleContinuousLinearMap ℝ (fun _ : ι => ℝ) 2 j).comp
    (Real.sqrt (w j) • ℓ j)

theorem finiteMap_apply (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (s : Finset ι) (x : H) (j : ι) :
    finiteMap w ℓ s x j = if j ∈ s then Real.sqrt (w j) * ℓ j x else 0 := by
  simp only [finiteMap, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, lp.singleContinuousLinearMap_apply, smul_eq_mul]
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp [lp.single_apply, Pi.single_apply, eq_comm]

/-- Exact identity: the full omitted-coordinate energy is the operator error. -/
theorem finiteMap_error_sq (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (s : Finset ι) (x : H) :
    ‖coordinateMap w ℓ hw hs x - finiteMap w ℓ s x‖ ^ 2 =
      ∑' j : {j : ι // j ∉ s}, w j * (ℓ j x) ^ 2 := by
  calc
    ‖coordinateMap w ℓ hw hs x - finiteMap w ℓ s x‖ ^ 2 =
        ∑' j, (coordinateMap w ℓ hw hs x j - finiteMap w ℓ s x j) ^ 2 :=
      coordinateHilbert_norm_sq (coordinateMap w ℓ hw hs x - finiteMap w ℓ s x)
    _ = ∑' j, ({j : ι | j ∉ s}.indicator (fun j => w j * (ℓ j x) ^ 2)) j := by
      apply tsum_congr
      intro j
      rw [coordinateMap_apply, finiteMap_apply]
      by_cases hj : j ∈ s
      · simp [Set.indicator, hj]
      · simp [Set.indicator, hj, mul_pow, Real.sq_sqrt (hw j)]
    _ = ∑' j : {j : ι // j ∉ s}, w j * (ℓ j x) ^ 2 :=
      (tsum_subtype {j : ι | j ∉ s} (fun j => w j * (ℓ j x) ^ 2)).symm

theorem finiteMap_error_completion (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (s : Finset ι) (x : H) :
    observationEnergy w ℓ x = (∑ j ∈ s, w j * (ℓ j x) ^ 2) +
      ‖coordinateMap w ℓ hw hs x - finiteMap w ℓ s x‖ ^ 2 := by
  rw [finiteMap_error_sq]
  exact ((observation_summable w ℓ hw hs x).sum_add_tsum_subtype_compl s).symm

def tailMass (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (s : Finset ι) : ℝ :=
  ∑' j : {j : ι // j ∉ s}, w j * ‖ℓ j‖ ^ 2

theorem tailMass_nonneg (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (s : Finset ι) : 0 ≤ tailMass w ℓ s :=
  tsum_nonneg (fun j => mul_nonneg (hw j) (sq_nonneg _))

theorem finiteMap_error_sq_le (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (s : Finset ι) (x : H) :
    ‖coordinateMap w ℓ hw hs x - finiteMap w ℓ s x‖ ^ 2 ≤ tailMass w ℓ s * ‖x‖ ^ 2 := by
  rw [finiteMap_error_sq]
  exact observationEnergy_le (fun j : {j : ι // j ∉ s} => w j)
    (fun j => ℓ j) (fun j => hw j) (hs.subtype _) x

/-- Uniform finite-rank approximation in the complete operator norm. -/
theorem finiteMap_opNorm_error_le (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (s : Finset ι) :
    ‖coordinateMap w ℓ hw hs - finiteMap w ℓ s‖ ≤ Real.sqrt (tailMass w ℓ s) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (tailMass_nonneg w ℓ hw s)]
  exact finiteMap_error_sq_le w ℓ hw hs s x

theorem tailMass_tendsto_zero (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) :
    Tendsto (tailMass w ℓ) atTop (𝓝 0) := by
  have hsum : Tendsto (fun s : Finset ι => ∑ j ∈ s, w j * ‖ℓ j‖ ^ 2)
      atTop (𝓝 (observationMass w ℓ)) := hs.hasSum
  have he (s : Finset ι) : tailMass w ℓ s =
      observationMass w ℓ - ∑ j ∈ s, w j * ‖ℓ j‖ ^ 2 := by
    have h := hs.sum_add_tsum_subtype_compl s
    change _ + tailMass w ℓ s = observationMass w ℓ at h
    linarith
  have ht : Tendsto (fun s : Finset ι => observationMass w ℓ -
      ∑ j ∈ s, w j * ‖ℓ j‖ ^ 2) atTop (𝓝 (observationMass w ℓ - observationMass w ℓ)) :=
    tendsto_const_nhds.sub hsum
  simpa only [← he, sub_self] using ht

theorem finiteMap_tendsto (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) :
    Tendsto (finiteMap w ℓ) atTop (𝓝 (coordinateMap w ℓ hw hs)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun s => Real.sqrt (tailMass w ℓ s)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp
      (tailMass_tendsto_zero w ℓ hs)
  apply squeeze_zero (fun s => norm_nonneg _) _ ht
  intro s
  rw [norm_sub_rev]
  exact finiteMap_opNorm_error_le w ℓ hw hs s

theorem finiteMap_isCompactOperator (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (s : Finset ι) :
    IsCompactOperator (finiteMap w ℓ s) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [finiteMap, Finset.sum_empty]
    change IsCompactOperator (0 : H → CoordinateHilbert ι)
    exact isCompactOperator_zero
  | @insert j s hj ih =>
    have hr : IsCompactOperator ((lp.singleContinuousLinearMap ℝ (fun _ : ι => ℝ) 2 j).comp
        (Real.sqrt (w j) • ℓ j)) :=
      (isCompactOperator_of_locallyCompactSpace_rng
        (lp.singleContinuousLinearMap ℝ (fun _ : ι => ℝ) 2 j)).comp_clm _
    rw [finiteMap, Finset.sum_insert hj]
    change IsCompactOperator (fun x =>
      ((lp.singleContinuousLinearMap ℝ (fun _ : ι => ℝ) 2 j).comp
        (Real.sqrt (w j) • ℓ j)) x + finiteMap w ℓ s x)
    exact hr.add ih

omit [DecidableEq ι] in
/-- Summable weighted squared observation norms produce a compact operator,
without countability, completeness of the source, or positivity of every weight. -/
theorem coordinateMap_isCompactOperator (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) :
    IsCompactOperator (coordinateMap w ℓ hw hs) := by
  classical
  exact isCompactOperator_of_tendsto (finiteMap_tendsto w ℓ hw hs)
    (Eventually.of_forall (finiteMap_isCompactOperator w ℓ))

omit [DecidableEq ι] in
/-- The exact kernel records precisely the support of the weights. -/
theorem coordinateMap_eq_zero_iff (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    coordinateMap w ℓ hw hs x = 0 ↔ ∀ j, w j = 0 ∨ ℓ j x = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff, coordinateMap_norm_sq]
  exact observationEnergy_eq_zero_iff_supported w ℓ hw hs x

omit [DecidableEq ι] in
theorem coordinateMap_injective (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 < w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (hsep : ∀ x : H, (∀ j, ℓ j x = 0) → x = 0) :
    Function.Injective (coordinateMap w ℓ (fun j => (hw j).le) hs) := by
  intro x y hxy
  have hz : coordinateMap w ℓ (fun j => (hw j).le) hs (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hc := (coordinateMap_eq_zero_iff w ℓ (fun j => (hw j).le) hs (x - y)).mp hz
  exact sub_eq_zero.mp (hsep (x - y) (fun j => (hc j).resolve_left (hw j).ne'))

end RiemannResearch.Analysis.CompactObservationMap
