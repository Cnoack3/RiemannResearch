import Mathlib.Analysis.Complex.Circle
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Backward ratios on the countable circle torus

Write the input as x₀,x₁,… and retain x₀ if an invertible map is wanted.
The formula for the inverse on angular lifts is a cumulative difference,
with absolute determinant one on every finite prefix. Product Haar is
characterized using translation invariance and normalization. Source for
the application: Compact Orbit, three-prime gap tests and diagonal Parseval.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.RatioChainHaar

scoped instance circleBorel : MeasurableSpace Circle := borel Circle
scoped instance : BorelSpace Circle := ⟨rfl⟩

abbrev Chain := ℕ → Circle

def ratios : Chain →* Chain where
  toFun x k := x k / x (k+1)
  map_one' := by ext k; simp
  map_mul' x y := by ext k; simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]

theorem continuous_ratios : Continuous ratios :=
  continuous_pi fun k => (continuous_apply k).div' (continuous_apply (k+1))

def reconstruct (a : Circle) (y : Chain) : Chain
  | 0 => a
  | k+1 => reconstruct a y k / y k

theorem ratios_reconstruct (a : Circle) (y : Chain) : ratios (reconstruct a y) = y := by
  funext k
  change reconstruct a y k / (reconstruct a y k / y k) = y k
  exact div_div_cancel _ _

theorem reconstruct_ratios (x : Chain) : reconstruct (x 0) (ratios x) = x := by
  funext k
  induction k with
  | zero => rfl
  | succ k hk =>
    change reconstruct (x 0) (ratios x) k / (x k / x (k+1)) = x (k+1)
    rw [hk, div_div_cancel]

theorem ratios_surjective : Function.Surjective ratios :=
  fun y => ⟨reconstruct 1 y, ratios_reconstruct 1 y⟩

theorem ratios_eq_iff_common_factor (x z : Chain) :
    ratios x = ratios z ↔ ∃ a : Circle, ∀ k, z k = a * x k := by
  constructor
  · intro h
    refine ⟨z 0 / x 0, fun k => ?_⟩
    induction k with
    | zero => exact (div_mul_cancel _ _).symm
    | succ k hk =>
      have he := congrFun h k
      change x k / x (k+1) = z k / z (k+1) at he
      rw [hk] at he
      have hc := (div_eq_div_iff_mul_eq_mul).mp he
      apply mul_left_cancel (a := x k)
      calc
        x k * z (k+1) = (z 0 / x 0 * x k) * x (k+1) := hc
        _ = x k * (z 0 / x 0 * x (k+1)) := by ac_rfl
  · rintro ⟨a, h⟩
    funext k
    change x k / x (k+1) = z k / z (k+1)
    rw [h k, h (k+1)]
    simp

/-- Retain the original phase in coordinate zero and store the backward
ratios in coordinates 1,2,…. -/
def anchoredRatios : Chain →* Chain where
  toFun x := fun n => Nat.casesOn n (x 0) (fun k => ratios x k)
  map_one' := by funext n; cases n <;> simp
  map_mul' x y := by funext n; cases n <;> simp

theorem continuous_anchoredRatios : Continuous anchoredRatios := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_apply 0
  | succ k => exact (continuous_apply k).comp continuous_ratios

theorem anchoredRatios_bijective : Function.Bijective anchoredRatios := by
  constructor
  · intro x y h
    have h0 : x 0 = y 0 := congrFun h 0
    have hr : ratios x = ratios y := funext fun k => congrFun h (k+1)
    calc
      x = reconstruct (x 0) (ratios x) := (reconstruct_ratios x).symm
      _ = reconstruct (y 0) (ratios y) := by rw [h0, hr]
      _ = y := reconstruct_ratios y
  · intro y
    let u : Chain := fun k => y (k+1)
    refine ⟨reconstruct (y 0) u, ?_⟩
    funext n
    cases n with
    | zero => rfl
    | succ k => exact congrFun (ratios_reconstruct (y 0) u) k

/-- The square angular coordinate change on m+1 coordinates. -/
def angleJacobian (m : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) ℤ := fun i j =>
  if i = j then (if i.val = 0 then 1 else -1)
  else if j.val + 1 = i.val then 1 else 0

theorem angleJacobian_det (m : ℕ) : (angleJacobian m).det = (-1 : ℤ)^m := by
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp [angleJacobian]
  · intro i j hij
    change i < j at hij
    have hv : i.val < j.val := hij
    simp [angleJacobian, ne_of_lt hij, show j.val+1 ≠ i.val by omega]

/-- The inverse angular map (θ₀,δ₀,δ₁,…) ↦ (θ₀,θ₀−δ₀,θ₀−δ₀−δ₁,…). -/
def inverseAngleJacobian (m : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) ℤ := fun i j =>
  if j.val = 0 then 1 else if j ≤ i then -1 else 0

private theorem angleJacobian_zero_row (m : ℕ) (j : Fin (m+1)) :
    angleJacobian m 0 j = if j = 0 then 1 else 0 := by
  by_cases h : j = 0
  · subst j; simp [angleJacobian]
  · simp [angleJacobian, h, Ne.symm h]

private theorem angleJacobian_succ_row (m : ℕ) (i : Fin m) (j : Fin (m+1)) :
    angleJacobian m i.succ j = (if j = i.castSucc then 1 else 0) -
      (if j = i.succ then 1 else 0) := by
  have h01 : i.succ ≠ i.castSucc := by intro h; have hv := congrArg Fin.val h; simp at hv
  by_cases h : j = i.succ
  · subst j; simp [angleJacobian, h01]
  · simp [angleJacobian, h, Ne.symm h]
    simp [Fin.ext_iff]

/-- The finite angular matrices compose to the identity over the integers. -/
theorem angleJacobian_mul_inverse (m : ℕ) :
    angleJacobian m * inverseAngleJacobian m = 1 := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [Matrix.mul_apply]
    simp_rw [angleJacobian_zero_row, ite_mul, one_mul, zero_mul]
    by_cases h : j = 0 <;> simp [inverseAngleJacobian, Matrix.one_apply, eq_comm, h]
  · rw [Matrix.mul_apply]
    simp_rw [angleJacobian_succ_row, sub_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Matrix.one_apply]
    simp only [inverseAngleJacobian, Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ,
      Fin.ext_iff]
    split_ifs <;> omega

theorem inverseAngleJacobian_det (m : ℕ) : (inverseAngleJacobian m).det = (-1 : ℤ)^m := by
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp [inverseAngleJacobian]
  · intro i j hij
    change i < j at hij
    have hv : i.val < j.val := hij
    have h0 : j.val ≠ 0 := by omega
    simp [inverseAngleJacobian, h0, not_le.mpr hij]

theorem inverseAngleJacobian_abs_det (m : ℕ) : |(inverseAngleJacobian m).det| = 1 := by
  rw [inverseAngleJacobian_det, abs_pow]
  simp

private def unitCompact (G : Type*) [TopologicalSpace G] [CompactSpace G] [Nonempty G] :
    PositiveCompacts G := ⟨⟨univ, isCompact_univ⟩, by simp⟩

def circleHaar : Measure Circle := Measure.haarMeasure (unitCompact Circle)

instance : IsProbabilityMeasure circleHaar :=
  ⟨Measure.haarMeasure_self⟩

instance : Measure.IsMulLeftInvariant circleHaar := by
  unfold circleHaar
  infer_instance

def productHaar : Measure Chain := Measure.infinitePi fun _ : ℕ => circleHaar

instance : IsProbabilityMeasure productHaar := by unfold productHaar; infer_instance

instance : Measure.IsMulLeftInvariant productHaar := by
  constructor
  intro y
  change (Measure.infinitePi (fun _ : ℕ => circleHaar)).map
    (fun x k => y k * x k) = Measure.infinitePi (fun _ : ℕ => circleHaar)
  rw [Measure.infinitePi_map_pi _ (fun k => measurable_const_mul (y k))]
  simp only [map_mul_left_eq_self]

/-- Any surjective continuous group map from an invariant probability to this
torus has the countable product of uniform circle laws as its pushforward. -/
theorem map_eq_productHaar {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    [Measure.IsMulLeftInvariant μ] (f : G →* Chain) (hf : Continuous f)
    (hs : Function.Surjective f) : μ.map f = productHaar := by
  have : IsProbabilityMeasure (μ.map f) := μ.isProbabilityMeasure_map hf.measurable.aemeasurable
  have : Measure.IsMulLeftInvariant (μ.map f) :=
    isMulLeftInvariant_map (μ := μ) f.toMulHom hf.measurable hs
  have h (ν : Measure Chain) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν] :
      Measure.haarMeasure (unitCompact Chain) = ν :=
    (Measure.haarMeasure_eq_iff _ _).2 (measure_univ : ν univ = 1)
  exact (h _).symm.trans (h _)

theorem ratios_map_productHaar : productHaar.map ratios = productHaar :=
  map_eq_productHaar productHaar ratios continuous_ratios ratios_surjective

/-- The anchor and all backward ratios together also have product Haar law. -/
theorem anchoredRatios_map_productHaar : productHaar.map anchoredRatios = productHaar :=
  map_eq_productHaar productHaar anchoredRatios continuous_anchoredRatios
    anchoredRatios_bijective.surjective

theorem coordinate_map (k : ℕ) : productHaar.map (fun x => x k) = circleHaar :=
  Measure.infinitePi_map_eval (fun _ : ℕ => circleHaar) k

theorem independent_coordinates : iIndepFun (fun k (x : Chain) => x k) productHaar := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun k => measurable_pi_apply k)]
  simp only [coordinate_map]
  exact Measure.map_id

end RiemannResearch.Analysis.RatioChainHaar
