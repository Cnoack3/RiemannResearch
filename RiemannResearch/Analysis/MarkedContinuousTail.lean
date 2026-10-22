import RiemannResearch.Analysis.MarkedFourierTail
import RiemannResearch.Analysis.TentFourierInversion
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Literal integral marked Fourier tails

The actual continuum frequency integral is partitioned into disjoint half-open
unit intervals. The sole quantitative provider hypothesis is the unit-window
integral bound on the marked function. Absolute convergence is proved from it.
-/

noncomputable section
open MeasureTheory

namespace RiemannResearch.Analysis.MarkedContinuousTail

open MarkedFourierTail TentFourierInversion

def positiveWindow (B : ℝ) (n : ℕ) : Set ℝ :=
  Set.Ico (B + (n : ℝ)) (B + (n : ℝ) + 1)

theorem positiveWindow_iUnion (B : ℝ) : (⋃ n : ℕ, positiveWindow B n) = Set.Ici B := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact le_trans (by linarith) hn.1
  · intro hx
    have hx0 : 0 ≤ x - B := sub_nonneg.mpr hx
    apply Set.mem_iUnion.mpr
    refine ⟨⌊x - B⌋₊, ?_⟩
    change B + (⌊x - B⌋₊ : ℝ) ≤ x ∧ x < B + (⌊x - B⌋₊ : ℝ) + 1
    constructor
    · linarith [Nat.floor_le hx0]
    · linarith [Nat.lt_floor_add_one (x - B)]

theorem positiveWindow_pairwise (B : ℝ) :
    Pairwise (fun m n : ℕ => Disjoint (positiveWindow B m) (positiveWindow B n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro x hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [hm.2, hn.1]
  · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [hn.2, hm.1]

theorem integral_Ico_eq_interval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Ico a b, f x) = ∫ x in a..b, f x := by
  rw [← integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

theorem tentTransform_neg (v x : ℝ) : tentTransform v (-x) = tentTransform v x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [tentTransform, tentTransform, if_neg (neg_ne_zero.mpr hx), if_neg hx]
    rw [show Real.pi * v * -x = -(Real.pi * v * x) by ring,
      show Real.pi * -x = -(Real.pi * x) by ring, Real.sin_neg, neg_div_neg_eq]

/-- The inverse-square envelope can be frozen at the left endpoint of a
positive unit interval without removing either boundary contribution. -/
theorem tentTransform_le_window_envelope (v : ℝ) {B : ℝ} (hB : 1 ≤ B)
    (n : ℕ) {x : ℝ} (hx : x ∈ positiveWindow B n) :
    tentTransform v x ≤ 1 / (Real.pi ^ 2 * (B + (n : ℝ)) ^ 2) := by
  have hB0 : 0 < B := by linarith
  have hd : 0 < B + (n : ℝ) := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le hd hx.1
  have hsq : (B + (n : ℝ)) ^ 2 ≤ x ^ 2 :=
    (sq_le_sq₀ (le_of_lt hd) (le_of_lt hx0)).2 hx.1
  calc
    _ ≤ 1 / (Real.pi ^ 2 * x ^ 2) := tentTransform_le_inverse_square v (ne_of_gt hx0)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))

/-- A literal positive-half-line bound, together with proved absolute
integrability. The `C` hypothesis is a genuine integral spectral-window budget. -/
theorem positive_tail_integrable_and_le (f : ℝ → ℂ) (hf : Continuous f)
    (v : ℝ) {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hwindow : ∀ a : ℝ, (∫ x in Set.Ico a (a + 1), ‖f x‖) ≤ C) :
    IntegrableOn (fun x => tentTransform v x * ‖f x‖) (Set.Ici B) ∧
      (∫ x in Set.Ici B, tentTransform v x * ‖f x‖) ≤
        2 * C / (Real.pi ^ 2 * B) := by
  let g : ℝ → ℝ := fun x => tentTransform v x * ‖f x‖
  let c : ℝ := C / Real.pi ^ 2
  have hB0 : 0 < B := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hg0 (x : ℝ) : 0 ≤ g x :=
    mul_nonneg (tentTransform_nonneg v x) (norm_nonneg _)
  have hgm : AEStronglyMeasurable g volume := by
    dsimp [g]
    exact ((tentTransform_measurable v).mul hf.norm.measurable).aestronglyMeasurable
  have hl (n : ℕ) : IntegrableOn (fun x => ‖f x‖) (positiveWindow B n) :=
    hf.norm.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hpt (n : ℕ) (x : ℝ) (hx : x ∈ positiveWindow B n) :
      g x ≤ (1 / (Real.pi ^ 2 * (B + (n : ℝ)) ^ 2)) * ‖f x‖ :=
    mul_le_mul_of_nonneg_right (tentTransform_le_window_envelope v hB n hx) (norm_nonneg _)
  have hgi (n : ℕ) : IntegrableOn g (positiveWindow B n) := by
    apply ((hl n).const_mul (1 / (Real.pi ^ 2 * (B + (n : ℝ)) ^ 2))).mono'
      hgm.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    exact hpt n x hx
  have hw (n : ℕ) : (∫ x in positiveWindow B n, g x) ≤ c / (B + (n : ℝ)) ^ 2 := by
    calc
      _ ≤ ∫ x in positiveWindow B n,
          (1 / (Real.pi ^ 2 * (B + (n : ℝ)) ^ 2)) * ‖f x‖ :=
        setIntegral_mono_on (hgi n)
          ((hl n).const_mul _) measurableSet_Ico (hpt n)
      _ = (1 / (Real.pi ^ 2 * (B + (n : ℝ)) ^ 2)) *
          (∫ x in positiveWindow B n, ‖f x‖) := integral_const_mul _ _
      _ ≤ (1 / (Real.pi ^ 2 * (B + (n : ℝ)) ^ 2)) * C :=
        mul_le_mul_of_nonneg_left (hwindow _) (by positivity)
      _ = _ := by
        dsimp [c]
        simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
        ring
  let mass : ℕ → ℝ := fun n => (∫ x in positiveWindow B n, g x) * (B + (n : ℝ)) ^ 2
  have hm0 (n : ℕ) : 0 ≤ mass n :=
    mul_nonneg (integral_nonneg (fun x => hg0 x)) (sq_nonneg _)
  have hm (n : ℕ) : mass n ≤ c := by
    dsimp [mass]
    have hd : 0 < (B + (n : ℝ)) ^ 2 := by positivity
    exact (le_div_iff₀ hd).mp (hw n)
  have heq (n : ℕ) : mass n / (B + (n : ℝ)) ^ 2 = ∫ x in positiveWindow B n, g x := by
    dsimp [mass]
    have hd : B + (n : ℝ) ≠ 0 := by positivity
    field_simp [hd]
  have hs : Summable (fun n => ∫ x in positiveWindow B n, g x) := by
    simpa only [heq] using summable_window_tail mass hB hc hm0 hm
  have hsn : Summable (fun n => ∫ x in positiveWindow B n, ‖g x‖) := by
    have heNorm : (fun x => ‖g x‖) = g := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    simpa only [heNorm] using hs
  have hiU := integrableOn_iUnion_of_summable_integral_norm hgi hsn
  have hi : IntegrableOn g (Set.Ici B) := by
    simpa only [positiveWindow_iUnion] using hiU
  refine ⟨hi, ?_⟩
  change (∫ x in Set.Ici B, g x) ≤ _
  rw [← positiveWindow_iUnion B]
  rw [integral_iUnion (s := positiveWindow B)
    (fun n => show MeasurableSet (positiveWindow B n) from measurableSet_Ico)
    (positiveWindow_pairwise B) hiU]
  calc
    _ = ∑' n, mass n / (B + (n : ℝ)) ^ 2 := by simp only [heq]
    _ ≤ 2 * c / B := window_tsum_tail_le mass hB hc hm0 hm
    _ = _ := by
      dsimp [c]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem reflected_window_bound (f : ℝ → ℂ) {C : ℝ}
    (hwindow : ∀ a : ℝ, (∫ x in Set.Ico a (a + 1), ‖f x‖) ≤ C) :
    ∀ a : ℝ, (∫ x in Set.Ico a (a + 1), ‖f (-x)‖) ≤ C := by
  intro a
  rw [integral_Ico_eq_interval _ (by linarith : a ≤ a + 1)]
  rw [intervalIntegral.integral_comp_neg (fun x : ℝ => ‖f x‖)]
  have h := hwindow (-(a + 1))
  rw [integral_Ico_eq_interval _ (by linarith : -(a + 1) ≤ -(a + 1) + 1)] at h
  convert h using 1 <;> ring

/-- The full literal frequency tail, preserving the `|x| = B` endpoints.
The bound is uniform in the tent width `v`. -/
theorem two_sided_tail_integrable_and_le (f : ℝ → ℂ) (hf : Continuous f)
    (v : ℝ) {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hwindow : ∀ a : ℝ, (∫ x in Set.Ico a (a + 1), ‖f x‖) ≤ C) :
    IntegrableOn (fun x => tentTransform v x * ‖f x‖) {x : ℝ | B ≤ |x|} ∧
      (∫ x in {x : ℝ | B ≤ |x|}, tentTransform v x * ‖f x‖) ≤
        4 * C / (Real.pi ^ 2 * B) := by
  let g : ℝ → ℝ := fun x => tentTransform v x * ‖f x‖
  have hp := positive_tail_integrable_and_le f hf v hB hC hwindow
  have hn := positive_tail_integrable_and_le (fun x => f (-x))
    (hf.comp continuous_neg) v hB hC (reflected_window_bound f hwindow)
  have href : (fun x => tentTransform v x * ‖f (-x)‖) = (fun x => g (-x)) := by
    funext x
    dsimp [g]
    rw [tentTransform_neg]
  rw [href] at hn
  have hiN : IntegrableOn g (Set.Iic (-B)) := by
    have hi : IntegrableOn (fun x => g (-x)) (Set.Ici (-(-B))) := by
      simpa only [neg_neg] using hn.1
    have h := hi.comp_neg_Iic
    simpa only [neg_neg] using h
  have hN : (∫ x in Set.Iic (-B), g x) ≤ 2 * C / (Real.pi ^ 2 * B) := by
    rw [integral_Ici_eq_integral_Ioi, integral_comp_neg_Ioi] at hn
    exact hn.2
  have hset : {x : ℝ | B ≤ |x|} = Set.Ici B ∪ Set.Iic (-B) := by
    ext x
    change (B ≤ |x|) ↔ (B ≤ x ∨ x ≤ -B)
    rw [le_abs']
    exact or_comm
  have hd : Disjoint (Set.Ici B) (Set.Iic (-B)) :=
    Set.Ici_disjoint_Iic.mpr (by linarith)
  rw [hset]
  refine ⟨hp.1.union hiN, ?_⟩
  rw [setIntegral_union hd measurableSet_Iic hp.1 hiN]
  calc
    _ ≤ 2 * C / (Real.pi ^ 2 * B) + 2 * C / (Real.pi ^ 2 * B) := add_le_add hp.2 hN
    _ = _ := by ring

end RiemannResearch.Analysis.MarkedContinuousTail
