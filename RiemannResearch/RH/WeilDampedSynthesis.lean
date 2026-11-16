import RiemannResearch.Analysis.SquareSummableSynthesis
import RiemannResearch.RH.WeilDampedWeights
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# Actual damped prime synthesis on Lebesgue L²

Source: user-provided prime-side factorization continuation, Priority 1.
The compact support assumption is only almost-everywhere support of an L²
function; smoothness is unnecessary. Coordinates are all natural numbers,
with the actual von Mangoldt weight zero off prime powers. This agrees with
prime-power coordinates after discarding the zero columns.

The shift convention is `shift a f x = f (x-a)`; hence the note's
`tau_a` is `shift (-a)`. The exact support projection is proved as an
identity of bounded operators, not merely of finite matrices.
-/

set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical
namespace RiemannResearch.RH.WeilDampedSynthesis
open RiemannResearch.Analysis.SquareSummableSynthesis
open WeilDampedWeights
abbrev L2 := MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

def shift (a : ℝ) : L2 →ₗᵢ[ℂ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x - a)
    (measurePreserving_sub_right volume a)

theorem shift_coe (a : ℝ) (f : L2) :
    shift a f =ᵐ[volume] fun x => f (x - a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume a)

theorem shift_add (a b : ℝ) (f : L2) : shift a (shift b f) = shift (a + b) f := by
  change Lp.compMeasurePreserving (fun x : ℝ => x - a) _
    (Lp.compMeasurePreserving (fun x : ℝ => x - b) _ f) =
      Lp.compMeasurePreserving (fun x : ℝ => x - (a + b)) _ f
  have hh : (fun x : ℝ => x - b) ∘ (fun x : ℝ => x - a) =
      (fun x : ℝ => x - (a + b)) := by funext x; simp only [Function.comp_apply]; ring
  have h := Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_sub_right volume b) (measurePreserving_sub_right volume a)
  simpa only [hh] using h.symm

def column (σ : ℝ) (φ : L2) (m : ℕ) : L2 :=
  (amplitude σ m : ℂ) • shift (Real.log m) φ

theorem norm_column (σ : ℝ) (φ : L2) (m : ℕ) :
    ‖column σ φ m‖ = amplitude σ m * ‖φ‖ := by
  rw [column, norm_smul, Complex.norm_real, Real.norm_of_nonneg (amplitude_nonneg σ m),
    (shift (Real.log m)).norm_map]

theorem norm_column_sq (σ : ℝ) (φ : L2) (m : ℕ) :
    ‖column σ φ m‖ ^ 2 = energy σ m * ‖φ‖ ^ 2 := by
  rw [norm_column, mul_pow, amplitude_sq]

theorem column_square_summable {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) :
    Summable (fun m => ‖column σ φ m‖ ^ 2) := by
  simp_rw [norm_column_sq]
  exact (energy_summable hσ).mul_right _

def columns {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) : lp (fun _ : ℕ => L2) 2 :=
  ⟨column σ φ, (memℓp_gen_iff (by norm_num)).2 (by
    simpa using column_square_summable hσ φ)⟩

def J {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) : Coeff ℕ →L[ℂ] L2 :=
  synthesis (columns hσ φ)

theorem J_single {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) (m : ℕ) :
    J hσ φ (lp.single 2 m 1) = column σ φ m := synthesis_single _ _

theorem J_hasSum {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) (c : Coeff ℕ) :
    HasSum (fun m => c m • column σ φ m) (J hσ φ c) := synthesis_hasSum _ _

theorem J_column_square_sum {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) :
    (∑' m, ‖J hσ φ (lp.single 2 m 1)‖ ^ 2) =
      (∑' m, energy σ m) * ‖φ‖ ^ 2 := by
  simp only [J_single, norm_column_sq]
  exact tsum_mul_right

theorem columns_norm_sq {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) :
    ‖columns hσ φ‖ ^ 2 = (∑' m, energy σ m) * ‖φ‖ ^ 2 := by
  rw [norm_sq]
  change (∑' m, ‖column σ φ m‖ ^ 2) = _
  simp_rw [norm_column_sq]
  exact tsum_mul_right

theorem column_small (σ : ℝ) (φ : L2) {m : ℕ} (hm : m < 2) :
    column σ φ m = 0 := by
  interval_cases m <;> simp [column, amplitude]

theorem shift_inner_zero {r a b : ℝ} (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) (hab : 2 * r < a - b) :
    inner ℂ (shift a φ) (shift b φ) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  have ha := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae hφ
  have hb := (measurePreserving_sub_right volume b).quasiMeasurePreserving.ae hφ
  filter_upwards [shift_coe a φ, shift_coe b φ, ha, hb] with x hxa hxb hpa hpb
  rw [hxa, hxb]
  by_cases hx : r < |x - a|
  · rw [hpa hx]
    simp
  · have hax := abs_le.mp (le_of_not_gt hx)
    have hbx : r < |x - b| := by
      by_contra hn
      have := abs_le.mp (le_of_not_gt hn)
      linarith
    rw [hpb hbx]
    simp

def tailSet (r a : ℝ) : Set ℕ := {m | 2 * Real.exp (a - 2 * r) ≤ (m : ℝ)}
def tailProjection (r a : ℝ) : Coeff ℕ →L[ℂ] Coeff ℕ :=
  projection (tailSet r a)

theorem column_inner_shift_column_zero {σ r a : ℝ} (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) {m : ℕ}
    (hm : m ∉ tailSet r a) (k : ℕ) :
    inner ℂ (column σ φ k) (shift (-a) (column σ φ m)) = 0 := by
  by_cases hk : k < 2
  · rw [column_small σ φ hk]
    simp
  by_cases hm2 : m < 2
  · rw [column_small σ φ hm2]
    simp
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hklog : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ k by omega))
  have hmlog : Real.log m < Real.log 2 + (a - 2 * r) := by
    apply (Real.log_lt_iff_lt_exp hm0).2
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact lt_of_not_ge hm
  unfold column
  rw [map_smul, inner_smul_left, inner_smul_right, shift_add]
  rw [shift_inner_zero φ hφ (by linarith : 2 * r < Real.log k - (-a + Real.log m))]
  simp

theorem support_projection_identity {σ r a : ℝ} (hσ : 1 / 2 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    ((J hσ φ).adjoint.comp ((shift (-a)).toContinuousLinearMap.comp (J hσ φ))) =
      ((J hσ φ).adjoint.comp ((shift (-a)).toContinuousLinearMap.comp (J hσ φ))).comp
        (tailProjection r a) := by
  apply ext_single
  intro m
  change (J hσ φ).adjoint (shift (-a) (J hσ φ (lp.single 2 m 1))) =
    (J hσ φ).adjoint (shift (-a) (J hσ φ (projection (tailSet r a) (lp.single 2 m 1))))
  rw [projection_single]
  by_cases hm : m ∈ tailSet r a
  · simp [hm]
  · simp only [hm, ↓reduceIte, map_zero, J_single]
    rw [J, synthesis, ContinuousLinearMap.adjoint_adjoint]
    ext k
    exact column_inner_shift_column_zero φ hφ hm k

theorem masked_columns_norm_sq {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) (Y : ℝ) :
    ‖mask {m : ℕ | Y ≤ (m : ℝ)} (columns hσ φ)‖ ^ 2 =
      tailEnergy σ Y * ‖φ‖ ^ 2 := by
  rw [norm_sq, tailEnergy, ← tsum_mul_right]
  apply tsum_congr
  intro m
  by_cases hm : Y ≤ (m : ℝ) <;>
    simp [mask_apply, Set.indicator_apply, hm, columns, norm_column_sq]

theorem masked_columns_half_exponent {σ : ℝ} (hσ : 1 < σ) (φ : L2)
    {Y : ℝ} (hY : 0 < Y) :
    ‖mask {m : ℕ | Y ≤ (m : ℝ)} (columns (by linarith : 1 / 2 < σ) φ)‖ ^ 2 ≤
      Y ^ (-σ) * ((∑' m, energy (σ / 2) m) * ‖φ‖ ^ 2) := by
  rw [masked_columns_norm_sq]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (tailEnergy_half_exponent hσ hY) (sq_nonneg ‖φ‖)
end RiemannResearch.RH.WeilDampedSynthesis
