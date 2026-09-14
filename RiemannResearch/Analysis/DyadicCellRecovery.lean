import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Recovering integer values from shrinking dyadic cells

Source: user-provided `RH_Iff_Two_Seed_Approximation_20260914.md`,
Section 4.4. This proves the quantitative recovery step for the actual
floor step functions. Ordinary L2 convergence without the stated rate
is not used to infer convergence at points.
-/

namespace RiemannResearch.Analysis
open MeasureTheory Filter
noncomputable section

def scaledFloorStep (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  a ⌊(q : ℝ) * x⌋₊

theorem scaledFloorStep_on_cell (a : ℕ → ℝ) (q n : ℕ)
    (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1 / (q : ℝ))) :
    scaledFloorStep a q x = a (q * n) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg n) hx.1
  have hfloor : ⌊(q : ℝ) * x⌋₊ = q * n := by
    apply (Nat.floor_eq_iff (mul_nonneg hqR.le hx0)).mpr
    simp only [Nat.cast_mul]
    constructor
    · exact mul_le_mul_of_nonneg_left hx.1 hqR.le
    · have hu := mul_lt_mul_of_pos_left hx.2 hqR
      have he : (q : ℝ) * (1 / (q : ℝ)) = 1 := by field_simp
      nlinarith
  exact congrArg a hfloor

theorem scaledFloorStep_cell_error (a : ℕ → ℝ) (q n : ℕ)
    (hq : 0 < q) (c : ℝ) :
    (∫ x in Set.Ico (n : ℝ) ((n : ℝ) + 1 / (q : ℝ)),
      (scaledFloorStep a q x - c)^2) = (a (q*n) - c)^2 / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ = ∫ _x in Set.Ico (n : ℝ) ((n : ℝ) + 1 / (q : ℝ)),
        (a (q*n) - c)^2 := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      change (scaledFloorStep a q x - c)^2 = (a (q*n) - c)^2
      rw [scaledFloorStep_on_cell a q n hq hx]
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ico,
        add_sub_cancel_left]
      rw [ENNReal.toReal_ofReal (by positivity)]
      simp only [smul_eq_mul]
      ring

theorem scaledFloorStep_recovery_lower_bound (a : ℕ → ℝ) (q n : ℕ)
    (hq : 0 < q) (c : ℝ)
    (hint : IntegrableOn (fun x => (scaledFloorStep a q x - c)^2)
      (Set.Ico (n : ℝ) ((n : ℝ)+1))) :
    (a (q*n) - c)^2 / (q : ℝ) ≤
      ∫ x in Set.Ico (n : ℝ) ((n : ℝ)+1), (scaledFloorStep a q x - c)^2 := by
  rw [← scaledFloorStep_cell_error a q n hq c]
  apply setIntegral_mono_set hint
  · exact Eventually.of_forall (fun x => sq_nonneg _)
  · apply Eventually.of_forall
    intro x hx
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hdiv : 1 / (q : ℝ) ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq1
    exact ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩

theorem dyadic_invariance_pow (a : ℕ → ℝ)
    (hdouble : ∀ n, 0 < n → a (2*n) = a n)
    (j n : ℕ) (hn : 0 < n) : a (2^j*n) = a n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Nat.mul_assoc,
      hdouble (2^j*n) (Nat.mul_pos (pow_pos (by norm_num) j) hn), ih]

/-- The little-o squared-error estimate on an ordinary unit interval
recovers its left integer value. The error budget tends to zero; all
integrals are the actual floor-step squared errors. -/
theorem dyadicFloorStep_recovery (a : ℕ → ℝ)
    (hdouble : ∀ n, 0 < n → a (2*n) = a n)
    (n : ℕ) (hn : 0 < n) (c C : ℝ) (E : ℕ → ℝ)
    (hE : Tendsto E atTop (nhds 0))
    (hint : ∀ j, IntegrableOn (fun x => (scaledFloorStep a (2^j) x - c)^2)
      (Set.Ico (n : ℝ) ((n : ℝ)+1)))
    (herr : ∀ j,
      (∫ x in Set.Ico (n : ℝ) ((n : ℝ)+1),
        (scaledFloorStep a (2^j) x - c)^2) ≤ C / (2 : ℝ)^j * E j) :
    a n = c := by
  have hb (j : ℕ) : (a n - c)^2 ≤ C * E j := by
    have hp : (0 : ℝ) < (2 : ℝ)^j := pow_pos (by norm_num) j
    have h := (scaledFloorStep_recovery_lower_bound a (2^j) n
      (pow_pos (by norm_num) j) c (hint j)).trans (herr j)
    rw [dyadic_invariance_pow a hdouble j n hn] at h
    simp only [Nat.cast_pow, Nat.cast_ofNat] at h
    have hm := mul_le_mul_of_nonneg_right h hp.le
    field_simp at hm
    nlinarith only [hm]
  have hlim : Tendsto (fun j => (a n-c)^2 - C * E j) atTop
      (nhds ((a n-c)^2)) := by
    simpa using (tendsto_const_nhds.sub (hE.const_mul C))
  have hz : (a n-c)^2 ≤ 0 :=
    le_of_tendsto hlim (Eventually.of_forall (fun j => sub_nonpos.mpr (hb j)))
  nlinarith [sq_nonneg (a n-c)]

end
end RiemannResearch.Analysis
