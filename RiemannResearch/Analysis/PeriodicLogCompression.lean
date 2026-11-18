import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Order of the logarithmic moment of power-law progressions

Source: C. Noack's October 2026 carry trace note. Comparing two residue
classes directly by a two-index inequality avoids differentiating in the
residue. Any increasing function of the progression index satisfies the
finite comparison. Vanishing at the zero class improves the compression
bound to the conditional mean of the last supported class.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.PeriodicLogCompression

/-- Monotone likelihood-ratio comparison for arbitrary positive finite weights. -/
theorem ordered_weighted_sums (s : Finset ℕ) (w v f : ℕ → ℝ)
    (hf : Monotone f) (ho : ∀ i j, i ≤ j → w j * v i ≤ w i * v j) :
    (∑ i ∈ s, w i * f i) * (∑ i ∈ s, v i) ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, v i * f i := by
  have hp (i j : ℕ) :
      (w i * f i) * v j + v i * (w j * f j) ≤
        w i * (v j * f j) + (v i * f i) * w j := by
    rcases le_total i j with hij | hji
    · nlinarith only [mul_nonneg (sub_nonneg.mpr (ho i j hij)) (sub_nonneg.mpr (hf hij))]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr (ho j i hji)) (sub_nonneg.mpr (hf hji))]
  have H := Finset.sum_le_sum (s := s) (fun i _ => Finset.sum_le_sum (s := s) (fun j _ => hp i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at H
  linarith

def weight (a D σ : ℝ) (k : ℕ) : ℝ := (a + D * k) ^ (-σ)
def moment (a D σ : ℝ) (k : ℕ) : ℝ := weight a D σ k * Real.log (a + D*k)
def mean (a D σ : ℝ) := (∑' k, moment a D σ k) / ∑' k, weight a D σ k

private theorem weight_pos {a D : ℝ} (ha : 1 ≤ a) (hD : 1 ≤ D) (σ : ℝ) (k : ℕ) :
    0 < weight a D σ k := by
  unfold weight
  have hk := mul_nonneg (show 0 ≤ D by linarith) (Nat.cast_nonneg (α := ℝ) k)
  exact Real.rpow_pos_of_pos (by linarith) _

private theorem progression_ge {a D : ℝ} (ha : 1 ≤ a) (hD : 1 ≤ D) (k : ℕ) :
    (k : ℝ) + 1 ≤ a + D*k := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hD) (Nat.cast_nonneg (α := ℝ) k)]

private theorem weight_summable {a D σ : ℝ} (ha : 1 ≤ a) (hD : 1 ≤ D) (hσ : 1 < σ) :
    Summable (weight a D σ) := by
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
  apply Summable.of_nonneg_of_le (fun k => (weight_pos ha hD σ k).le) _ hs
  intro k
  unfold weight
  push_cast
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (progression_ge ha hD k) (by linarith)

private theorem moment_summable {a D σ : ℝ} (ha : 1 ≤ a) (hD : 1 ≤ D) (hσ : 1 < σ) :
    Summable (moment a D σ) := by
  let t := (σ-1)/2
  have ht : 0 < t := by dsimp [t]; linarith
  have he : t-σ < -1 := by dsimp [t]; linarith
  have hs := ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr he)).mul_right (1/t)
  apply Summable.of_nonneg_of_le _ _ hs
  · intro k
    exact mul_nonneg (weight_pos ha hD σ k).le (Real.log_nonneg (by
      have := progression_ge ha hD k; linarith [Nat.cast_nonneg (α := ℝ) k]))
  · intro k
    let x := a + D * k
    have hx : 0 < x := by have := progression_ge ha hD k; dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx t)
    rw [Real.log_rpow hx] at hl
    have hb : Real.log x ≤ x ^ t * (1/t) := by
      rw [mul_one_div, le_div_iff₀ ht]
      linarith
    change x ^ (-σ) * Real.log x ≤ _
    calc
      _ ≤ x ^ (-σ) * (x^t * (1/t)) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx.le _)
      _ = x ^ (t-σ) * (1/t) := by rw [← mul_assoc, ← Real.rpow_add hx]; congr 2; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        push_cast
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (progression_ge ha hD k) (by linarith)

private theorem weights_ordered {a b D σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hD : 1 ≤ D) (hσ : 1 < σ) (i j : ℕ) (hij : i ≤ j) :
    weight a D σ j * weight b D σ i ≤ weight a D σ i * weight b D σ j := by
  have hb := ha.trans hab
  have hpos {c : ℝ} (hc : 1 ≤ c) (k : ℕ) : 0 < c + D * k := by
    have := progression_ge hc hD k
    linarith [Nat.cast_nonneg (α := ℝ) k]
  unfold weight
  rw [← Real.mul_rpow (hpos ha j).le (hpos hb i).le,
    ← Real.mul_rpow (hpos ha i).le (hpos hb j).le]
  apply Real.rpow_le_rpow_of_nonpos (mul_pos (hpos ha i) (hpos hb j)) _ (by linarith)
  have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith only [mul_nonneg (mul_nonneg (by linarith : 0 ≤ D) (sub_nonneg.mpr hab))
    (sub_nonneg.mpr hcast)]

theorem mean_mono {a b D σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hD : 1 ≤ D) (hσ : 1 < σ) :
    mean a D σ ≤ mean b D σ := by
  have hb := ha.trans hab
  have aw := weight_summable ha hD hσ
  have bw := weight_summable hb hD hσ
  have am := moment_summable ha hD hσ
  have bm := moment_summable hb hD hσ
  have hpos {c : ℝ} (hc : 1 ≤ c) : 0 < ∑' k, weight c D σ k :=
    (weight_summable hc hD hσ).tsum_pos (fun k => (weight_pos hc hD σ k).le) 0 (weight_pos hc hD σ 0)
  rw [mean, mean, div_le_div_iff₀ (hpos ha) (hpos hb)]
  rw [mul_comm (∑' k, moment b D σ k)]
  apply le_of_tendsto_of_tendsto'
    (am.hasSum.tendsto_sum_nat.mul bw.hasSum.tendsto_sum_nat)
    (aw.hasSum.tendsto_sum_nat.mul bm.hasSum.tendsto_sum_nat)
  intro N
  let f : ℕ → ℝ := fun k => Real.log (b + D*k)
  have hf : Monotone f := by
    intro i j hij
    apply Real.log_le_log
    · have := progression_ge hb hD i; linarith [Nat.cast_nonneg (α := ℝ) i]
    · exact add_le_add_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by linarith)) _
  apply le_trans _ (ordered_weighted_sums (Finset.range N) (weight a D σ)
    (weight b D σ) f hf (weights_ordered ha hab hD hσ))
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun k _ => (weight_pos hb hD σ k).le))
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (weight_pos ha hD σ k).le
  apply Real.log_le_log _ (add_le_add_left hab _)
  have := progression_ge ha hD k
  linarith [Nat.cast_nonneg (α := ℝ) k]

/-- Factoring out the period gives the endpoint mean exactly. -/
theorem mean_last {D σ : ℝ} (hD : 1 ≤ D) (hσ : 1 < σ) :
    mean D D σ = Real.log D + mean 1 1 σ := by
  have hd : 0 < D := by linarith
  have hpow : D ^ (-σ) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  have hw (k : ℕ) : weight D D σ k = D ^ (-σ) * weight 1 1 σ k := by
    unfold weight
    rw [show D+D*k = D*(1+1*k) by ring, Real.mul_rpow hd.le (by positivity)]
  have hm (k : ℕ) : moment D D σ k = D ^ (-σ) *
      (Real.log D * weight 1 1 σ k + moment 1 1 σ k) := by
    change weight D D σ k * Real.log (D+D*k) = _
    rw [hw, show D+D*k = D*(1+1*k) by ring, Real.log_mul hd.ne' (by positivity)]
    unfold moment
    ring
  have hsum := weight_summable (a := 1) (D := 1) le_rfl le_rfl hσ
  have hmom := moment_summable (a := 1) (D := 1) le_rfl le_rfl hσ
  have hne := (hsum.tsum_pos (fun k => (weight_pos le_rfl le_rfl σ k).le) 0
    (weight_pos le_rfl le_rfl σ 0)).ne'
  unfold mean
  simp_rw [hw, hm]
  rw [tsum_mul_left, (hsum.mul_left _).tsum_add hmom, tsum_mul_left, tsum_mul_left]
  field_simp [hpow, hne]

theorem compression_upper {ι : Type*} (s : Finset ι) {a w y : ι → ℝ} {b D σ : ℝ}
    (hD : 1 ≤ D) (hσ : 1 < σ) (ha : ∀ i ∈ s, 1 ≤ a i)
    (hb : ∀ i ∈ s, y i ≠ 0 → a i ≤ b) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * y i ^ 2 * mean (a i) D σ) ≤
      (∑ i ∈ s, w i * y i ^ 2) * mean b D σ := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hz : y i = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left (mean_mono (ha i hi) (hb i hi hz) hD hσ)
      (mul_nonneg (hw i hi) (sq_nonneg _))

section Leverage
open scoped Matrix
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

def weightedGram (w : α → ℝ) (v : α → ι → ℝ) : Matrix ι ι ℝ :=
  ∑ a, w a • Matrix.vecMulVec (v a) (v a)

def leverage (w : α → ℝ) (v : α → ι → ℝ) (a : α) : ℝ :=
  w a * (((weightedGram w v)⁻¹ *ᵥ v a) ⬝ᵥ v a)

theorem leverage_nonneg {w : α → ℝ} {v : α → ι → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hG : (weightedGram w v).PosDef) (a : α) :
    0 ≤ leverage w v a := by
  have h := hG.inv.posSemidef.dotProduct_mulVec_nonneg (v a)
  unfold leverage
  rw [dotProduct_comm]
  exact mul_nonneg (hw a) (by simpa using h)

theorem weighted_trace (w m : α → ℝ) (v : α → ι → ℝ) :
    ((weightedGram w v)⁻¹ * weightedGram (fun a => m a * w a) v).trace =
      ∑ a, m a * leverage w v a := by
  unfold leverage
  simp only [weightedGram]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, smul_eq_mul, mul_assoc]

theorem leverage_sum {w : α → ℝ} {v : α → ι → ℝ} (hG : (weightedGram w v).PosDef) :
    ∑ a, leverage w v a = (Fintype.card ι : ℝ) := by
  have h := weighted_trace w (fun _ => 1) v
  simp only [one_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hG.det_pos.ne'),
    Matrix.trace_one] at h
  exact h.symm

/-- An upper bound only over nonzero feature rows suffices for the corrected trace. -/
theorem log_trace_upper {w a : α → ℝ} {v : α → ι → ℝ} {D b σ : ℝ}
    (hG : (weightedGram w v).PosDef) (hw : ∀ j, 0 ≤ w j) (ha : ∀ j, 1 ≤ a j)
    (hb : ∀ j, v j ≠ 0 → a j ≤ b) (hD : 1 ≤ D) (hσ : 1 < σ) :
    ((weightedGram w v)⁻¹ * weightedGram (fun j => mean (a j) D σ * w j) v).trace ≤
      (Fintype.card ι : ℝ) * mean b D σ := by
  rw [weighted_trace, ← leverage_sum hG, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : v j = 0
  · simp [leverage, hj]
  · rw [mul_comm (mean _ _ _)]
    exact mul_le_mul_of_nonneg_left (mean_mono (ha j) (hb j hj) hD hσ) (leverage_nonneg hw hG j)

end Leverage
end RiemannResearch.Analysis.PeriodicLogCompression
