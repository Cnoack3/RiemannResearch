import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# The full Pareto L1 norm on the sequence Hilbert space

Source: the user's L2-to-L1 convergence argument, 22 September 2026.
The absolute-value vector realizes the complete weighted L1 norm as
a Hilbert pairing with the constant target. Cauchy--Schwarz gives
L1 <= L2 because the Pareto measure has total mass one.
These estimates apply to every actual ThresholdHilbert vector.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

private theorem abs_sequence_square_summable (f : ThresholdHilbert) :
    Summable (fun k => positiveWeight k * |hilbertSequence f k| ^ 2) := by
  simpa only [sq_abs] using hilbertSequence_square_summable f

def hilbertAbs (f : ThresholdHilbert) : ThresholdHilbert :=
  sequenceHilbert (fun k => |hilbertSequence f k|) (abs_sequence_square_summable f)

theorem hilbertAbs_sequence (f : ThresholdHilbert) :
    hilbertSequence (hilbertAbs f) = fun k => |hilbertSequence f k| := by
  apply hilbertSequence_sequenceHilbert
  simp

theorem hilbertAbs_norm (f : ThresholdHilbert) : ‖hilbertAbs f‖ = ‖f‖ := by
  have h : ‖hilbertAbs f‖ ^ 2 = ‖f‖ ^ 2 := by
    simp only [hilbert_norm_weighted_sq, hilbertAbs_sequence, sq_abs]
  nlinarith [norm_nonneg (hilbertAbs f), norm_nonneg f]

/-- The complete Pareto L1 norm, with zero coordinate anchored. -/
def hilbertL1Norm (f : ThresholdHilbert) : ℝ :=
  ∑' k, positiveWeight k * |hilbertSequence f k|

theorem hilbertL1Norm_summable (f : ThresholdHilbert) :
    Summable (fun k => positiveWeight k * |hilbertSequence f k|) :=
  weighted_summable_of_square (abs_sequence_square_summable f)

theorem hilbertL1Norm_nonneg (f : ThresholdHilbert) : 0 ≤ hilbertL1Norm f :=
  tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k) (abs_nonneg _))

theorem hilbertL1Norm_eq_inner_abs (f : ThresholdHilbert) :
    hilbertL1Norm f = inner ℝ (hilbertAbs f) hilbertOne := by
  rw [hilbert_inner_one, hilbertAbs_sequence]
  rfl

theorem hilbertL1Norm_le_norm (f : ThresholdHilbert) : hilbertL1Norm f ≤ ‖f‖ := by
  have hOne : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  rw [hilbertL1Norm_eq_inner_abs]
  simpa only [hilbertAbs_norm, hOne, mul_one] using real_inner_le_norm (hilbertAbs f) hilbertOne

theorem inner_one_le_hilbertL1Norm (f : ThresholdHilbert) :
    inner ℝ f hilbertOne ≤ hilbertL1Norm f := by
  rw [hilbert_inner_one]
  exact Summable.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (le_abs_self _) (positiveWeight_nonneg k))
    (weighted_summable_of_square (hilbertSequence_square_summable f))
    (hilbertL1Norm_summable f)

theorem hilbertL1Norm_tendsto_zero_of_norm {f : ℕ → ThresholdHilbert}
    (h : Tendsto (fun n => ‖f n‖) atTop (𝓝 0)) :
    Tendsto (fun n => hilbertL1Norm (f n)) atTop (𝓝 0) :=
  squeeze_zero (fun n => hilbertL1Norm_nonneg (f n))
    (fun n => hilbertL1Norm_le_norm (f n)) h

theorem inner_one_sub_first_le_hilbertL1Norm (f : ThresholdHilbert) :
    inner ℝ f hilbertOne - hilbertSequence f 1 ≤ hilbertL1Norm f := by
  have hs := weighted_summable_of_square (hilbertSequence_square_summable f)
  have hi : Summable (fun k : ℕ => if k = 1 then hilbertSequence f 1 else 0) := by
    apply (summable_nat_add_iff 2).mp
    have he : (fun k : ℕ => if k + 2 = 1 then hilbertSequence f 1 else 0) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext k
      rw [if_neg (by omega)]
    rw [he]
    exact summable_zero
  have hb := Summable.tsum_le_tsum
    (f := fun k => positiveWeight k * hilbertSequence f k -
      (if k = 1 then hilbertSequence f 1 else 0))
    (g := fun k => positiveWeight k * |hilbertSequence f k|)
    (fun k => by
      by_cases hk : k = 1
      · subst k
        change positiveWeight 1 * hilbertSequence f 1 - hilbertSequence f 1 ≤
          positiveWeight 1 * |hilbertSequence f 1|
        rw [show positiveWeight 1 = (1 / 2 : ℝ) by norm_num [positiveWeight]]
        linarith [neg_le_abs (hilbertSequence f 1)]
      · simp only [if_neg hk, sub_zero]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (positiveWeight_nonneg k))
    (hs.sub hi) (hilbertL1Norm_summable f)
  rw [hs.tsum_sub hi] at hb
  simpa [hilbert_inner_one, paretoMean, hilbertL1Norm] using hb

theorem hilbertL1Norm_sub_le (f g : ThresholdHilbert) :
    hilbertL1Norm f - hilbertL1Norm g ≤ hilbertL1Norm (f - g) := by
  have hseq : hilbertSequence (f - g) = hilbertSequence f - hilbertSequence g :=
    hilbertSequenceLinear.map_sub f g
  have hb := Summable.tsum_le_tsum
    (f := fun k => positiveWeight k * |hilbertSequence f k| -
      positiveWeight k * |hilbertSequence g k|)
    (g := fun k => positiveWeight k * |hilbertSequence (f - g) k|)
    (fun k => by
      simpa only [mul_sub, hseq, Pi.sub_apply] using
        mul_le_mul_of_nonneg_left
          (abs_sub_abs_le_abs_sub (hilbertSequence f k) (hilbertSequence g k))
          (positiveWeight_nonneg k))
    ((hilbertL1Norm_summable f).sub (hilbertL1Norm_summable g))
    (hilbertL1Norm_summable (f - g))
  rw [(hilbertL1Norm_summable f).tsum_sub (hilbertL1Norm_summable g)] at hb
  exact hb

theorem hilbertL1Norm_smul (a : ℝ) (f : ThresholdHilbert) :
    hilbertL1Norm (a • f) = |a| * hilbertL1Norm f := by
  unfold hilbertL1Norm
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
  ring

@[simp] theorem hilbertL1Norm_zero : hilbertL1Norm (0 : ThresholdHilbert) = 0 :=
  le_antisymm (by simpa only [norm_zero] using hilbertL1Norm_le_norm (0 : ThresholdHilbert))
    (hilbertL1Norm_nonneg _)

theorem hilbertL1Norm_add_le (x y : ThresholdHilbert) :
    hilbertL1Norm (x+y) ≤ hilbertL1Norm x + hilbertL1Norm y := by
  have h := hilbertL1Norm_sub_le (x+y) x
  rw [add_sub_cancel_left] at h
  linarith only [h]

theorem hilbertL1Norm_abs_sub_le (f g : ThresholdHilbert) :
    |hilbertL1Norm f - hilbertL1Norm g| ≤ hilbertL1Norm (f - g) := by
  have hfg := hilbertL1Norm_sub_le f g
  have hgf := hilbertL1Norm_sub_le g f
  have he : hilbertL1Norm (g - f) = hilbertL1Norm (f - g) := by
    unfold hilbertL1Norm
    apply tsum_congr
    intro k
    have hgf : hilbertSequence (g - f) = hilbertSequence g - hilbertSequence f :=
      hilbertSequenceLinear.map_sub g f
    have hfg : hilbertSequence (f - g) = hilbertSequence f - hilbertSequence g :=
      hilbertSequenceLinear.map_sub f g
    rw [hgf, hfg]
    simp only [Pi.sub_apply]
    rw [abs_sub_comm]
  rw [he] at hgf
  exact abs_le.mpr ⟨by linarith, hfg⟩

theorem hilbertL1Norm_lipschitz : LipschitzWith 1 hilbertL1Norm := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa [Real.dist_eq, dist_eq_norm] using
    (hilbertL1Norm_abs_sub_le f g).trans (hilbertL1Norm_le_norm (f - g))

theorem hilbertL1Norm_continuous : Continuous hilbertL1Norm :=
  hilbertL1Norm_lipschitz.continuous

theorem hilbertL1Norm_tendsto_of_sub {U : ℕ → ThresholdHilbert}
    {Y : ThresholdHilbert} {p : ℝ}
    (hY : hilbertL1Norm Y = p)
    (h : Tendsto (fun n => hilbertL1Norm (U n - Y)) atTop (𝓝 0)) :
    Tendsto (fun n => hilbertL1Norm (U n)) atTop (𝓝 p) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => by
      simpa only [Real.norm_eq_abs, hY] using hilbertL1Norm_abs_sub_le (U n) Y) h

/-- The full Pareto expectation of the pointwise negative part. -/
def hilbertNegativeMass (f : ThresholdHilbert) : ℝ :=
  ∑' k, positiveWeight k * max (-hilbertSequence f k) 0

private theorem negativePart_identity (x : ℝ) :
    max (-x) 0 = (|x| - x) / 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
    ring
  · have hn : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_left (neg_nonneg.mpr hn), abs_of_nonpos hn]
    ring

theorem hilbertNegativeMass_eq (f : ThresholdHilbert) :
    hilbertNegativeMass f = (hilbertL1Norm f - inner ℝ f hilbertOne) / 2 := by
  have hs := weighted_summable_of_square (hilbertSequence_square_summable f)
  calc
    _ = ∑' k, (positiveWeight k * |hilbertSequence f k| -
        positiveWeight k * hilbertSequence f k) / 2 := by
      apply tsum_congr
      intro k
      rw [negativePart_identity]
      ring
    _ = _ := by
      rw [tsum_div_const, (hilbertL1Norm_summable f).tsum_sub hs, hilbert_inner_one]
      rfl

theorem hilbertNegativeMass_nonneg (f : ThresholdHilbert) :
    0 ≤ hilbertNegativeMass f :=
  tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k) (le_max_right _ _))

theorem hilbertNegativeMass_tendsto_zero_iff {U : ℕ → ThresholdHilbert} {p : ℝ}
    (hmean : ∀ n, inner ℝ (U n) hilbertOne = p) :
    Tendsto (fun n => hilbertNegativeMass (U n)) atTop (𝓝 0) ↔
      Tendsto (fun n => hilbertL1Norm (U n)) atTop (𝓝 p) := by
  constructor
  · intro h
    have heq : (fun n => hilbertL1Norm (U n)) =
        (fun n => 2 * hilbertNegativeMass (U n) + p) := by
      funext n
      rw [hilbertNegativeMass_eq, hmean n]
      ring
    rw [heq]
    have ht : Tendsto (fun n => 2 * hilbertNegativeMass (U n) + p)
        atTop (𝓝 (2 * 0 + p)) :=
      (tendsto_const_nhds.mul h).add tendsto_const_nhds
    simpa using ht
  · intro h
    have ht : Tendsto (fun n => (hilbertL1Norm (U n) - p) / 2)
        atTop (𝓝 ((p - p) / 2)) :=
      (h.sub tendsto_const_nhds).div_const 2
    simpa only [hilbertNegativeMass_eq, hmean, sub_self, zero_div] using ht

section NegativeMassContinuity
set_option backward.isDefEq.respectTransparency false

theorem hilbertL1Norm_neg (f : ThresholdHilbert) :
    hilbertL1Norm (-f) = hilbertL1Norm f := by
  have hs : hilbertSequence (-f) = -hilbertSequence f :=
    hilbertSequenceLinear.map_neg f
  simp only [hilbertL1Norm, hs, Pi.neg_apply, abs_neg]

theorem hilbertNegativeMass_abs_sub_le (f g : ThresholdHilbert) :
    |hilbertNegativeMass f - hilbertNegativeMass g| ≤ hilbertL1Norm (f - g) := by
  have ha := hilbertL1Norm_abs_sub_le f g
  have hu := inner_one_le_hilbertL1Norm (f - g)
  have hl := inner_one_le_hilbertL1Norm (-(f - g))
  rw [inner_neg_left, hilbertL1Norm_neg] at hl
  rw [inner_sub_left] at hu hl
  rw [hilbertNegativeMass_eq, hilbertNegativeMass_eq]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩

theorem hilbertNegativeMass_lipschitz : LipschitzWith 1 hilbertNegativeMass := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa [Real.dist_eq, dist_eq_norm] using
    (hilbertNegativeMass_abs_sub_le f g).trans (hilbertL1Norm_le_norm (f - g))

theorem hilbertNegativeMass_continuous : Continuous hilbertNegativeMass := by
  have hi : Continuous (fun f : ThresholdHilbert => inner ℝ f hilbertOne) :=
    continuous_id.inner continuous_const
  have heq : hilbertNegativeMass =
      (fun f => (hilbertL1Norm f - inner ℝ f hilbertOne) / 2) :=
    funext hilbertNegativeMass_eq
  rw [heq]
  exact (hilbertL1Norm_continuous.sub hi).div_const 2

end NegativeMassContinuity

end RiemannResearch.RH.Pareto
