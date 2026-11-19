import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The microscopic horizontal hypothesis in ordinate pair correlation

The cumulative multiplicity law gives weight 1/N(T) to each occurrence.
For a Selberg density input of any fixed positive slope, convergence in
probability of the log-scaled horizontal marks to zero is equivalent to the
vanishing of any one of their positive integer moments. At order two this is
the horizontal hypothesis in §7 of MellinModularQuadraticAttempt20261118.md.
The implication uses a uniform twice-order moment and a finite Young bound.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Cumulative probability of leaving every fixed microscopic box tends to zero. -/
def MicroscopicHorizontalConcentration : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℝ =>
    strictTail T (δ / Real.log T) / (Ncount 0 T : ℝ)) atTop (𝓝 0)

private theorem scaled_mark_sum (T : ℝ) (k : ℕ) :
    (∑ c : Copies T, (copyDisplacement T c * Real.log T) ^ k) / (Ncount 0 T : ℝ) =
      displacementMoment T k * Real.log T ^ k := by
  simp only [mul_pow, ← Finset.sum_mul, displacementMoment]
  ring

/-- Upper and lower finite comparisons, with strict thresholds and copies. -/
theorem microscopic_moment_tail_sandwich {T δ w : ℝ} (hT : 1 < T) (hδ : 0 < δ)
    (hw : 0 < w) (k : ℕ) :
    let P := strictTail T (δ / Real.log T) / (Ncount 0 T : ℝ)
    let M := fun j : ℕ => displacementMoment T j * Real.log T ^ j
    δ ^ k * P ≤ M k ∧ M k ≤ δ ^ k + w * M (2*k) + P / (4*w) := by
  classical
  let x := fun c : Copies T => copyDisplacement T c * Real.log T
  let i := fun c : Copies T => if δ / Real.log T < copyDisplacement T c then (1 : ℝ) else 0
  have hL := Real.log_pos hT
  have xpos (c : Copies T) : 0 ≤ x c := mul_nonneg (abs_nonneg _) hL.le
  have tail : strictTail T (δ / Real.log T) = ∑ c : Copies T, i c := rfl
  have left (c : Copies T) : δ ^ k * i c ≤ x c ^ k := by
    dsimp only [i]
    split_ifs with hc
    · rw [mul_one]
      exact pow_le_pow_left₀ hδ.le ((div_lt_iff₀ hL).mp hc).le _
    · simp [pow_nonneg (xpos c)]
  have right (c : Copies T) :
      x c ^ k ≤ δ ^ k + w * x c ^ (2*k) + i c / (4*w) := by
    dsimp only [i]
    split_ifs with hc
    · have hs := sq_nonneg (2*w*x c^k - 1)
      have h := (le_div_iff₀ (show 0 < 4*w by positivity)).mpr
        (show (x c^k - w * (x c^k)^2)*(4*w) ≤ 1 by nlinarith only [hs])
      rw [Nat.mul_comm 2 k, pow_mul]
      linarith [pow_nonneg hδ.le k]
    · have hx : x c ≤ δ := (le_div_iff₀ hL).mp (le_of_not_gt hc)
      have hpow := pow_le_pow_left₀ (xpos c) hx k
      have hpos := mul_nonneg hw.le (pow_nonneg (xpos c) (2*k))
      simp only [zero_div, add_zero]
      linarith
  let N : ℝ := (Ncount 0 T : ℝ)
  have hn : 0 ≤ N := Nat.cast_nonneg _
  have card : (Fintype.card (Copies T) : ℝ) = N := by
    rw [card_copies]
  dsimp only
  rw [← scaled_mark_sum, ← scaled_mark_sum, tail]
  constructor
  · have h := div_le_div_of_nonneg_right (Finset.sum_le_sum (s := Finset.univ) fun c _ => left c) hn
    simpa only [← Finset.mul_sum, mul_div_assoc, x] using h
  · have h := div_le_div_of_nonneg_right (Finset.sum_le_sum (s := Finset.univ) fun c _ => right c) hn
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_div, card] at h
    by_cases hzero : N = 0
    · change (Ncount 0 T : ℝ) = 0 at hzero
      simp [hzero, pow_nonneg hδ.le k]
    · have heq : (N * δ^k + w * (∑ c : Copies T, x c^(2*k)) +
          (∑ c : Copies T, i c) / (4*w)) / N =
          δ^k + w * ((∑ c : Copies T, x c^(2*k)) / N) +
          ((∑ c : Copies T, i c) / N) / (4*w) := by
        field_simp [hzero,hw.ne']
      exact h.trans_eq heq

private theorem scaled_displacement_eventually_bounded {a : ℝ} (ha : 0 < a)
    (h : UniformSelbergDensity a) (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop,
      displacementMoment T (p+1) * Real.log T ^ (p+1) ≤ K := by
  obtain ⟨B, hB, hbound⟩ := exists_selberg_displacementMoment_bound ha h
  refine ⟨B * ((p+1).factorial : ℝ) / a ^ (p+1), by positivity, ?_⟩
  filter_upwards [hbound] with T hb
  apply (le_div_iff₀ (pow_pos ha _)).mpr
  simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hb p

/-- With one positive-slope Selberg estimate, a fixed integer moment of
any positive order vanishes exactly under microscopic concentration. -/
theorem scaled_displacement_tendsto_zero_iff {a : ℝ} (ha : 0 < a)
    (h : UniformSelbergDensity a) (p : ℕ) :
    Tendsto (fun T : ℝ => displacementMoment T (p+1) * Real.log T ^ (p+1))
      atTop (𝓝 0) ↔ MicroscopicHorizontalConcentration := by
  constructor
  · intro hm δ hδ
    apply squeeze_zero'
    · filter_upwards with T
      exact div_nonneg (FiniteStrictTail.tail_nonneg _ _ _) (Nat.cast_nonneg _)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
      have hb := (microscopic_moment_tail_sandwich hT hδ (by norm_num : (0 : ℝ) < 1) (p+1)).1
      exact (le_div_iff₀ (pow_pos hδ _)).mpr (by simpa only [mul_comm] using hb)
    · simpa [mul_comm] using hm.div_const (δ ^ (p+1))
  · intro hc
    obtain ⟨K, hK, hbound⟩ := scaled_displacement_eventually_bounded ha h (2*p+1)
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ : ℝ := min (ε/4) 1
    have hd : 0 < δ := lt_min (by positivity) zero_lt_one
    have hd1 : δ ≤ 1 := min_le_right _ _
    have hdε : δ ≤ ε/4 := min_le_left _ _
    have hd' : δ ^ (p+1) ≤ ε/4 :=
      (by simpa using pow_le_pow_of_le_one hd.le hd1 (show 1 ≤ p+1 by omega) : δ^(p+1) ≤ δ).trans hdε
    let w := ε / (4 * (K+1))
    have hw : 0 < w := div_pos hε (by positivity)
    have hwK : w * K ≤ ε/4 := by
      calc
        _ ≤ w * (K+1) := mul_le_mul_of_nonneg_left (by linarith) hw.le
        _ = ε/4 := by dsimp [w]; field_simp [show K + 1 ≠ 0 by positivity]
    have ht := ((hc δ hd).div_const (4*w)).eventually (Iio_mem_nhds (show (0:ℝ)/(4*w) < ε/4 by simpa using (show 0 < ε/4 by positivity)))
    filter_upwards [hbound, ht, eventually_gt_atTop (1 : ℝ)] with T hB htail hT
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (displacementMoment_nonneg _ _)
      (pow_nonneg (Real.log_pos hT).le _))]
    have hB' : displacementMoment T (2*(p+1)) * Real.log T ^ (2*(p+1)) ≤ K := by
      simpa only [show 2*(p+1) = 2*p+1+1 by omega] using hB
    have hb := (microscopic_moment_tail_sandwich hT hd hw (p+1)).2
    change strictTail T (δ / Real.log T) / (Ncount 0 T : ℝ) / (4*w) < ε/4 at htail
    linarith only [hb, hd', mul_le_mul_of_nonneg_left hB' hw.le, hwK, htail, hε]

end RiemannResearch.Analysis.ActualZeroOrdinate
