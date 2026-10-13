import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Residual endpoint feedback and reciprocal rates

Source: user-requested backwards RH verification, 13 October 2026.
These conditional deductions are independently formalized, without a novelty claim.
No missing arithmetic bound is asserted.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.ResidualEndpointFeedback

/-- Replacing `a` by an upper bound is valid on the decreasing side of the
quadratic Gram determinant. No lower bound on `a` is necessary. -/
theorem gram_upper_surrogate (x y a b : ℝ) (hy : 0 ≤ y) (hab : a ≤ b)
    (hslope : 2 * (1 + y) * b ≤ 4 * x)
    (hgram : (x - a / 2)^2 ≤ (y / 2) * (x - a^2 / 2)) :
    4 * x^2 - 2 * x * y - 4 * x * b + (1 + y) * b^2 ≤ 0 := by
  have hfac : 0 ≤ 4 * x - (1 + y) * (a + b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 1 + y by linarith)]
  have hprod := mul_nonneg (sub_nonneg.mpr hab) hfac
  nlinarith

/-- The tangent quadratic drop, expressed through its two coefficient
identities. This version isolates the algebra from the square-root constant. -/
theorem quadratic_drop_of_endpoint_coefficients (x y a c κ : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 3 / 4)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 4)
    (hroot : c^2 - 4 * c + 2 = 0)
    (hscale : (6 - 4 * c) * κ = c^2)
    (ha : a ≤ c * y)
    (hgram : (x - a / 2)^2 ≤ (y / 2) * (x - a^2 / 2)) :
    x ≤ y - κ * y^2 := by
  by_contra hn
  have hxb : y - κ * y^2 < x := lt_of_not_ge hn
  let b : ℝ := y - κ * y^2
  have hy2 : y^2 ≤ y := by nlinarith
  have hb : 3 / 4 * y ≤ b := by
    dsimp [b]
    nlinarith [mul_nonneg (show 0 ≤ 1 / 4 - κ by linarith) (sq_nonneg y)]
  have hcy : c * y ≤ 3 / 4 * y :=
    mul_le_mul_of_nonneg_right hc1 hy0
  have hcy0 : 0 ≤ c * y := mul_nonneg hc0 hy0
  have hslope : 2 * (1 + y) * (c * y) ≤ 4 * x := by
    nlinarith [mul_nonneg hcy0 (show 0 ≤ 1 - y by linarith)]
  have hFnonpos := gram_upper_surrogate x y a (c * y) hy0 ha hslope hgram
  have hfac : 0 < 4 * (x + b) - 2 * y - 4 * c * y := by
    change b < x at hxb
    nlinarith
  have hstrict : 0 < (x - b) * (4 * (x + b) - 2 * y - 4 * c * y) :=
    mul_pos (sub_pos.mpr hxb) hfac
  have hbase :
      4 * b^2 - 2 * b * y - 4 * b * (c * y) + (1 + y) * (c * y)^2 =
        4 * κ^2 * y^4 := by
    dsimp [b]
    calc
      _ = y^2 * (c^2 - 4 * c + 2) +
          y^3 * (c^2 - (6 - 4 * c) * κ) + 4 * κ^2 * y^4 := by ring
      _ = _ := by rw [hroot, hscale]; ring
  have hbase0 : 0 ≤ 4 * κ^2 * y^4 := by positivity
  nlinarith

/-- The numerical coefficient advertised in the research note is valid.
The hypotheses do not require `a ≥ 0`, `x ≥ 0`, or `x ≤ y`. -/
theorem quadratic_drop_of_endpoint (x y a : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (ha : a ≤ (2 - Real.sqrt 2) * y)
    (hgram : (x - a / 2)^2 ≤ (y / 2) * (x - a^2 / 2)) :
    x ≤ y - ((4 * Real.sqrt 2 - 5) / 7) * y^2 := by
  have hs0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hslo : 5 / 4 ≤ Real.sqrt (2 : ℝ) := by nlinarith
  have hshi : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by nlinarith
  apply quadratic_drop_of_endpoint_coefficients x y a (2 - Real.sqrt 2)
    ((4 * Real.sqrt 2 - 5) / 7) hy0 hy1
  · linarith
  · linarith
  · linarith
  · linarith
  · nlinarith
  · nlinarith
  · exact ha
  · exact hgram

/-- Cofinal endpoint feedback with an additive error tending to zero.
Only `x`, `y`, and the error must converge; `a` need not converge or be
nonnegative. A subsequence can be substituted for the sequences here. -/
theorem limit_zero_of_endpoint (x y a e : ℕ → ℝ) (L c : ℝ)
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hc0 : 0 < c) (hc1 : c < 1)
    (hroot : c^2 - 4 * c + 2 = 0)
    (hx : Tendsto x atTop (𝓝 L)) (hy : Tendsto y atTop (𝓝 L))
    (he : Tendsto e atTop (𝓝 0))
    (hy0 : ∀ n, 0 ≤ y n)
    (ha : ∀ n, a n ≤ c * y n + e n)
    (hgram : ∀ n, (x n - a n / 2)^2 ≤ (y n / 2) * (x n - (a n)^2 / 2)) :
    L = 0 := by
  by_contra hL
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
  let b : ℕ → ℝ := fun n => c * y n + e n
  have hb : Tendsto b atTop (𝓝 (c * L)) := by
    simpa only [b, add_zero] using (tendsto_const_nhds.mul hy).add he
  have hmargin : Tendsto (fun n => 4 * x n - 2 * (1 + y n) * b n)
      atTop (𝓝 (4 * L - 2 * (1 + L) * (c * L))) :=
    (tendsto_const_nhds.mul hx).sub
      ((tendsto_const_nhds.mul (tendsto_const_nhds.add hy)).mul hb)
  have hfactor : 0 < 2 - (1 + L) * c := by
    nlinarith [mul_nonneg (le_of_lt hc0) (show 0 ≤ 1 - L by linarith)]
  have hmargin_pos : 0 < 4 * L - 2 * (1 + L) * (c * L) := by
    nlinarith [mul_pos hLpos hfactor]
  have hevent : ∀ᶠ n in atTop, 2 * (1 + y n) * b n ≤ 4 * x n := by
    filter_upwards [hmargin.eventually (eventually_gt_nhds hmargin_pos)] with n hn
    linarith
  have hFevent : ∀ᶠ n in atTop,
      4 * (x n)^2 - 2 * x n * y n - 4 * x n * b n + (1 + y n) * (b n)^2 ≤ 0 := by
    filter_upwards [hevent] with n hn
    exact gram_upper_surrogate (x n) (y n) (a n) (b n) (hy0 n) (ha n) hn (hgram n)
  have hFlimit : Tendsto (fun n =>
      4 * (x n)^2 - 2 * x n * y n - 4 * x n * b n + (1 + y n) * (b n)^2)
      atTop (𝓝 (4 * L^2 - 2 * L * L - 4 * L * (c * L) + (1 + L) * (c * L)^2)) :=
    (((tendsto_const_nhds.mul (hx.pow 2)).sub
      ((tendsto_const_nhds.mul hx).mul hy)).sub
      ((tendsto_const_nhds.mul hx).mul hb)).add
      ((tendsto_const_nhds.add hy).mul (hb.pow 2))
  have hFle := le_of_tendsto_of_tendsto hFlimit tendsto_const_nhds hFevent
  have hid : 4 * L^2 - 2 * L * L - 4 * L * (c * L) + (1 + L) * (c * L)^2 =
      c^2 * L^3 := by
    calc
      _ = L^2 * (c^2 - 4 * c + 2) + c^2 * L^3 := by ring
      _ = _ := by rw [hroot]; ring
  rw [hid] at hFle
  have hpos : 0 < c^2 * L^3 := mul_pos (sq_pos_of_pos hc0) (pow_pos hLpos 3)
  linarith

/-- A nonnegative quadratic-drop recurrence yields the affine reciprocal
budget even if some iterate vanishes. -/
theorem quadratic_drop_affine_budget (d : ℕ → ℝ) (α t : ℝ)
    (hd : ∀ n, 0 ≤ d n) (hα : 0 ≤ α) (hinit : t * d 0 ≤ 1)
    (hdrop : ∀ n, d (n + 1) ≤ d n - α * (d n)^2) :
    ∀ n : ℕ, (t + α * (n : ℝ)) * d n ≤ 1 := by
  intro n
  induction n with
  | zero => simpa using hinit
  | succ n ih =>
      have hmon : d (n + 1) ≤ d n := by
        nlinarith [hdrop n, mul_nonneg hα (sq_nonneg (d n))]
      have hfrac : d (n + 1) + α * d n * d (n + 1) ≤ d n := by
        have hp := mul_le_mul_of_nonneg_left hmon (mul_nonneg hα (hd n))
        nlinarith [hdrop n]
      have hnext : (t + α * (n : ℝ) + α) * d (n + 1) ≤ 1 := by
        by_cases hz : d n = 0
        · have hzero : d (n + 1) = 0 := le_antisymm (by simpa [hz] using hmon) (hd _)
          simp [hzero]
        · have hpos : 0 < d n := lt_of_le_of_ne (hd n) (Ne.symm hz)
          apply (mul_le_mul_iff_right₀ hpos).mp
          have hp := mul_le_mul_of_nonneg_right ih (hd (n + 1))
          nlinarith
      simpa only [Nat.cast_succ, mul_add, mul_one, add_assoc] using hnext

theorem quadratic_drop_reciprocal_rate (d : ℕ → ℝ) (α : ℝ)
    (hd : ∀ n, 0 ≤ d n) (hd0 : 0 < d 0) (hα : 0 ≤ α)
    (hdrop : ∀ n, d (n + 1) ≤ d n - α * (d n)^2) :
    ∀ n : ℕ, d n ≤ 1 / (1 / d 0 + α * (n : ℝ)) := by
  have hinit : (1 / d 0) * d 0 ≤ 1 := by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hd0)]
  have hb := quadratic_drop_affine_budget d α (1 / d 0) hd hα hinit hdrop
  intro n
  have hden : 0 < 1 / d 0 + α * (n : ℝ) := by positivity
  apply (le_div_iff₀ hden).mpr
  simpa only [mul_comm] using hb n

end RiemannResearch.Analysis.ResidualEndpointFeedback
