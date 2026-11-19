import RiemannResearch.Analysis.ActualZeroLoglogTilt
import RiemannResearch.Analysis.MontgomeryReflectedDefect
import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The horizontal defect at the Montgomery transition

The crossover frequency satisfies α log T = (log log T + c)/2.
For bounded c the exponential fourth-moment tilt is bounded by two times
log log T. The Ingham moment bound then controls the signed reflected Gram
estimate at order (log log T)^8/(log T)^3.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open ActualZeroOrdinate MontgomeryHorizontalTransfer

/-- Internal quantitative horizontal defect bound, uniform over bounded
shifts. The constant can be chosen before the bound on the shift. -/
theorem exists_transition_horizontalDefect_loglog_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      horizontalDefect T (transitionFrequency c T) ≤
        K*(Real.log (Real.log T))^8/(Real.log T)^3 := by
  obtain ⟨G, hG, hgram⟩ := MontgomeryReflectedDefect.exists_horizontalDefect_le_reflected_quartic
  obtain ⟨H, hH, htilt⟩ := exists_loglog_tilted_fourth_moment_bound 2 (by norm_num)
  refine ⟨16*G*H, by positivity, ?_⟩
  intro A
  filter_upwards [eventually_ge_atTop (9:ℝ), htilt,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 A)]
    with T hT hw hlarge
  intro c hc
  let L := Real.log T
  let ℓ := Real.log L
  let α := transitionFrequency c T
  let u := (ℓ+c)/2
  have hT0 : 0 < T := by linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  change max 1 A ≤ ℓ at hlarge
  have hℓ := (le_max_left 1 A).trans hlarge
  have hA := (le_max_right 1 A).trans hlarge
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [(abs_le.mp hc).1]
  have huℓ : u ≤ ℓ := by dsimp [u]; linarith [(abs_le.mp hc).2]
  have hαu : α * L = u := div_mul_cancel₀ _ hL.ne'
  have harg : 2 * |u| ≤ 2 * ℓ := by rw [abs_of_nonneg hu0]; linarith
  have hweight := hw (2 * |u|) (by positivity) harg
  have hpoly : (1+|u|)^4 ≤ 16*ℓ^4 := by
    rw [abs_of_nonneg hu0]
    calc
      _ ≤ (2*ℓ)^4 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = _ := by ring
  have hg := hgram T α hT
  change horizontalDefect T α ≤ G*(1+|α*L|)^4*
    ((∑ i : Copies T, (i.1.1.re-1/2)^4 * Real.exp (2 * |α*L| * |i.1.1.re-1/2|))/T) at hg
  rw [hαu] at hg
  apply hg.trans
  calc
    _ ≤ (G*(16*ℓ^4))*(H*ℓ^4/L^3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpoly hG.le) hweight
        (div_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) hT0.le) (by positivity)
    _ = _ := by change _ = 16*G*H*ℓ^8/L^3; ring

/-- The horizontal defect is uniformly little-o of the inverse squared
logarithm. This is the budget for the second-order raw/complex transfer. -/
theorem eventually_transition_horizontalDefect_scaled_le (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      horizontalDefect T (transitionFrequency c T) ≤ ε/(Real.log T)^2 := by
  obtain ⟨K,hK,h⟩ := exists_transition_horizontalDefect_loglog_bound
  filter_upwards [h A,eventually_gt_atTop (1:ℝ),
    (loglog_pow_div_log_tendsto_zero 8).eventually_le_const (div_pos hε hK)]
    with T hb hT hsmall
  intro c hc
  have hL := Real.log_pos hT
  have hp : K*(Real.log (Real.log T))^8 ≤ ε * Real.log T := by
    have hx := mul_le_mul_of_nonneg_left ((div_le_iff₀ hL).mp hsmall) hK.le
    apply hx.trans_eq
    field_simp
  apply (hb c hc).trans
  calc
    _ ≤ (ε*Real.log T)/(Real.log T)^3 := div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := by field_simp

/-- A quartic bound for the horizontal defect over each band
2|α log T| ≤ B log T / log log T, using the Ingham density estimate. -/
theorem exists_horizontalDefect_ingham_band (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ α : ℝ,
      2 * |α * Real.log T| ≤ B * Real.log T / Real.log (Real.log T) →
      horizontalDefect T α ≤ K * (1 + |α * Real.log T|)^4 *
        (Real.log (Real.log T))^4/(Real.log T)^3 := by
  obtain ⟨G,hG,hgram⟩ := MontgomeryReflectedDefect.exists_horizontalDefect_le_reflected_quartic
  obtain ⟨H,hH,hweight⟩ := exists_ingham_tilted_fourth_moment_bound B hB
  refine ⟨G*H,mul_pos hG hH,?_⟩
  filter_upwards [hweight,eventually_ge_atTop (9:ℝ)] with T hw hT
  intro α hα
  have hm := hw (2 * |α * Real.log T|) (by positivity) hα
  apply (hgram T α hT).trans
  exact (mul_le_mul_of_nonneg_left hm (show 0 ≤ G*(1+|α*Real.log T|)^4 by positivity)).trans_eq (by ring)

/-- The reflected horizontal defect is negligible relative to a comparison
scale at least u/log T throughout the mesoscopic Ingham range. -/
theorem mesoscopic_defect_relative_ingham (u scale : ℝ → ℝ)
    (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3*(Real.log (Real.log T))^4/(Real.log T)^2) atTop (𝓝 0))
    (hscale : ∀ᶠ T in atTop, u T/Real.log T ≤ scale T) :
    Tendsto (fun T => horizontalDefect T (u T/Real.log T) / scale T) atTop (𝓝 0) := by
  obtain ⟨K,hK,he⟩ := exists_horizontalDefect_ingham_band 1 (by norm_num)
  have hzero := hsmall.const_mul (16*K)
  simp only [mul_zero] at hzero
  apply squeeze_zero' _ _ hzero
  · filter_upwards [hu.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ),hscale] with T h1 ht hs
    exact div_nonneg (horizontalDefect_nonneg ht _) ((div_nonneg (zero_le_one.trans h1) (Real.log_pos ht).le).trans hs)
  · filter_upwards [hu.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 8,
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
      he,hscale,hsmall.eventually_le_const zero_lt_one,eventually_gt_atTop (1:ℝ)]
      with T hu1 hL8 hℓ1 hF hs hc ht
    let L := Real.log T
    let ℓ := Real.log L
    let x := u T
    change 1 ≤ x at hu1
    change 8 ≤ L at hL8
    change x/L ≤ scale T at hs
    have hx : 0 < x := zero_lt_one.trans_le hu1
    have hL : 0 < L := Real.log_pos ht
    change 1 ≤ ℓ at hℓ1
    have hℓ : 0 < ℓ := zero_lt_one.trans_le hℓ1
    change x^3*ℓ^4/L^2 ≤ 1 at hc
    have hab : x^3*ℓ^4 ≤ L^2 := ((div_le_iff₀ (pow_pos hL 2)).mp hc).trans_eq (one_mul _)
    have hband : 2*x*ℓ ≤ L := by
      have hcube : (2*x*ℓ)^3 ≤ L^3 := calc
        _ = 8*(x^3*ℓ^3) := by ring
        _ ≤ 8*(x^3*ℓ^4) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ1 (by decide : 3 ≤ 4))
            (pow_nonneg hx.le 3)) (by norm_num)
        _ ≤ 8*L^2 := mul_le_mul_of_nonneg_left hab (by norm_num)
        _ ≤ L^3 := by nlinarith only [mul_le_mul_of_nonneg_right hL8 (sq_nonneg L)]
      by_contra! hn
      have hh := pow_lt_pow_left₀ hn hL.le (by decide : (3:ℕ) ≠ 0)
      exact (not_lt_of_ge hcube) hh
    let α := x/L
    have hα : α*L = x := div_mul_cancel₀ _ hL.ne'
    have hfrequency : 2 * |α*L| ≤ 1*L/ℓ := by
      rw [hα,abs_of_pos hx,one_mul]
      exact (le_div_iff₀ hℓ).mpr hband
    have hb := hF α hfrequency
    change horizontalDefect T α ≤ K*(1+|α*L|)^4*ℓ^4/L^3 at hb
    rw [hα,abs_of_pos hx] at hb
    have hp : (1+x)^4 ≤ (2*x)^4 := pow_le_pow_left₀ (by linarith) (by linarith [hu1]) _
    change horizontalDefect T α / scale T ≤ (16*K)*(x^3*ℓ^4/L^2)
    calc
      _ ≤ horizontalDefect T α /(x/L) :=
        div_le_div_of_nonneg_left (horizontalDefect_nonneg ht α) (div_pos hx hL) hs
      _ ≤ (K*(1+x)^4*ℓ^4/L^3)/(x/L) := div_le_div_of_nonneg_right hb (div_pos hx hL).le
      _ ≤ (K*(2*x)^4*ℓ^4/L^3)/(x/L) :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp hK.le) (pow_nonneg hℓ.le 4)) (pow_nonneg hL.le 3)) (div_pos hx hL).le
      _ = _ := by field_simp <;> ring

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
