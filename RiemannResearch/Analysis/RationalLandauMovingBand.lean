import RiemannResearch.Analysis.ActualUniformRationalLandau
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Moving rational Landau bands

Source: the repository's unconditional contour bound
ActualUniformRationalLandau.exists_uniform_rational_landau_rpow_bound.
The exponent 2/5 is the threshold of its X^(5/2) error term, not a claimed
optimal theorem in the literature. The proof keeps all complex zero weights.
Ford--Meng--Zaharescu, Lemma 1, https://arxiv.org/html/1511.06814v2#Thmlem1,
gives a stronger external prime-power range; its sharper provider is not
formalized here. Concrete consumers: ActualFejerMovingFMZ and microscopic
prime-phase probe synthesis. No RH or density hypothesis is used.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate
private theorem log_power_band_envelope_tendsto_zero (θ : ℝ)
    (hθ : θ < 2 / 5) :
    Tendsto (fun T : ℝ => Real.log T *
      (Real.exp (5 * θ * Real.log T / 2) *
        (1 + 4 * (Real.log T)^2 + 2 * Real.log T) / T)) atTop (𝓝 0) := by
  let ε : ℝ := 1 - 5 * θ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have htop : Tendsto (fun T : ℝ => ε * Real.log T) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1 Real.tendsto_log_atTop) (b / ε)] with T hT
    exact (div_le_iff₀ hε).mp hT |>.trans_eq (mul_comm _ _)
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp htop).const_mul (1 / ε)
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp htop).const_mul (2 / ε^2)
  have h3 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp htop).const_mul (4 / ε^3)
  have h := (h1.add h2).add h3
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_def, pow_one]
  have he : Real.exp (5 * θ * Real.log T / 2) / T = Real.exp (-(ε * Real.log T)) := by
    rw [← Real.exp_log hT, ← Real.exp_sub]
    congr 1
    dsimp [ε]
    simp only [Real.log_exp]
    ring
  rw [show Real.log T * (Real.exp (5 * θ * Real.log T / 2) *
      (1 + 4 * (Real.log T)^2 + 2 * Real.log T) / T) =
      (Real.log T * (1 + 4 * (Real.log T)^2 + 2 * Real.log T)) *
        (Real.exp (5 * θ * Real.log T / 2) / T) by ring, he]
  field_simp
  ring

/-- Uniform normalized Landau error on every fixed numerator band T^θ,
θ < 2/5. The previous sufficient 1/8 band is not the limit of the available
rpow envelope. This theorem has no Selberg or RH premise. -/
theorem eventually_rational_landau_error_power_band (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ : θ < 2 / 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n → Real.log (n : ℝ) ≤ θ * Real.log T →
      ‖(landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤ C / Real.log T := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℝ),
    (log_power_band_envelope_tendsto_zero θ hθ).eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with T hT henv
  intro n m hm hmn hn
  have hT0 : 0 < T := by linarith
  have hLp : 0 < Real.log T := Real.log_pos (by linarith)
  have hL : 0 ≤ Real.log T := hLp.le
  have hn0 : (0 : ℝ) < n := by
    have hnpos : 0 < n := by omega
    exact_mod_cast hnpos
  let X := Real.exp (θ * Real.log T)
  have hX : 0 < X := Real.exp_pos _
  have hnX : (n : ℝ) ≤ X := by
    rw [← Real.exp_log hn0]
    exact Real.exp_le_exp.mpr hn
  have hp (r : ℝ) (hr : r ≤ 5 / 2) : X ^ r ≤ Real.exp (5 * θ * Real.log T / 2) := by
    rw [Real.rpow_def_of_pos hX]
    dsimp [X]
    rw [Real.log_exp]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hr (mul_nonneg hθ0 hL)])
  have hXhalf : X ≤ Real.exp (5 * θ * Real.log T / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hθ0 hL])
  have hlog : Real.log (T + 3) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T * T) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_mul hT0.ne' hT0.ne']; ring
  have hlog0 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hsq : (Real.log (T + 3)) ^ 2 ≤ 4 * (Real.log T) ^ 2 := by
    nlinarith
  have hterms : X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
      X * Real.log (T + 3) ≤
      Real.exp (5 * θ * Real.log T / 2) * (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) := by
    have h1 := hp (5 / 2) (by norm_num)
    have h2 := mul_le_mul (hp (3 / 2) (by norm_num)) hsq
      (sq_nonneg _) (Real.exp_pos _).le
    have h3 := mul_le_mul hXhalf hlog hlog0 (Real.exp_pos _).le
    nlinarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  calc
    _ ≤ C * (X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
      X * Real.log (T + 3)) / T :=
      div_le_div_of_nonneg_right (hb T X n m hT hm hmn hnX) hT0.le
    _ ≤ C * (Real.exp (5 * θ * Real.log T / 2) *
      (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hterms hC.le) hT0.le
    _ ≤ C / Real.log T := by
      have hs : Real.exp (5 * θ * Real.log T / 2) *
          (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T ≤ 1 / Real.log T :=
        (le_div_iff₀ hLp).2 (by nlinarith [henv])
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hs hC.le



#print axioms eventually_rational_landau_error_power_band
end RiemannResearch.Analysis.ActualZeroOrdinate
