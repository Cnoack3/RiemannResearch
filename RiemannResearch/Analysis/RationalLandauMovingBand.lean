import RiemannResearch.Analysis.ActualUniformRationalLandau
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Moving rational Landau bands

The contour estimate retains the numerator n and the ratio n/m separately.
Every fixed inverse power of log T follows on the joint band
log n + (3/2) log(n/m) ≤ θ log T with θ < 1. The numerator-only band
n ≤ T^θ with θ < 2/5 follows by dropping m from the budget. The explicit
formula with the nearest-prime-power term is Lemma 1 of Ford, Meng and
Zaharescu, https://doi.org/10.1112/blms.12001.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The numerator and the rational frequency have separate contributions to the contour error. -/
theorem eventually_rational_landau_height_ratio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ, 1 ≤ m → m < n →
      let u := Real.log ((n : ℝ) / (m : ℝ))
      ‖(landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤
        C * ((n : ℝ) * Real.exp (3*u/2)) * (Real.log T)^2 / T := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_rational_landau_bound
  refine ⟨11*C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with T hT hL n m hm hmn
  let L := Real.log T
  let H := Real.log (T+3)
  let u := Real.log ((n : ℝ) / (m : ℝ))
  let E := Real.exp (3*u/2)
  let A := (n : ℝ) * E
  have hT0 : 0 < T := by linarith
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hu := rational_frequency_bounds hm hmn (le_refl (n : ℝ))
  have hu0 : 0 < u := hu.1
  have hE : 1 ≤ E := Real.one_le_exp (by change 0 ≤ 3*u/2; linarith)
  have hnA : (n : ℝ) ≤ A := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg n)
  have hEA : E ≤ A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (zero_le_one.trans hE)
  have hA : 1 ≤ A := hn.trans hnA
  have hH0 : 0 ≤ H := Real.log_nonneg (by linarith)
  have hHL : H ≤ 2 * L := by
    calc
      H ≤ Real.log (T*T) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * L := by rw [Real.log_mul hT0.ne' hT0.ne']; dsimp [L]; ring
  have hHL2 : H^2 ≤ 4*L^2 := by nlinarith [pow_le_pow_left₀ hH0 hHL 2]
  have hgap : 1 + 1 / u ≤ 3 * A := by linarith [hu.2.2.1]
  have hF : E * ((n : ℝ) + H^2) ≤ A + A*(4*L^2) := by
    rw [mul_add, mul_comm E (n : ℝ)]
    exact add_le_add le_rfl (mul_le_mul hEA hHL2 (sq_nonneg _) (by linarith))
  have hG := mul_le_mul hgap hHL hH0 (by linarith : 0 ≤ 3*A)
  have hL1 : 1 ≤ L := hL
  have hsmall : 1 ≤ L^2 := one_le_pow₀ hL1
  have hlinear : L ≤ L^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (by linarith : 0 ≤ L)]
  have hsum : E * ((n : ℝ) + H^2) + (1 + 1/u)*H ≤ 11*A*L^2 := by
    nlinarith only [hF, hG, mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ A),
      mul_le_mul_of_nonneg_left hlinear (by linarith : 0 ≤ A)]
  change ‖(landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤
    11*C*A*L^2/T
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  apply div_le_div_of_nonneg_right _ hT0.le
  exact (hbound T n m hT hm hmn).trans ((mul_le_mul_of_nonneg_left hsum hC.le).trans_eq (by ring))

/-- Every fixed inverse-log power on the joint numerator and frequency band. -/
theorem eventually_rational_landau_error_height_ratio_band (θ : ℝ) (hθ : θ < 1) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ, 1 ≤ m → m < n →
      Real.log (n : ℝ) + 3 * Real.log ((n : ℝ)/(m : ℝ)) / 2 ≤ θ * Real.log T →
      ‖(landauSum T (Real.log ((n : ℝ)/(m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤ C / (Real.log T)^q := by
  obtain ⟨C, hC, hb⟩ := eventually_rational_landau_height_ratio_bound
  have hlim : Tendsto (fun T : ℝ => (Real.log T)^(q+2) / T^(1-θ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop ((q+2 : ℕ) : ℝ) (sub_pos.mpr hθ)).tendsto_div_nhds_zero
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ), hlim.eventually_le_const (by norm_num : (0:ℝ)<1)]
    with T hbound hT hbudget n m hm hmn hband
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hw : (n : ℝ) * Real.exp (3 * Real.log ((n : ℝ)/(m : ℝ)) / 2) ≤ T^θ := by
    simpa only [Real.exp_add, Real.exp_log hn0, Real.rpow_def_of_pos hT0, mul_comm θ (Real.log T)]
      using Real.exp_le_exp.mpr hband
  have hp : T ^ θ * T ^ (1-θ) = T := by
    rw [← Real.rpow_add hT0, show θ + (1-θ) = 1 by ring, Real.rpow_one]
  have hcap : T^θ * (Real.log T)^(q+2) / T ≤ 1 := by
    apply (div_le_one hT0).2
    exact (mul_le_mul_of_nonneg_left ((div_le_one (Real.rpow_pos_of_pos hT0 _)).1 hbudget)
      (Real.rpow_nonneg hT0.le _)).trans_eq hp
  apply (hbound n m hm hmn).trans
  calc
    _ ≤ C * T^θ * (Real.log T)^2 / T := by gcongr
    _ ≤ _ := by
      apply (le_div_iff₀ (pow_pos hL q)).2
      calc
        _ = C * (T^θ * (Real.log T)^(q+2) / T) := by rw [pow_add]; ring
        _ ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcap hC.le

/-- The numerator-only range with any prescribed inverse-log power. -/
theorem eventually_rational_landau_error_power_band_pow (θ : ℝ) (hθ : θ < 2 / 5) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n → Real.log (n : ℝ) ≤ θ * Real.log T →
      ‖(landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤ C / (Real.log T)^q := by
  obtain ⟨C, hC, hb⟩ := eventually_rational_landau_error_height_ratio_band
    (5*θ/2) (by linarith) q
  refine ⟨C, hC, hb.mono ?_⟩
  intro T ht n m hm hmn hn
  apply ht n m hm hmn
  have hu := rational_frequency_bounds hm hmn (le_refl (n : ℝ))
  nlinarith only [hu.2.1, hn]

/-- The first inverse logarithm in the original numerator-only formulation. -/
theorem eventually_rational_landau_error_power_band (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ : θ < 2 / 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n → Real.log (n : ℝ) ≤ θ * Real.log T →
      ‖(landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤ C / Real.log T := by
  simpa only [pow_one] using
    eventually_rational_landau_error_power_band_pow θ (by linarith only [hθ0, hθ]) 1

#print axioms eventually_rational_landau_error_height_ratio_band
end RiemannResearch.Analysis.ActualZeroOrdinate
