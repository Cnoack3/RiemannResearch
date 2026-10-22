import RiemannResearch.RH.ParetoHiddenConditioningLimit
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Exact change of variables for the hidden-noise conditional norm

The actual geometric transform is related to the rescaled Fermi profile by an
exact one-dimensional change of variables.  Together with dominated convergence,
this gives the conditioned asymptotic with a remaining explicit real integral.
-/

open scoped BigOperators
open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem squareWave_geometricTransform_exp (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) :
    geometricTransform (fun k => squareWave m (k + 1)) (Real.exp (-x / (n : ℝ))) =
      Real.exp (x / (n : ℝ)) / (Real.exp ((m : ℝ) * x / (n : ℝ)) + 1) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : Real.exp (-x / (n : ℝ)) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨Real.exp_pos _, ?_⟩
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hx) hn'
  rw [squareWave_geometricTransform_positive m hm ht]
  have hm' : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, hm']
  have he1 : Real.exp (((m : ℝ) - 1) * (-x / (n : ℝ))) =
      Real.exp (x / (n : ℝ)) * (Real.exp ((m : ℝ) * x / (n : ℝ)))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp ((m : ℝ) * (-x / (n : ℝ))) =
      (Real.exp ((m : ℝ) * x / (n : ℝ)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [he1, he2]
  have he : Real.exp ((m : ℝ) * x / (n : ℝ)) ≠ 0 := by positivity
  have he' : Real.exp ((m : ℝ) * x / (n : ℝ)) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem hiddenNoise_geometricTransform_exp (n : ℕ) (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) :
    geometricTransform (fun k => hiddenNoise n (k + 1)) (Real.exp (-x / (n : ℝ))) =
      Real.exp (x / (n : ℝ)) * hiddenConditioningRescaled n x := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : Real.exp (-x / (n : ℝ)) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨Real.exp_pos _, ?_⟩
    exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos hx) hn')
  have hsplit : geometricTransform (fun k => hiddenNoise n (k + 1))
      (Real.exp (-x / (n : ℝ))) =
      ((n : ℝ) + 2) * geometricTransform (fun k => squareWave (n + 2) (k + 1))
        (Real.exp (-x / (n : ℝ))) -
      (n : ℝ) * geometricTransform (fun k => squareWave n (k + 1))
        (Real.exp (-x / (n : ℝ))) := by
    rw [hiddenNoise_geometricTransform n hn ht,
      squareWave_geometricTransform_positive (n + 2) (by omega) ht,
      squareWave_geometricTransform_positive n hn ht]
    have he : n + 2 - 1 = n + 1 := by omega
    rw [he]
    ring
  rw [hsplit, squareWave_geometricTransform_exp (n + 2) n (by omega) hn hx,
    squareWave_geometricTransform_exp n n hn hn hx]
  have h1 : ((n + 2 : ℕ) : ℝ) * x / (n : ℝ) = (1 + 2 / (n : ℝ)) * x := by
    push_cast
    field_simp
    <;> ring
  have h2 : (n : ℝ) * x / (n : ℝ) = x := by field_simp
  rw [h1, h2]
  unfold hiddenConditioningRescaled hiddenConditioningProfile
  have hd1 : Real.exp ((1 + 2 / (n : ℝ)) * x) + 1 ≠ 0 := by positivity
  have hd2 : Real.exp x + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem hiddenConditioning_substitution_image (n : ℕ) (hn : 0 < n) :
    (fun x : ℝ => Real.exp (-x / (n : ℝ))) '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos hx) hn')
  · intro hy
    refine ⟨-(n : ℝ) * Real.log y, ?_, ?_⟩
    · have hlog := Real.log_neg hy.1 hy.2
      change 0 < -(n : ℝ) * Real.log y
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos hn') hlog
    · have he : -(-(n : ℝ) * Real.log y) / (n : ℝ) = Real.log y := by field_simp
      change Real.exp (-(-(n : ℝ) * Real.log y) / (n : ℝ)) = y
      rw [he, Real.exp_log hy.1]

theorem hiddenNoise_conditioned_norm_substitution (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * (∫ t : ℝ in Set.Ioc 0 1,
      (geometricTransform (fun k => hiddenNoise n (k + 1)) t)^2) =
      ∫ x : ℝ in Set.Ioi 0, hiddenConditioningIntegrand n x := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hderiv (x : ℝ) : HasDerivAt
      (fun x : ℝ => Real.exp (-x / (n : ℝ)))
      (-Real.exp (-x / (n : ℝ)) / (n : ℝ)) x := by
    exact (((hasDerivAt_id x).neg.div_const (n : ℝ)).exp).congr_deriv
      (by simp only [Pi.neg_apply, id_eq]; ring)
  have hinj : Set.InjOn (fun x : ℝ => Real.exp (-x / (n : ℝ))) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have h := Real.exp_injective hxy
    have h' := (div_left_inj' (ne_of_gt hn')).mp h
    linarith
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x _ => (hderiv x).hasDerivWithinAt) hinj
    (fun t => (geometricTransform (fun k => hiddenNoise n (k + 1)) t)^2)
  rw [hiddenConditioning_substitution_image n hn] at hsub
  rw [integral_Ioc_eq_integral_Ioo, hsub, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hnonpos : -Real.exp (-x / (n : ℝ)) / (n : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hn'.le
  rw [smul_eq_mul, abs_of_nonpos hnonpos, hiddenNoise_geometricTransform_exp n hn hx]
  unfold hiddenConditioningIntegrand
  have hneg : -x / (n : ℝ) = -(x / (n : ℝ)) := by ring
  rw [hneg, Real.exp_neg]
  have he : Real.exp (x / (n : ℝ)) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Actual conditioned second moments converge after multiplying by n.
The only unevaluated quantity is the displayed, explicit real integral. -/
theorem hiddenNoise_conditioned_norm_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) * (∫ t : ℝ in Set.Ioc 0 1,
      (geometricTransform (fun k => hiddenNoise n (k + 1)) t)^2)) atTop
      (nhds (4 * ∫ x : ℝ in Set.Ioi 0, hiddenConditioningDerivative x ^ 2)) := by
  apply hiddenConditioning_integral_tendsto.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hiddenNoise_conditioned_norm_substitution n (by omega)).symm

end
end RiemannResearch.RH.Pareto
