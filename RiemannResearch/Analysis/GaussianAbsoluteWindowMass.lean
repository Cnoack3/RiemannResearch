import RiemannResearch.Analysis.GaussianSpectralWindows

/-!
# Absolute marked unit-window mass

This is an integral-of-norm bound, as needed for Fourier tails. The pointwise
arithmetic-geometric mean inequality consumes the two genuine Gaussian L2
window bounds, uniformly in both centres. It does not replace this mass by
merely the norm of a signed integral.
-/
noncomputable section
open MeasureTheory

namespace RiemannResearch.Analysis.GaussianSpectralWindows

theorem unit_window_energy_Ico_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q b : ℝ) :
    (∫ t in Set.Ico b (b + 1), ‖amplitude s γ q t‖ ^ 2) ≤
      (6 / windowFloor) * squareBudget s γ := by
  rw [← integral_Icc_eq_integral_Ico]
  exact unit_window_energy_le s γ q b

theorem unit_window_marked_Ico_norm_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u b : ℝ) :
    ‖∫ t in Set.Ico b (b + 1),
      amplitude s γ (q + u) t * star (amplitude s γ q t)‖ ≤
        (6 / windowFloor) * squareBudget s γ := by
  rw [← integral_Icc_eq_integral_Ico]
  exact unit_window_marked_norm_le s γ q u b



/-- Literal absolute marked mass in a Lebesgue unit window. -/
theorem unit_window_absolute_marked_mass_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u b : ℝ) :
    (∫ t in Set.Icc b (b + 1),
      ‖amplitude s γ (q + u) t * star (amplitude s γ q t)‖) ≤
        (6 / windowFloor) * squareBudget s γ := by
  have hleft : IntegrableOn (fun t => ‖amplitude s γ (q + u) t‖ ^ 2)
      (Set.Icc b (b + 1)) :=
    (show Continuous (fun t => ‖amplitude s γ (q + u) t‖ ^ 2) by
      unfold amplitude phase; fun_prop).continuousOn.integrableOn_Icc
  have hright : IntegrableOn (fun t => ‖amplitude s γ q t‖ ^ 2)
      (Set.Icc b (b + 1)) :=
    (show Continuous (fun t => ‖amplitude s γ q t‖ ^ 2) by
      unfold amplitude phase; fun_prop).continuousOn.integrableOn_Icc
  have hprod : IntegrableOn
      (fun t => ‖amplitude s γ (q + u) t * star (amplitude s γ q t)‖)
      (Set.Icc b (b + 1)) :=
    (show Continuous
      (fun t => ‖amplitude s γ (q + u) t * star (amplitude s γ q t)‖) by
      unfold amplitude phase; fun_prop).continuousOn.integrableOn_Icc
  have hmono : (∫ t in Set.Icc b (b + 1),
      ‖amplitude s γ (q + u) t * star (amplitude s γ q t)‖) ≤
      (1 / 2 : ℝ) *
        ((∫ t in Set.Icc b (b + 1), ‖amplitude s γ (q + u) t‖ ^ 2) +
          (∫ t in Set.Icc b (b + 1), ‖amplitude s γ q t‖ ^ 2)) := by
    calc
      _ ≤ ∫ t in Set.Icc b (b + 1), (1 / 2 : ℝ) *
          (‖amplitude s γ (q + u) t‖ ^ 2 + ‖amplitude s γ q t‖ ^ 2) := by
        apply integral_mono_ae hprod ((hleft.add hright).const_mul _)
        exact Filter.Eventually.of_forall (fun t => by
          change ‖amplitude s γ (q + u) t * star (amplitude s γ q t)‖ ≤
            (1 / 2 : ℝ) * (‖amplitude s γ (q + u) t‖ ^ 2 + ‖amplitude s γ q t‖ ^ 2)
          rw [norm_mul, norm_star]
          nlinarith [sq_nonneg (‖amplitude s γ (q + u) t‖ - ‖amplitude s γ q t‖)])
      _ = _ := by rw [integral_const_mul, integral_add hleft hright]
  have hl := unit_window_energy_le s γ (q + u) b
  have hr := unit_window_energy_le s γ q b
  linarith

/-- Half-open windows have exactly the same absolute mass as closed windows. -/
theorem unit_window_absolute_marked_Ico_mass_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u b : ℝ) :
    (∫ t in Set.Ico b (b + 1),
      ‖amplitude s γ (q + u) t * star (amplitude s γ q t)‖) ≤
        (6 / windowFloor) * squareBudget s γ := by
  rw [← integral_Icc_eq_integral_Ico]
  exact unit_window_absolute_marked_mass_le s γ q u b

end RiemannResearch.Analysis.GaussianSpectralWindows
