import RiemannResearch.Analysis.WeightedMellinBoundary

/-!
# Endpoint energy recovery and the general Hardy converse obligation

Source: user-requested continuation of
RH_Energy_Holomorphy_Hardy_Implications_2026-09-18.md.
Fatou's lemma recovers endpoint energy from bounded interior energies.
Consequently a represented Mellin transform with all interior energies finite
is Hardy H2 exactly when its endpoint energy is finite.

GeneralHardyConverse states the still-unproved-in-this-project classical
Paley--Wiener representation theorem as a Prop, not an axiom.
The final boundary theorem explicitly assumes this proposition. It must not
be reported as an unconditional theorem for arbitrary Hardy functions.
-/

set_option autoImplicit false
open MeasureTheory Set Filter FourierTransform
open scoped Topology
noncomputable section
namespace MeasureTheory.WeightedMellin

theorem finiteEnergy_of_bounded_approximating_energies {f : ℝ → ℂ} {s C : ℝ}
    {u : ℕ → ℝ} (hu : ∀ n, s ≤ u n)
    (hlim : Tendsto u atTop (𝓝 s))
    (hf : ∀ n, FiniteEnergy f (u n)) (hb : ∀ n, energy f (u n) ≤ C) :
    FiniteEnergy f s ∧ energy f s ≤ C := by
  let μ : Measure ℝ := volume.restrict (Ioi (1 : ℝ))
  let G : ℕ → ℝ → ℝ := fun n x => ‖f x‖ ^ 2 * x ^ (-u n - 1)
  have hi (n : ℕ) : Integrable (G n) μ := (hf n).2
  have hn (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ G n x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans zero_le_one hx.le) _)
  have hB (n : ℕ) : (∫⁻ x, ‖G n x‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    apply ENNReal.ofReal_le_ofReal
    have he : (∫ x, ‖G n x‖ ∂μ) = energy f (u n) := by
      apply integral_congr_ae
      filter_upwards [hn n] with x hx
      exact Real.norm_of_nonneg hx
    rw [he]
    exact hb n
  have hL : liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C := by
    exact Filter.liminf_le_of_frequently_le
      (Filter.Eventually.of_forall hB).frequently
      ⟨0, Filter.Eventually.of_forall (fun _ => bot_le)⟩
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop
      (𝓝 (‖f x‖ ^ 2 * x ^ (-s - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    exact tendsto_const_nhds.mul
      ((Real.continuous_const_rpow hx0.ne').continuousAt.tendsto.comp
        (hlim.neg.sub_const 1))
  have hfs : FiniteEnergy f s := ⟨(hf 0).1,
    integrable_of_tendsto ht (fun n => (hi n).aestronglyMeasurable)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL)⟩
  exact ⟨hfs, le_of_tendsto (energy_tendsto hfs hu hlim)
    (Filter.Eventually.of_forall hb)⟩

theorem finiteEnergy_of_hardy_interior {f : ℝ → ℂ} {s : ℝ}
    (hi : ∀ u : ℝ, s < u → FiniteEnergy f u)
    (hH : HardyH2 (transform f) (s / 2)) : FiniteEnergy f s := by
  obtain ⟨C, hC⟩ := hH.2.2
  let u : ℕ → ℝ := fun n => s + 1 / ((n : ℝ) + 1)
  have hu : ∀ n, s < u n := by
    intro n
    have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    dsimp [u]; linarith
  have ht : Tendsto u atTop (𝓝 s) := by
    simpa [u] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply (finiteEnergy_of_bounded_approximating_energies (C := C)
    (fun n => (hu n).le) ht (fun n => hi (u n) (hu n)) ?_).1
  intro n
  have he := vertical_plancherel (hi ((s + u n) / 2) (by linarith [hu n]))
    (σ := u n / 2) (by linarith [hu n])
  have hb := hC (u n / 2) (by linarith [hu n])
  rw [he] at hb
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hb

/-- Within the class already having all interior weighted energies,
Hardy membership is equivalent to endpoint finite energy. -/
theorem finiteEnergy_iff_hardy_of_interior {f : ℝ → ℂ} {s : ℝ}
    (hi : ∀ u : ℝ, s < u → FiniteEnergy f u) :
    FiniteEnergy f s ↔ HardyH2 (transform f) (s / 2) :=
  ⟨energy_to_hardy, finiteEnergy_of_hardy_interior hi⟩

/-- OPEN classical Paley--Wiener representation obligation.
This definition is a proposition, not an axiom or a proof. -/
def GeneralHardyConverse : Prop :=
  ∀ (α : ℝ) (F : ℂ → ℂ), HardyH2 F α →
    ∃ f : ℝ → ℂ, FiniteEnergy f (2 * α) ∧
      ∀ z : ℂ, α < z.re → transform f z = F z

/-- If the open general representation obligation is discharged, boundary
convergence for every Hardy function follows from the proved Mellin case. -/
theorem hardy_boundary_of_general_converse (hPW : GeneralHardyConverse)
    {F : ℂ → ℂ} {α : ℝ} (hF : HardyH2 F α) :
    ∃ B : Lp ℂ 2 (volume : Measure ℝ),
      ∀ (σ : ℕ → ℝ), (∀ n, α < σ n) → Tendsto σ atTop (𝓝 α) →
        Tendsto (fun n => ∫ w : ℝ, ‖F (verticalPoint (σ n) w) - B w‖ ^ 2)
          atTop (𝓝 0) := by
  obtain ⟨f, hf, he⟩ := hPW α F hF
  refine ⟨boundaryTrace hf, ?_⟩
  intro σ hσ ht
  have hh : (2 * α) / 2 = α := by ring
  have hb := transform_boundary_integral hf
    (σ := σ) (by simpa only [hh] using hσ) (by simpa only [hh] using ht)
  have hv (n : ℕ) (w : ℝ) :
      transform f (verticalPoint (σ n) w) = F (verticalPoint (σ n) w) :=
    he _ (by simpa [verticalPoint] using hσ n)
  simpa only [hv] using hb

end MeasureTheory.WeightedMellin
