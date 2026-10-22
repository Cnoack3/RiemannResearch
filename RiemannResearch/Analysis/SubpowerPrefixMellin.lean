import RiemannResearch.Analysis.LogarithmicPrefixMellin

-- The private project has no Mathlib Apache license header. This scopes out
-- only that header-format check; theorem verification and other linters remain active.
set_option linter.style.header false in
/-! # Subpower and eventual critical-energy prefix bounds

Source: independently assembled integration-by-parts argument, building on
`LogarithmicPrefixMellin`. The density primitive is retained exactly; its
compact head is only absorbed into the comparison coefficient.

These are generic analytic implications. They do not provide the arithmetic
prefix bounds needed by the RH application.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace MeasureTheory.WeightedMellin

private theorem continuousOn_rpow_Ici_one (r : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ r) (Ici 1) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x r
    (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))).continuousWithinAt

/-- A power bound on the critical energy primitive gives weighted energy
at every strictly larger damping exponent. -/
theorem finiteEnergy_of_prefix_power
    (f : ℝ → ℂ) (hfm : Measurable f) (hfc : ContinuousOn f (Ici 1))
    (C ε s : ℝ) (hs : 1 < s) (hεs : ε < s - 1)
    (hprefix : ∀ X : ℝ, 1 ≤ X →
      (∫ x in (1 : ℝ)..X, ‖f x‖ ^ 2 * x ^ (-2 : ℝ)) ≤ C * X ^ ε) :
    FiniteEnergy f s := by
  have hC : 0 ≤ C := by simpa using hprefix 1 (le_refl 1)
  let g : ℝ → ℝ := fun x => ‖f x‖ ^ 2 * x ^ (-2 : ℝ)
  have hg : ContinuousOn g (Ici 1) :=
    hfc.norm.pow 2 |>.mul (continuousOn_rpow_Ici_one (-2))
  have hg0 : ∀ x ∈ Ici 1, 0 ≤ g x := by
    intro x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx) _)
  have hgi := integrableOn_density_rpow_of_prefix_power
    g hg hg0 C ε (s - 1) hC (by linarith) hεs hprefix
  refine ⟨hfm, hgi.congr_fun ?_ measurableSet_Ioi⟩
  intro x hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  dsimp [g]
  rw [mul_assoc, ← Real.rpow_add hxpos]
  rw [show (-2 : ℝ) + -(s - 1) = -s - 1 by ring]

/-- An eventual power prefix bound suffices: the exact compact head is
absorbed into the coefficient, without imposing a bound at small cutoffs. -/
theorem integrableOn_density_rpow_of_eventual_prefix_power
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici 1))
    (hg0 : ∀ x ∈ Ici 1, 0 ≤ g x)
    (C ε η : ℝ) (hε : 0 ≤ ε)
    (hη : 0 < η) (hεη : ε < η)
    (hprefix : ∀ᶠ X : ℝ in atTop,
      (∫ x in (1 : ℝ)..X, g x) ≤ C * X ^ ε) :
    IntegrableOn (fun x : ℝ => g x * x ^ (-η)) (Ioi 1) := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hprefix
  let Y : ℝ := max 1 X₀
  let H : ℝ := |∫ x in (1 : ℝ)..Y, g x|
  let D : ℝ := max C 0 + H
  have hY : 1 ≤ Y := le_max_left _ _
  have hH : 0 ≤ H := abs_nonneg _
  have hD : 0 ≤ D := add_nonneg (le_max_right _ _) hH
  have hCD : C ≤ D := by
    dsimp [D]
    exact (le_max_left C 0).trans (le_add_of_nonneg_right hH)
  have hbound : ∀ X : ℝ, 1 ≤ X →
      (∫ x in (1 : ℝ)..X, g x) ≤ D * X ^ ε := by
    intro X hX
    by_cases hYX : Y ≤ X
    · have hCX := hX₀ X ((le_max_right _ _).trans hYX)
      exact hCX.trans (mul_le_mul_of_nonneg_right
        hCD (Real.rpow_nonneg (zero_le_one.trans hX) _))
    · have hXY : X ≤ Y := le_of_not_ge hYX
      have hgint : IntervalIntegrable g volume 1 Y :=
        ContinuousOn.intervalIntegrable_of_Icc hY
          (hg.mono Icc_subset_Ici_self)
      have hga : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) Y)] g := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact hg0 x hx.1.le
      have hmono := intervalIntegral.integral_mono_interval
        (le_refl (1 : ℝ)) hX hXY hga hgint
      have hhead : (∫ x in (1 : ℝ)..X, g x) ≤ H :=
        hmono.trans (le_abs_self _)
      have hone : 1 ≤ X ^ ε := Real.one_le_rpow hX hε
      calc
        (∫ x in (1 : ℝ)..X, g x) ≤ H := hhead
        _ ≤ D := by dsimp [D]; linarith [le_max_right C 0]
        _ = D * 1 := (mul_one D).symm
        _ ≤ D * X ^ ε := mul_le_mul_of_nonneg_left hone hD
  exact integrableOn_density_rpow_of_prefix_power
    g hg hg0 D ε η hD hη hεη hbound

/-- Eventual control of the critical energy primitive suffices for finite
Mellin energy. The bound is needed only after some real cutoff. -/
theorem finiteEnergy_of_eventual_prefix_power
    (f : ℝ → ℂ) (hfm : Measurable f) (hfc : ContinuousOn f (Ici 1))
    (C ε s : ℝ) (hε : 0 ≤ ε)
    (hs : 1 < s) (hεs : ε < s - 1)
    (hprefix : ∀ᶠ X : ℝ in atTop,
      (∫ x in (1 : ℝ)..X, ‖f x‖ ^ 2 * x ^ (-2 : ℝ)) ≤ C * X ^ ε) :
    FiniteEnergy f s := by
  let g : ℝ → ℝ := fun x => ‖f x‖ ^ 2 * x ^ (-2 : ℝ)
  have hg : ContinuousOn g (Ici 1) :=
    hfc.norm.pow 2 |>.mul (continuousOn_rpow_Ici_one (-2))
  have hg0 : ∀ x ∈ Ici 1, 0 ≤ g x := by
    intro x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx) _)
  have hgi := integrableOn_density_rpow_of_eventual_prefix_power
    g hg hg0 C ε (s - 1) hε (by linarith) hεs hprefix
  refine ⟨hfm, hgi.congr_fun ?_ measurableSet_Ioi⟩
  intro x hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  dsimp [g]
  rw [mul_assoc, ← Real.rpow_add hxpos]
  rw [show (-2 : ℝ) + -(s - 1) = -s - 1 by ring]

/-- A finite weighted energy controls every weaker finite prefix, with the exact
comparison coefficient `X ^ (s - u)`. No continuity is needed. -/
theorem finiteEnergy_prefix_rpow_le {f : ℝ → ℂ} {s u : ℝ}
    (hf : FiniteEnergy f s) (hus : u ≤ s) {X : ℝ} (hX : 1 ≤ X) :
    IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2 * x ^ (-u - 1)) volume 1 X ∧
      (∫ x in (1 : ℝ)..X, ‖f x‖ ^ 2 * x ^ (-u - 1)) ≤
        X ^ (s - u) * energy f s := by
  have hsub : Ioc (1 : ℝ) X ⊆ Ioi 1 := fun _ hx => hx.1
  have hbase : IntegrableOn
      (fun x : ℝ => ‖f x‖ ^ 2 * x ^ (-s - 1)) (Ioc 1 X) := hf.2.mono_set hsub
  have hpoint : ∀ x ∈ Ioc (1 : ℝ) X,
      ‖f x‖ ^ 2 * x ^ (-u - 1) ≤
        X ^ (s - u) * (‖f x‖ ^ 2 * x ^ (-s - 1)) := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx.1
    calc
      ‖f x‖ ^ 2 * x ^ (-u - 1) =
          (‖f x‖ ^ 2 * x ^ (-s - 1)) * x ^ (s - u) := by
        rw [show -u - 1 = (-s - 1) + (s - u) by ring, Real.rpow_add hx0]
        ring
      _ ≤ (‖f x‖ ^ 2 * x ^ (-s - 1)) * X ^ (s - u) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hx0.le hx.2 (sub_nonneg.mpr hus))
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx0.le _))
      _ = _ := by ring
  have hlocal : IntegrableOn
      (fun x : ℝ => ‖f x‖ ^ 2 * x ^ (-u - 1)) (Ioc 1 X) := by
    apply (hbase.const_mul (X ^ (s - u))).mono'
      ((hf.1.norm.pow_const 2).mul (measurable_id.pow_const _)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change ‖‖f x‖ ^ 2 * x ^ (-u - 1)‖ ≤
      X ^ (s - u) * (‖f x‖ ^ 2 * x ^ (-s - 1))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hx.1]) _))]
    exact hpoint x hx
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2 hlocal, ?_⟩
  rw [intervalIntegral.integral_of_le hX]
  calc
    (∫ x in Ioc (1 : ℝ) X, ‖f x‖ ^ 2 * x ^ (-u - 1)) ≤
        ∫ x in Ioc (1 : ℝ) X,
          X ^ (s - u) * (‖f x‖ ^ 2 * x ^ (-s - 1)) := by
      apply integral_mono_ae hlocal (hbase.const_mul (X ^ (s - u)))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hpoint x hx
    _ = X ^ (s - u) *
        (∫ x in Ioc (1 : ℝ) X, ‖f x‖ ^ 2 * x ^ (-s - 1)) := integral_const_mul _ _
    _ ≤ X ^ (s - u) * energy f s := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (zero_le_one.trans hX) _)
      apply setIntegral_mono_set hf.2
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx.le) _)
      · exact Filter.Eventually.of_forall (fun x hx => hx.1)

/-- Weighted energy is nonnegative, including when the Bochner integral is
defined to be zero because integrability has not yet been established. -/
theorem energy_nonneg (f : ℝ → ℂ) (s : ℝ) : 0 ≤ energy f s := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx.le) _)

/-- Finite energy at `s ≥ 1` controls the critical prefix at every real cutoff. -/
theorem critical_prefix_le_energy {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (hs : 1 ≤ s) {X : ℝ} (hX : 1 ≤ X) :
    (∫ x in (1 : ℝ)..X, ‖f x‖ ^ 2 * x ^ (-2 : ℝ)) ≤
      energy f s * X ^ (s - 1) := by
  simpa only [show -(1 : ℝ) - 1 = -2 by norm_num, mul_comm] using
    (finiteEnergy_prefix_rpow_le hf hs hX).2

end MeasureTheory.WeightedMellin
