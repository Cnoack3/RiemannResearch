/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.SupportL2Bound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Compact-kernel quadratic continuity
Real bounded-kernel quadratic forms are continuous along L2-convergent sequences
with a common compact support window. Positivity transfers only under an explicit
positivity hypothesis on the approximating tests.
Source: user-provided RH_Local_to_Global_Trace_Attack_Plan_2026-09-05.pdf,
page 4, supports the continuity and conditional dense-test transfer strategy.
RH consumer: passage from exact dyadic Haar compressions to local real tests.
No arithmetic positivity, Weil identity, or RH assertion is supplied here.
-/

open MeasureTheory Set Filter
namespace RiemannResearch.Analysis

/-- The actual full-line real bilinear integral, with no normalization. -/
noncomputable def realKernelBilinear (k : ℝ → ℝ → ℝ) (u v : ℝ → ℝ) : ℝ :=
  ∫ x, u x * (∫ y, k x y * v y)

/-- The diagonal of the actual bilinear integral. -/
noncomputable def realKernelQuadratic (k : ℝ → ℝ → ℝ) (u : ℝ → ℝ) : ℝ :=
  realKernelBilinear k u u

/-- Compact support and a bounded measurable kernel give absolute product integrability. -/
theorem integrable_realKernel_product
    {k : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {S : Set ℝ} {C : ℝ}
    (hS : MeasurableSet S) (hC : 0 ≤ C) (hk : Measurable (Function.uncurry k))
    (hbound : ∀ x ∈ S, ∀ y ∈ S, ‖k x y‖ ≤ C)
    (hu : Integrable u) (hv : Integrable v)
    (hus : ∀ x ∉ S, u x = 0) (hvs : ∀ x ∉ S, v x = 0) :
    Integrable (fun p : ℝ × ℝ => u p.1 * k p.1 p.2 * v p.2)
      (volume.prod volume) := by
  let K : ℝ × ℝ → ℝ := (S ×ˢ S).indicator (Function.uncurry k)
  have hK : AEStronglyMeasurable K (volume.prod volume) :=
    (hk.indicator (hS.prod hS)).aestronglyMeasurable
  have hKb : ∀ p, ‖K p‖ ≤ C := by
    intro p
    by_cases hp : p ∈ S ×ˢ S
    · simpa [K, hp, Function.uncurry] using hbound p.1 hp.1 p.2 hp.2
    · simpa [K, hp] using hC
  have h := (hu.mul_prod hv).mul_bdd hK (Eventually.of_forall hKb)
  convert h using 1
  ext p
  by_cases hx : p.1 ∈ S
  · by_cases hy : p.2 ∈ S
    · simp [K, hx, hy, Function.uncurry]
      ring
    · simp [hvs p.2 hy]
  · simp [hus p.1 hx]

/-- Fubini identifies the actual iterated form; product integrability is explicit. -/
theorem realKernelBilinear_eq_product
    {k : ℝ → ℝ → ℝ} {u v : ℝ → ℝ}
    (h : Integrable (fun p : ℝ × ℝ => u p.1 * k p.1 p.2 * v p.2)
      (volume.prod volume)) :
    realKernelBilinear k u v =
      ∫ p : ℝ × ℝ, u p.1 * k p.1 p.2 * v p.2 ∂volume.prod volume := by
  rw [integral_prod _ h]
  simp only [realKernelBilinear, mul_assoc, integral_const_mul]

/-- The outer integrand of the full-line form is integrable. -/
theorem integrable_realKernel_outer
    {k : ℝ → ℝ → ℝ} {u v : ℝ → ℝ}
    (h : Integrable (fun p : ℝ × ℝ => u p.1 * k p.1 p.2 * v p.2)
      (volume.prod volume)) :
    Integrable (fun x => u x * (∫ y, k x y * v y)) := by
  simpa only [mul_assoc, integral_const_mul] using h.integral_prod_left

/-- The exact L1 operator bound, valid also for empty and null support sets. -/
theorem norm_realKernelBilinear_le
    {k : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {S : Set ℝ} {C : ℝ}
    (hS : MeasurableSet S) (hC : 0 ≤ C) (hk : Measurable (Function.uncurry k))
    (hbound : ∀ x ∈ S, ∀ y ∈ S, ‖k x y‖ ≤ C)
    (hu : Integrable u) (hv : Integrable v)
    (hus : ∀ x ∉ S, u x = 0) (hvs : ∀ x ∉ S, v x = 0) :
    ‖realKernelBilinear k u v‖ ≤ C * (∫ x, ‖u x‖) * (∫ y, ‖v y‖) := by
  rw [realKernelBilinear_eq_product
    (integrable_realKernel_product hS hC hk hbound hu hv hus hvs)]
  calc
    _ ≤ ∫ p : ℝ × ℝ, C * (‖u p.1‖ * ‖v p.2‖) ∂volume.prod volume := by
      apply norm_integral_le_of_norm_le ((hu.norm.mul_prod hv.norm).const_mul C)
      apply Eventually.of_forall
      intro p
      by_cases hx : p.1 ∈ S
      · by_cases hy : p.2 ∈ S
        · simp only [norm_mul]
          nlinarith [mul_le_mul_of_nonneg_left (hbound p.1 hx p.2 hy)
            (mul_nonneg (norm_nonneg (u p.1)) (norm_nonneg (v p.2)))]
        · simp [hvs p.2 hy]
      · simp [hus p.1 hx]
    _ = _ := by rw [integral_const_mul, integral_prod_mul (fun x => ‖u x‖) (fun y => ‖v y‖)]; ring

/-- Difference of quadratic forms is the sum of two cross terms; symmetry is unnecessary. -/
theorem realKernelQuadratic_sub
    {k : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {S : Set ℝ} {C : ℝ}
    (hS : MeasurableSet S) (hC : 0 ≤ C) (hk : Measurable (Function.uncurry k))
    (hbound : ∀ x ∈ S, ∀ y ∈ S, ‖k x y‖ ≤ C)
    (hu : Integrable u) (hv : Integrable v)
    (hus : ∀ x ∉ S, u x = 0) (hvs : ∀ x ∉ S, v x = 0) :
    realKernelQuadratic k v - realKernelQuadratic k u =
      realKernelBilinear k (fun x => v x - u x) v +
      realKernelBilinear k u (fun x => v x - u x) := by
  have hds : ∀ x ∉ S, v x - u x = 0 := by
    intro x hx
    simp [hus x hx, hvs x hx]
  have hprod {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
      (hfs : ∀ x ∉ S, f x = 0) (hgs : ∀ x ∉ S, g x = 0) :=
    integrable_realKernel_product hS hC hk hbound hf hg hfs hgs
  change realKernelBilinear k v v - realKernelBilinear k u u =
    realKernelBilinear k (v - u) v + realKernelBilinear k u (v - u)
  rw [realKernelBilinear_eq_product (hprod hv hv hvs hvs),
    realKernelBilinear_eq_product (hprod hu hu hus hus),
    realKernelBilinear_eq_product (hprod (hv.sub hu) hv hds hvs),
    realKernelBilinear_eq_product (hprod hu (hv.sub hu) hus hds),
    ← integral_sub (hprod hv hv hvs hvs) (hprod hu hu hus hus),
    ← integral_add (hprod (hv.sub hu) hv hds hvs) (hprod hu (hv.sub hu) hus hds)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by dsimp; ring)

/-- Quantitative L1 continuity with the standard two cross-term factors. -/
theorem norm_realKernelQuadratic_sub_le
    {k : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {S : Set ℝ} {C : ℝ}
    (hS : MeasurableSet S) (hC : 0 ≤ C) (hk : Measurable (Function.uncurry k))
    (hbound : ∀ x ∈ S, ∀ y ∈ S, ‖k x y‖ ≤ C)
    (hu : Integrable u) (hv : Integrable v)
    (hus : ∀ x ∉ S, u x = 0) (hvs : ∀ x ∉ S, v x = 0) :
    ‖realKernelQuadratic k v - realKernelQuadratic k u‖ ≤
      C * (∫ x, ‖v x - u x‖) * ((∫ x, ‖v x‖) + (∫ x, ‖u x‖)) := by
  have hds : ∀ x ∉ S, v x - u x = 0 := by
    intro x hx
    simp [hus x hx, hvs x hx]
  rw [realKernelQuadratic_sub hS hC hk hbound hu hv hus hvs]
  calc
    _ ≤ ‖realKernelBilinear k (fun x => v x - u x) v‖ +
        ‖realKernelBilinear k u (fun x => v x - u x)‖ := norm_add_le _ _
    _ ≤ C * (∫ x, ‖v x - u x‖) * (∫ x, ‖v x‖) +
        C * (∫ x, ‖u x‖) * (∫ x, ‖v x - u x‖) :=
      add_le_add
        (norm_realKernelBilinear_le hS hC hk hbound (hv.sub hu) hv hds hvs)
        (norm_realKernelBilinear_le hS hC hk hbound hu (hv.sub hu) hus hds)
    _ = _ := by ring


/-- The sharp support-length Cauchy bound in square-root form, including R = 0. -/
theorem integral_norm_le_sqrt_support_mul_integral_sq
    {u : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R) (hu : Integrable u)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0) :
    (∫ x, ‖u x‖) ≤ Real.sqrt (2 * R * (∫ x, u x ^ 2)) :=
  Real.le_sqrt_of_sq_le
    (integral_norm_sq_le_support_length_mul_integral_sq hR hu hu2 hus)

/-- A quantitative L2 bound, expressed with square integrals and exact support length. -/
theorem norm_realKernelQuadratic_sub_le_l2
    {k : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hk : Measurable (Function.uncurry k))
    (hbound : ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R, ‖k x y‖ ≤ C)
    (hu : Integrable u) (hv : Integrable v)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hv2 : Integrable (fun x => v x ^ 2))
    (hd2 : Integrable (fun x => (v x - u x) ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hvs : ∀ x ∉ Icc (-R) R, v x = 0) :
    ‖realKernelQuadratic k v - realKernelQuadratic k u‖ ≤
      C * Real.sqrt (2 * R * (∫ x, (v x - u x) ^ 2)) *
        (Real.sqrt (2 * R * (∫ x, v x ^ 2)) +
          Real.sqrt (2 * R * (∫ x, u x ^ 2))) := by
  have hds : ∀ x ∉ Icc (-R) R, v x - u x = 0 := by
    intro x hx
    simp [hus x hx, hvs x hx]
  apply (norm_realKernelQuadratic_sub_le measurableSet_Icc hC hk hbound hu hv hus hvs).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (integral_norm_le_sqrt_support_mul_integral_sq hR (hv.sub hu) hd2 hds) hC
  · exact add_le_add
      (integral_norm_le_sqrt_support_mul_integral_sq hR hv hv2 hvs)
      (integral_norm_le_sqrt_support_mul_integral_sq hR hu hu2 hus)
  · positivity
  · positivity

/-- Square-integral convergence on a fixed support window implies L1 convergence. -/
theorem tendsto_integral_norm_of_tendsto_integral_sq
    {f : ℕ → ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ n, Integrable (f n))
    (hf2 : ∀ n, Integrable (fun x => f n x ^ 2))
    (hfs : ∀ n, ∀ x ∉ Icc (-R) R, f n x = 0)
    (hlim : Tendsto (fun n => ∫ x, f n x ^ 2) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, ‖f n x‖) atTop (nhds 0) := by
  have ht : Tendsto (fun n => Real.sqrt (2 * R * (∫ x, f n x ^ 2)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (2 * R * 0)).comp (hlim.const_mul (2 * R))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => integral_nonneg (fun x => norm_nonneg _))
    (fun n => integral_norm_le_sqrt_support_mul_integral_sq hR (hf n) (hf2 n) (hfs n))

/-- L2 convergence implies quadratic convergence for a bounded measurable kernel.
The only square-integrability assumptions needed here concern the differences. -/
theorem tendsto_realKernelQuadratic_of_tendsto_integral_sq
    {k : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hk : Measurable (Function.uncurry k))
    (hbound : ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R, ‖k x y‖ ≤ C)
    (hu : Integrable u) (hv : ∀ n, Integrable (v n))
    (hd2 : ∀ n, Integrable (fun x => (v n x - u x) ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hvs : ∀ n, ∀ x ∉ Icc (-R) R, v n x = 0)
    (hlim : Tendsto (fun n => ∫ x, (v n x - u x) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n => realKernelQuadratic k (v n)) atTop
      (nhds (realKernelQuadratic k u)) := by
  have hds : ∀ n, ∀ x ∉ Icc (-R) R, v n x - u x = 0 := by
    intro n x hx
    simp [hus x hx, hvs n x hx]
  have hL1 := tendsto_integral_norm_of_tendsto_integral_sq hR
    (fun n => (hv n).sub hu) hd2 hds hlim
  have hvnorm (n : ℕ) :
      (∫ x, ‖v n x‖) ≤ (∫ x, ‖v n x - u x‖) + (∫ x, ‖u x‖) := by
    rw [← integral_add (f := fun x => ‖v n x - u x‖) (g := fun x => ‖u x‖)
      ((hv n).sub hu).norm hu.norm]
    apply integral_mono (hv n).norm (((hv n).sub hu).norm.add hu.norm)
    intro x
    change ‖v n x‖ ≤ ‖v n x - u x‖ + ‖u x‖
    simpa only [sub_add_cancel] using norm_add_le (v n x - u x) (u x)
  have hmajor : Tendsto
      (fun n => C * (∫ x, ‖v n x - u x‖) *
        ((∫ x, ‖v n x - u x‖) + 2 * (∫ x, ‖u x‖))) atTop (nhds 0) := by
    simpa using (hL1.const_mul C).mul (hL1.add_const (2 * (∫ x, ‖u x‖)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun n => norm_nonneg _)
  intro n
  apply (norm_realKernelQuadratic_sub_le measurableSet_Icc hC hk hbound hu (hv n)
    hus (hvs n)).trans
  apply mul_le_mul_of_nonneg_left
  · linarith [hvnorm n]
  · positivity



/-- For a continuous kernel, each inner integral is absolutely integrable, even when
the fixed outer point is outside the common support window. -/
theorem integrable_realKernel_inner_of_continuous
    {k : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {R : ℝ}
    (hk : Continuous (Function.uncurry k)) (hv : Integrable v)
    (hvs : ∀ y ∉ Icc (-R) R, v y = 0) (x : ℝ) :
    Integrable (fun y => k x y * v y) := by
  have hkx : Continuous (fun y => k x y) :=
    hk.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
      hkx.continuousOn
  apply (hv.norm.const_mul (max C 0)).mono'
    (hkx.aestronglyMeasurable.mul hv.aestronglyMeasurable)
  apply Eventually.of_forall
  intro y
  change ‖k x y * v y‖ ≤ max C 0 * ‖v y‖
  by_cases hy : y ∈ Icc (-R) R
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hC y hy).trans (le_max_left _ _)) (norm_nonneg _)
  · simp [hvs y hy]

/-- Joint continuity supplies the uniform bound on the compact square. -/
theorem tendsto_realKernelQuadratic_of_continuous
    {k : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hk : Continuous (Function.uncurry k))
    (hu : Integrable u) (hv : ∀ n, Integrable (v n))
    (hd2 : ∀ n, Integrable (fun x => (v n x - u x) ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hvs : ∀ n, ∀ x ∉ Icc (-R) R, v n x = 0)
    (hlim : Tendsto (fun n => ∫ x, (v n x - u x) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n => realKernelQuadratic k (v n)) atTop
      (nhds (realKernelQuadratic k u)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-R) R ×ˢ Icc (-R) R) hk.continuousOn
  apply tendsto_realKernelQuadratic_of_tendsto_integral_sq hR (le_max_right C 0)
    hk.measurable _ hu hv hd2 hus hvs hlim
  intro x hx y hy
  exact (hC (x,y) ⟨hx,hy⟩).trans (le_max_left _ _)

/-- Conditional positivity passage. No positivity of any arithmetic kernel is inferred
unless the caller proves the explicitly quantified approximating-test hypothesis. -/
theorem realKernelQuadratic_nonneg_of_approx
    {k : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hk : Continuous (Function.uncurry k))
    (hu : Integrable u) (hv : ∀ n, Integrable (v n))
    (hd2 : ∀ n, Integrable (fun x => (v n x - u x) ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hvs : ∀ n, ∀ x ∉ Icc (-R) R, v n x = 0)
    (hlim : Tendsto (fun n => ∫ x, (v n x - u x) ^ 2) atTop (nhds 0))
    (hpos : ∀ n, 0 ≤ realKernelQuadratic k (v n)) :
    0 ≤ realKernelQuadratic k u :=
  ge_of_tendsto
    (tendsto_realKernelQuadratic_of_continuous hR hk hu hv hd2 hus hvs hlim)
    (Eventually.of_forall hpos)

/-- Dense-test positivity transfer on the exact mean-zero support window.
Density and positivity are separate hypotheses; neither is postulated by a definition
of the arithmetic form. All L1, L2, support, and mean-zero requirements are explicit. -/
theorem realKernelQuadratic_nonneg_of_meanZero_L2_dense
    {k : ℝ → ℝ → ℝ} {D : Set (ℝ → ℝ)} {R : ℝ}
    (hR : 0 ≤ R) (hk : Continuous (Function.uncurry k))
    (hD : ∀ v ∈ D, Integrable v ∧
      (∀ x ∉ Icc (-R) R, v x = 0) ∧ (∫ x, v x) = 0)
    (hdense : ∀ u : ℝ → ℝ, Integrable u →
      Integrable (fun x => u x ^ 2) →
      (∀ x ∉ Icc (-R) R, u x = 0) → (∫ x, u x) = 0 →
      ∃ v : ℕ → ℝ → ℝ, (∀ n, v n ∈ D) ∧
        (∀ n, Integrable (fun x => (v n x - u x) ^ 2)) ∧
        Tendsto (fun n => ∫ x, (v n x - u x) ^ 2) atTop (nhds 0))
    (hpos : ∀ v ∈ D, 0 ≤ realKernelQuadratic k v)
    {u : ℝ → ℝ} (hu : Integrable u)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0) (hu0 : (∫ x, u x) = 0) :
    0 ≤ realKernelQuadratic k u := by
  obtain ⟨v, hvD, hv2, hlim⟩ := hdense u hu hu2 hus hu0
  exact realKernelQuadratic_nonneg_of_approx hR hk hu
    (fun n => (hD (v n) (hvD n)).1) hv2 hus
    (fun n => (hD (v n) (hvD n)).2.1) hlim
    (fun n => hpos (v n) (hvD n))

end RiemannResearch.Analysis
