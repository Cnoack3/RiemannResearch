/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import RiemannResearch.Analysis.ConsecutivePhaseTaylor

/-!
# Gap-weighted equidistribution for ordinate sequences

The gap-weighted measure has Haar limit from a vanishing squared-gap energy per
unit height. The theorem is deterministic: one-point equidistribution is not a
hypothesis for the gap-weighted law. For actual zeta ordinates, the required
energy input is supplied on paper by Fujii's unconditional gap-moment theorem;
this file does not silently assert that analytic theorem for actual zeta zeros.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ZeroOrdinate

/-- A finite average with nonnegative real weights in its applications. -/
def weightedMean (w : ℕ → ℕ → ℝ) (n : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (w n j : ℂ) * f j

@[simp] theorem weightedMean_zero (w : ℕ → ℕ → ℝ) (n : ℕ) :
    weightedMean w n (fun _ => 0) = 0 := by simp [weightedMean]

@[simp] theorem weightedMean_add (w : ℕ → ℕ → ℝ) (n : ℕ) (f g : ℕ → ℂ) :
    weightedMean w n (fun j => f j + g j) = weightedMean w n f + weightedMean w n g := by
  simp [weightedMean, mul_add, Finset.sum_add_distrib]

@[simp] theorem weightedMean_sub (w : ℕ → ℕ → ℝ) (n : ℕ) (f g : ℕ → ℂ) :
    weightedMean w n (fun j => f j - g j) = weightedMean w n f - weightedMean w n g := by
  simp [weightedMean, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem weightedMean_mul_left (w : ℕ → ℕ → ℝ) (n : ℕ) (c : ℂ) (f : ℕ → ℂ) :
    weightedMean w n (fun j => c * f j) = c * weightedMean w n f := by
  simp only [weightedMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Positivity bounds a weighted average by its total mass. -/
theorem norm_weightedMean_le (w : ℕ → ℕ → ℝ) (n : ℕ)
    (hw : ∀ j, 0 ≤ w n j) (f : ℕ → ℂ) (B : ℝ)
    (hf : ∀ j, ‖f j‖ ≤ B) :
    ‖weightedMean w n f‖ ≤ (∑ j ∈ Finset.range (n + 1), w n j) * B := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), ‖(w n j : ℂ) * f j‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n + 1), w n j * ‖f j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_mul, abs_of_nonneg (hw j)]
    _ ≤ ∑ j ∈ Finset.range (n + 1), w n j * B := by
      exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hf j) (hw j))
    _ = _ := by rw [Finset.sum_mul]

section WeightedDenseTests
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A positive weighted version of the dense-test criterion. Convergence of
the mass replaces exact normalization of every finite average. -/
theorem weighted_converge_of_dense_tests {ι : Type*} (test : ι → C(X, ℂ))
    (hdense : (Submodule.span ℂ (Set.range test)).topologicalClosure = ⊤)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n j, 0 ≤ w n j)
    (hmass : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), w n j) atTop (𝓝 1))
    (samples : ℕ → X) (L : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ f, ‖L f‖ ≤ ‖f‖)
    (htest : ∀ i, Tendsto (fun n => weightedMean w n (fun j => test i (samples j)))
      atTop (𝓝 (L (test i)))) (f : C(X, ℂ)) :
    Tendsto (fun n => weightedMean w n (fun j => f (samples j))) atTop (𝓝 (L f)) := by
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range test),
      Tendsto (fun n => weightedMean w n (fun j => g (samples j))) atTop (𝓝 (L g)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨i, rfl⟩ := hg
        exact htest i
    | zero => simp
    | add g h hg hh ihg ihh =>
        simpa only [ContinuousMap.add_apply, weightedMean_add, map_add] using ihg.add ihh
    | smul c g hg ih =>
        simpa only [ContinuousMap.smul_apply, smul_eq_mul, weightedMean_mul_left,
          map_smul, smul_eq_mul] using ih.const_mul c
  have hmass2 : ∀ᶠ n in atTop, (∑ j ∈ Finset.range (n + 1), w n j) ≤ 2 :=
    hmass.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hmass2
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hf : f ∈ (Submodule.span ℂ (Set.range test)).topologicalClosure := by
    rw [hdense]
    trivial
  change f ∈ closure (Submodule.span ℂ (Set.range test) : Set C(X, ℂ)) at hf
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / 8) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hspan g hg) (ε / 2) (by positivity)
  refine ⟨max M N, fun n hn => ?_⟩
  have havg : ‖weightedMean w n (fun j => f (samples j)) -
      weightedMean w n (fun j => g (samples j))‖ ≤ 2 * ‖f - g‖ := by
    rw [← weightedMean_sub]
    exact (norm_weightedMean_le w n (hw n) _ _
      (fun j => (f - g).norm_coe_le_norm (samples j))).trans
      (mul_le_mul_of_nonneg_right (hM n (le_trans (le_max_left _ _) hn)) (norm_nonneg _))
  have hint : ‖L g - L f‖ ≤ ‖f - g‖ := by
    rw [← map_sub]
    calc
      _ ≤ ‖g - f‖ := hL (g - f)
      _ = _ := norm_sub_rev _ _
  have htri := norm_add_le
    (weightedMean w n (fun j => f (samples j)) - L g) (L g - L f)
  have htri2 := norm_add_le
    (weightedMean w n (fun j => f (samples j)) - weightedMean w n (fun j => g (samples j)))
    (weightedMean w n (fun j => g (samples j)) - L g)
  simp only [sub_add_sub_cancel] at htri htri2
  rw [dist_eq_norm] at hfg ⊢
  have hgn := hN n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm] at hgn
  linarith

end WeightedDenseTests

section WeightedCircle
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Weighted Fourier cancellation and mass convergence imply Haar convergence. -/
theorem weighted_circle_equidistributed_of_fourier
    (times : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (hw : ∀ n j, 0 ≤ w n j)
    (hmass : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), w n j) atTop (𝓝 1))
    (hcancel : ∀ u : ℝ, u ≠ 0 → Tendsto
      (fun n => weightedMean w n (fun j => phase u (times j))) atTop (𝓝 0))
    (α : ℝ) (hα : α ≠ 0) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun n => weightedMean w n
      (fun j => f ((α * times j : ℝ) : AddCircle (1 : ℝ))))
      atTop (𝓝 (∫ x, f x ∂(AddCircle.haarAddCircle (T := 1)))) := by
  apply weighted_converge_of_dense_tests (fourier (T := 1)) span_fourier_closure_eq_top
    w hw hmass (fun j => ((α * times j : ℝ) : AddCircle (1 : ℝ)))
    (probabilityIntegral AddCircle.haarAddCircle) (probabilityIntegral_bound _) _ f
  intro k
  rw [haarIntegral_fourier]
  by_cases hk : k = 0
  · subst k
    simpa [weightedMean, ← Complex.ofReal_sum] using hmass.ofReal
  · have hu : 2 * Real.pi * (k : ℝ) * α ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (by exact_mod_cast hk)) hα
    simpa only [if_neg hk, fourier_sample] using hcancel _ hu

end WeightedCircle

/-- Consecutive gap weights, divided by the sampled height. -/
def gapWeight (times height : ℕ → ℝ) (n j : ℕ) : ℝ :=
  (times (j + 1) - times j) / height n

@[simp] theorem gapWeight_mass (times height : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), gapWeight times height n j) =
      (times (n + 1) - times 0) / height n := by
  simp only [gapWeight, ← Finset.sum_div, Finset.sum_range_sub]

/-- Exact cancellation of sample-count normalization: the ordinary mean of
normalized next gaps is precisely the height-normalized gap-weighted mean. -/
theorem normalized_gap_mean_eq_weightedMean (times height : ℕ → ℝ) (n : ℕ)
    (f : ℕ → ℂ) :
    mean n (fun j =>
      ((((n + 1 : ℕ) : ℝ) / height n * (times (j + 1) - times j) : ℝ) : ℂ) * f j) =
    weightedMean (gapWeight times height) n f := by
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold mean weightedMean gapWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  field_simp

/-- The height-normalized sum representation of gap weights. -/
theorem gapWeightedMean_eq (times height : ℕ → ℝ) (n : ℕ) (f : ℕ → ℂ) :
    weightedMean (gapWeight times height) n f =
      (height n : ℂ)⁻¹ * ∑ j ∈ Finset.range (n + 1),
        ((times (j + 1) - times j : ℝ) : ℂ) * f j := by
  unfold weightedMean gapWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

/-- A quantitative weighted-character bound; no equidistribution input is used. -/
theorem norm_gapWeightedMean_phase_le
    (times height : ℕ → ℝ) (n : ℕ) (hheight : 0 < height n)
    (u : ℝ) (hu : u ≠ 0) :
    ‖weightedMean (gapWeight times height) n (fun j => phase u (times j))‖ ≤
      (2 / |u|) * (height n)⁻¹ + (2 * u ^ 2 / |u|) *
        ((∑ j ∈ Finset.range (n + 1), (times (j + 1) - times j) ^ 2) / height n) := by
  have hphase (t : ℝ) : phase u t = OrdinateLagPhase.phase u t := by
    unfold phase OrdinateLagPhase.phase
    congr 1
    push_cast
    ring
  rw [gapWeightedMean_eq, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hheight]
  simp_rw [hphase]
  calc
    _ ≤ (height n)⁻¹ * ((2 + 2 * u ^ 2 *
        (∑ j ∈ Finset.range (n + 1), (times (j + 1) - times j) ^ 2)) / |u|) :=
      mul_le_mul_of_nonneg_left
        (OrdinateLagPhase.norm_gapWeightedPhaseSum_le times (n + 1) u hu)
        (inv_nonneg.mpr (le_of_lt hheight))
    _ = _ := by ring

/-- Squared-gap energy small relative to height implies cancellation of every
nonzero gap-weighted Fourier mode. This is independent of one-point Weyl
cancellation for the ordinate sequence. -/
theorem gapWeighted_fourierCancellation (times height : ℕ → ℝ)
    (hheight : ∀ n, 0 < height n)
    (hheightTop : Tendsto height atTop atTop)
    (henergy : Tendsto (fun n =>
      (∑ j ∈ Finset.range (n + 1), (times (j + 1) - times j) ^ 2) / height n) atTop (𝓝 0))
    (u : ℝ) (hu : u ≠ 0) :
    Tendsto (fun n => weightedMean (gapWeight times height) n
      (fun j => phase u (times j))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (height n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hheightTop
  have hmajor : Tendsto (fun n =>
      (2 / |u|) * (height n)⁻¹ + (2 * u ^ 2 / |u|) *
        ((∑ j ∈ Finset.range (n + 1), (times (j + 1) - times j) ^ 2) / height n))
      atTop (𝓝 0) := by
    simpa using (hinv.const_mul (2 / |u|)).add (henergy.const_mul (2 * u ^ 2 / |u|))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_gapWeightedMean_phase_le times height n (hheight n) u hu) hmajor

section GapWeightedCircle
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Gap-weighted Haar convergence follows solely from monotonicity, endpoint
normalization, increasing heights and squared-gap energy per height tending to
zero. For zeta ordinates these are unconditional analytic inputs. -/
theorem gapWeighted_circle_equidistributed (times height : ℕ → ℝ)
    (hmono : Monotone times) (hheight : ∀ n, 0 < height n)
    (hheightTop : Tendsto height atTop atTop)
    (hspan : Tendsto (fun n => (times (n + 1) - times 0) / height n) atTop (𝓝 1))
    (henergy : Tendsto (fun n =>
      (∑ j ∈ Finset.range (n + 1), (times (j + 1) - times j) ^ 2) / height n) atTop (𝓝 0))
    (α : ℝ) (hα : α ≠ 0) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun n => weightedMean (gapWeight times height) n
      (fun j => f ((α * times j : ℝ) : AddCircle (1 : ℝ))))
      atTop (𝓝 (∫ x, f x ∂(AddCircle.haarAddCircle (T := 1)))) := by
  apply weighted_circle_equidistributed_of_fourier times (gapWeight times height)
  · intro n j
    exact div_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ j))) (le_of_lt (hheight n))
  · simpa only [gapWeight_mass] using hspan
  · exact gapWeighted_fourierCancellation times height hheight hheightTop henergy
  · exact hα

/-- The mean normalized next gap, tested against the starting phase, has the
Haar mean. This is the continuous-test form of conditional mean independence. -/
theorem normalized_gap_circle_mean (times height : ℕ → ℝ)
    (hmono : Monotone times) (hheight : ∀ n, 0 < height n)
    (hheightTop : Tendsto height atTop atTop)
    (hspan : Tendsto (fun n => (times (n + 1) - times 0) / height n) atTop (𝓝 1))
    (henergy : Tendsto (fun n =>
      (∑ j ∈ Finset.range (n + 1), (times (j + 1) - times j) ^ 2) / height n) atTop (𝓝 0))
    (α : ℝ) (hα : α ≠ 0) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun n => mean n (fun j =>
      ((((n + 1 : ℕ) : ℝ) / height n * (times (j + 1) - times j) : ℝ) : ℂ) *
        f ((α * times j : ℝ) : AddCircle (1 : ℝ))))
      atTop (𝓝 (∫ x, f x ∂(AddCircle.haarAddCircle (T := 1)))) := by
  simp_rw [normalized_gap_mean_eq_weightedMean]
  exact gapWeighted_circle_equidistributed times height hmono hheight hheightTop hspan henergy α hα f

/-- Combining ordinary and gap-weighted Haar convergence annihilates every
continuous starting-phase test against the centered normalized next gap. This
is the exact test-function condition used in conditional-mean independence. -/
theorem centered_normalized_gap_circle_mean (times height : ℕ → ℝ)
    (hmono : Monotone times) (hheight : ∀ n, 0 < height n)
    (hheightTop : Tendsto height atTop atTop)
    (hspan : Tendsto (fun n => (times (n + 1) - times 0) / height n) atTop (𝓝 1))
    (henergy : Tendsto (fun n =>
      (∑ j ∈ Finset.range (n + 1), (times (j + 1) - times j) ^ 2) / height n) atTop (𝓝 0))
    (hcancel : FourierCancellation times)
    (α : ℝ) (hα : α ≠ 0) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun n => mean n (fun j =>
      (((((n + 1 : ℕ) : ℝ) / height n * (times (j + 1) - times j) : ℝ) : ℂ) - 1) *
        f ((α * times j : ℝ) : AddCircle (1 : ℝ)))) atTop (𝓝 0) := by
  have h := (normalized_gap_circle_mean times height hmono hheight hheightTop
    hspan henergy α hα f).sub (circle_equidistributed_of_fourier times hcancel α hα f)
  simpa only [Pi.sub_apply, sub_mul, one_mul, mean_sub, sub_self] using h

/-- Smooth phase selection has limiting conditional normalized next-gap mean
one whenever its Haar mean is nonzero. Positive continuous selection functions
with nonzero Haar integral are a special case. -/
theorem selected_normalized_gap_mean_tendsto_one (times height : ℕ → ℝ)
    (hmono : Monotone times) (hheight : ∀ n, 0 < height n)
    (hheightTop : Tendsto height atTop atTop)
    (hspan : Tendsto (fun n => (times (n + 1) - times 0) / height n) atTop (𝓝 1))
    (henergy : Tendsto (fun n =>
      (∑ j ∈ Finset.range (n + 1), (times (j + 1) - times j) ^ 2) / height n) atTop (𝓝 0))
    (hcancel : FourierCancellation times)
    (α : ℝ) (hα : α ≠ 0) (f : C(AddCircle (1 : ℝ), ℂ))
    (hf : (∫ x, f x ∂(AddCircle.haarAddCircle (T := 1))) ≠ 0) :
    Tendsto (fun n =>
      mean n (fun j =>
        ((((n + 1 : ℕ) : ℝ) / height n * (times (j + 1) - times j) : ℝ) : ℂ) *
          f ((α * times j : ℝ) : AddCircle (1 : ℝ))) /
      mean n (fun j => f ((α * times j : ℝ) : AddCircle (1 : ℝ)))) atTop (𝓝 1) := by
  have h : Tendsto (fun n =>
      mean n (fun j =>
        ((((n + 1 : ℕ) : ℝ) / height n * (times (j + 1) - times j) : ℝ) : ℂ) *
          f ((α * times j : ℝ) : AddCircle (1 : ℝ))) /
      mean n (fun j => f ((α * times j : ℝ) : AddCircle (1 : ℝ)))) atTop
      (𝓝 ((∫ x, f x ∂(AddCircle.haarAddCircle (T := 1))) /
        (∫ x, f x ∂(AddCircle.haarAddCircle (T := 1))))) :=
    (normalized_gap_circle_mean times height hmono hheight hheightTop
      hspan henergy α hα f).div
      (circle_equidistributed_of_fourier times hcancel α hα f) hf
  rw [div_self hf] at h
  exact h

end GapWeightedCircle

end RiemannResearch.Analysis.ZeroOrdinate
