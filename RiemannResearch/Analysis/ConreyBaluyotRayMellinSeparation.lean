/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGaussianPoleReduction
import RiemannResearch.Analysis.ConreyBaluyotEstermannActualGrowth
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The shifted Mellin formula integrated on each actual Gaussian ray

Baluyot, *On the Zeros of Riemann's Zeta-function* (2017), §3.3, rotates and
shifts the Gaussian transform. The existing angle-independence theorem permits
the right angle. There the imaginary part of the Mellin damping has constant
absolute value. Its negative real powers are bounded over the whole ray.
Consequently the residue and residual vertical integral are separately
integrable after Gaussian weighting. This is a fixed-parameter identity.
-/

noncomputable section
open Complex MeasureTheory Filter Set ENNReal
open scoped ENNReal

namespace RiemannResearch.Analysis.ConreyBaluyot

private theorem integrable_complex_tsum {ι X : Type*} [Countable ι]
    [MeasurableSpace X] {μ : Measure X} {F : ι → X → ℂ}
    (hf : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ x, ‖F i x‖ ∂μ) :
    Integrable (fun x => ∑' i, F i x) μ := by
  refine ⟨(AEStronglyMeasurable.tsum (fun i => (hf i).1)), ?_⟩
  have hc (i : ι) : ∫⁻ x, ‖F i x‖ₑ ∂μ = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hf i).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F i x))]
    simp only [coe_nnnorm]
  apply lt_of_le_of_lt (lintegral_mono
    (fun x : X => enorm_tsum_le_tsum_enorm (f := fun i => F i x)))
  rw [lintegral_tsum (fun i => (hf i).1.enorm), funext hc, lt_top_iff_ne_top]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)

/-- Right-angle damping on the two outward rays. -/
def orthogonalRayDamping (a τ r : ℝ) : ℂ :=
  ((2 * Real.pi * a : ℝ) : ℂ) * ((r : ℂ) + (τ : ℂ) * I)

private theorem orthogonalRayDamping_eq (a r : ℝ) {τ : ℝ} (ht : τ = 1 ∨ τ = -1) :
    -2 * (Real.pi : ℂ) * I * estermannRayArgument a τ (Real.pi/2) r =
      orthogonalRayDamping a τ r := by
  have he : Complex.exp ((((τ * (Real.pi / 2)) : ℝ) : ℂ) * I) = (τ : ℂ) * I := by
    rcases ht with rfl | rfl
    · simp
    · simp [neg_mul, Complex.exp_neg]
  unfold orthogonalRayDamping estermannRayArgument
  rw [he]
  rcases ht with rfl | rfl <;> push_cast <;>
    ring_nf <;> simp

private theorem orthogonalRayDamping_bounds {a τ : ℝ} (ha : 0 < a)
    (hτ : τ = 1 ∨ τ = -1) {r : ℝ} (hr : 0 < r) :
    0 < (orthogonalRayDamping a τ r).re ∧
      2 * Real.pi * a ≤ ‖orthogonalRayDamping a τ r‖ := by
  have hre : (orthogonalRayDamping a τ r).re = (2*Real.pi*a)*r := by
    simp [orthogonalRayDamping, Complex.mul_re]
  have him : |(orthogonalRayDamping a τ r).im| = 2*Real.pi*a := by
    rcases hτ with rfl | rfl <;>
      simp [orthogonalRayDamping, Complex.mul_im, abs_of_pos ha, abs_of_pos Real.pi_pos]
  exact ⟨hre ▸ mul_pos (by positivity) hr, him ▸ Complex.abs_im_le_norm _⟩

private theorem integrableOn_gaussian_mul_orthogonal_residue {K : ℕ} [NeZero K]
    (h : ZMod K) (l u x y : ℝ) (hx : x ≤ 1) (hy : y ≤ 1) {Δ a τ : ℝ}
    (hΔ : 0 < Δ) (ha : 0 < a) (ht : τ = 1 ∨ τ = -1) :
    IntegrableOn (fun r =>
      gaussianRayIntegrand l Δ u 0 (τ*(Real.pi/2)) r *
        estermannMellinResidueSum h (x : ℂ) (y : ℂ) (orthogonalRayDamping a τ r)) (Ioi 0) := by
  let G := gaussianRayIntegrand l Δ u 0 (τ*(Real.pi/2))
  let D := orthogonalRayDamping a τ
  have hG : IntegrableOn G (Ioi 0) := by
    simpa [G] using gaussianRayIntegrand_integrable l u hΔ (le_refl (0:ℝ))
      (show Real.pi/2 ∈ Ico 0 Real.pi by constructor <;> linarith [Real.pi_pos]) ht
  have hD : Continuous D := by unfold D orthogonalRayDamping; fun_prop
  have hpower (s : ℝ) (hs : s ≤ 0) :
      IntegrableOn (fun r => G r * D r ^ (s : ℂ)) (Ioi 0) := by
    have hc : ContinuousOn (fun r => D r ^ (s : ℂ)) (Ioi 0) := by
      intro r hr
      exact ((continuousAt_cpow_const
        (Complex.mem_slitPlane_iff.mpr (Or.inl (orthogonalRayDamping_bounds ha ht hr).1))).comp
        (hD.continuousAt (x := r))).continuousWithinAt
    apply hG.mul_bdd (c := (2 * Real.pi * a) ^ s) (hc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (Complex.norm_cpow_real (D r) s).le.trans
      (Real.rpow_le_rpow_of_nonpos (by positivity) (orthogonalRayDamping_bounds ha ht hr).2 hs)
  have h0 := hG.mul_const (estermann h (x : ℂ) (y : ℂ))
  have h1 := (hpower (x-1) (by linarith)).mul_const
    (Gamma (1-(x:ℂ)) * (K:ℂ)^(-(1-(x:ℂ)+(y:ℂ))) * riemannZeta (1-(x:ℂ)+(y:ℂ)))
  have h2 := (hpower (y-1) (by linarith)).mul_const
    (Gamma (1-(y:ℂ)) * (K:ℂ)^(-(1-(y:ℂ)+(x:ℂ))) * riemannZeta (1-(y:ℂ)+(x:ℂ)))
  apply ((h0.add h1).add h2).congr
  filter_upwards with r
  simp only [Pi.add_apply, estermannMellinResidueSum, Complex.ofReal_sub, Complex.ofReal_one]
  change _ = G r * _
  ring

/-- The full vertical remainder on the negative line, before taking the
outer Gaussian ray integral. -/
def rayMellinRemainder {K : ℕ} [NeZero K] (h : ZMod K) (x y : ℂ) (c : ℝ) (lam : ℂ) : ℂ :=
  (1/(2*(Real.pi:ℂ))) * ∫ t : ℝ, estermannMellinKernel h x y lam ((c : ℂ) + I*t)

/-- The original ray, the residue contribution and the vertical integral,
with separate absolute integrability of the last two terms. The near-line
specialization is x=2l−1, y=0 with 1/2<l<1. -/
theorem orthogonalRay_integral_eq_residue_add_mellin {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) (l u : ℝ) {x y a Δ τ c : ℝ}
    (hx : x < 1) (hy : y < 1) (hxy : x ≠ y)
    (ha : 0 < a) (hΔ : 0 < Δ) (ht : τ = 1 ∨ τ = -1)
    (hc : -1 < c) (hc0 : c < 0) (hcx : -1 < c + x) (hcy : -1 < c + y) :
    let G := gaussianRayIntegrand l Δ u 0 (τ*(Real.pi/2))
    let D := orthogonalRayDamping a τ
    let R := fun r => G r * estermannMellinResidueSum (h : ZMod K) (x : ℂ) (y : ℂ) (D r)
    let V := fun r => G r * rayMellinRemainder (h : ZMod K) (x : ℂ) (y : ℂ) c (D r)
    let F := fun r => G r * estermannDampedSeries (h : ZMod K) (x : ℂ) (y : ℂ)
      (estermannRayArgument a τ (Real.pi/2) r)
    IntegrableOn R (Ioi 0) ∧ IntegrableOn V (Ioi 0) ∧
      (∫ r in Ioi 0, F r) = (∫ r in Ioi 0, R r) + (∫ r in Ioi 0, V r) := by
  dsimp only
  let G := gaussianRayIntegrand l Δ u 0 (τ*(Real.pi/2))
  let D := orthogonalRayDamping a τ
  let R := fun r => G r * estermannMellinResidueSum (h : ZMod K) (x : ℂ) (y : ℂ) (D r)
  let V := fun r => G r * rayMellinRemainder (h : ZMod K) (x : ℂ) (y : ℂ) c (D r)
  let F := fun r => G r * estermannDampedSeries (h : ZMod K) (x : ℂ) (y : ℂ)
    (estermannRayArgument a τ (Real.pi/2) r)
  change IntegrableOn R (Ioi 0) ∧ IntegrableOn V (Ioi 0) ∧
    (∫ r in Ioi 0, F r) = (∫ r in Ioi 0, R r) + (∫ r in Ioi 0, V r)
  have hφ : Real.pi/2 ∈ Ioo 0 Real.pi := by constructor <;> linarith [Real.pi_pos]
  have hF : IntegrableOn F (Ioi 0) := by
    have H := integrable_complex_tsum
      (gaussianEstermannRayTerm_integrable (h : ZMod K) (x:ℂ) (y:ℂ) l u hΔ ha hφ ht)
      (summable_integral_norm_gaussianEstermannRayTerm (h : ZMod K) (x:ℂ) (y:ℂ) l u hΔ ha hφ ht)
    simpa only [F, G, IntegrableOn, estermannDampedSeries, ← tsum_mul_left,
      gaussianEstermannRayTerm] using H
  have hR : IntegrableOn R (Ioi 0) :=
    integrableOn_gaussian_mul_orthogonal_residue (h : ZMod K) l u x y hx.le hy.le hΔ ha ht
  have hpoint (r : ℝ) (hr : 0 < r) : F r = R r + V r := by
    have hw : 0 < (estermannRayArgument a τ (Real.pi/2) r).im := by
      rw [← Real.exp_log hr, estermannRayArgument_exp]
      exact estermannRayDisplacement_im_pos ha hφ ht _
    have H := estermannDampedSeries_eq_residues_add_mellinIntegral h
      (by simpa using hx : (x:ℂ).re < 1) (by simpa using hy : (y:ℂ).re < 1)
      (by exact_mod_cast hxy : (x:ℂ) ≠ (y:ℂ)) hw hc hc0 (by simpa using hcx)
      (by simpa using hcy) (b := 2 + |x| + |y|)
      (by simpa using (show 1 < 2 + |x| + |y| + x by linarith [neg_le_abs x, abs_nonneg y]))
      (by simpa using (show 1 < 2 + |x| + |y| + y by linarith [neg_le_abs y, abs_nonneg x]))
    rw [orthogonalRayDamping_eq _ _ ht] at H
    dsimp only [F, R, V, D, rayMellinRemainder]
    rw [H, mul_add]
  have hV : IntegrableOn V (Ioi 0) := by
    apply (hF.sub hR).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change F r - R r = V r
    rw [hpoint _ hr]; ring
  refine ⟨hR, hV, ?_⟩
  rw [← integral_add hR hV]
  exact setIntegral_congr_fun measurableSet_Ioi hpoint

/-- Specialization to each of the two actual reduced twists for the
near-line range. Angle independence allows every original angle in (0,π).
The inner vertical line is fixed at −1/2. -/
theorem gaussianEstermannRay_eq_residue_add_mellin {K H : ℕ} [NeZero K]
    (hH : 0 < H) (hcop : H.Coprime K) (u : ℝ) {l Δ φ : ℝ}
    (hl : 1 / 2 < l) (hl' : l < 1) (hΔ : 0 < Δ) (hφ : φ ∈ Ioo 0 Real.pi)
    {τ : ℤ} (ht : τ = 1 ∨ τ = -1) :
    let h : ZMod K := ((τ*(H:ℤ) : ℤ) : ZMod K)
    let G := gaussianRayIntegrand l Δ u 0 ((τ:ℝ)*(Real.pi/2))
    let D := orthogonalRayDamping ((H:ℝ)/(K:ℝ)) (τ:ℝ)
    let R := fun r => G r * estermannMellinResidueSum h ((2*l-1 : ℝ):ℂ) 0 (D r)
    let V := fun r => G r * rayMellinRemainder h ((2*l-1 : ℝ):ℂ) 0 (-1/2) (D r)
    IntegrableOn R (Ioi 0) ∧ IntegrableOn V (Ioi 0) ∧
      gaussianEstermannRay (K := K) H l Δ u φ τ =
        (∫ r in Ioi 0, R r) + (∫ r in Ioi 0, V r) := by
  have hp := (ZMod.isUnit_iff_coprime H K).2 hcop
  have hs : IsUnit ((τ*(H:ℤ) : ℤ) : ZMod K) := by
    rcases ht with rfl | rfl
    · simpa using hp
    · simpa using hp.neg
  obtain ⟨v, hv⟩ := hs
  have ht' : (τ:ℝ) = 1 ∨ (τ:ℝ) = -1 := by rcases ht with rfl | rfl <;> norm_num
  have ha : (0:ℝ) < (H:ℝ)/(K:ℝ) :=
    div_pos (by exact_mod_cast hH) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K))
  have hz := orthogonalRay_integral_eq_residue_add_mellin v l u
    (x := 2*l-1) (y := 0) (c := -1/2)
    (by linarith) (by norm_num) (by linarith) ha hΔ ht'
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  have hangle : Real.pi/2 ∈ Ioo 0 Real.pi := by constructor <;> linarith [Real.pi_pos]
  rw [gaussianEstermannRay_angle_independent H l u hΔ hH hφ hangle ht]
  simpa only [gaussianEstermannRay, hv, Complex.ofReal_zero, Complex.ofReal_sub,
    Complex.ofReal_one] using hz

/-- Residue and vertical contributions on one signed reduced ray. -/
def gaussianMellinRayParts {K : ℕ} [NeZero K] (H : ℕ) (l Δ u : ℝ) (τ : ℤ) : ℂ × ℂ :=
  let h : ZMod K := ((τ*(H:ℤ) : ℤ) : ZMod K)
  let G := gaussianRayIntegrand l Δ u 0 ((τ:ℝ)*(Real.pi/2))
  let D := orthogonalRayDamping ((H:ℝ)/(K:ℝ)) (τ:ℝ)
  (∫ r in Ioi 0, G r * estermannMellinResidueSum h ((2*l-1 : ℝ):ℂ) 0 (D r),
   ∫ r in Ioi 0, G r * rayMellinRemainder h ((2*l-1 : ℝ):ℂ) 0 (-1/2) (D r))

/-- Each component includes both signed rays at the reduced rational twist. -/
def reducedGaussianMellinParts (l Δ u : ℝ) (h k : ℕ) : ℂ × ℂ :=
  if hp : 0 < h ∧ 0 < k then
    letI : NeZero (k / h.gcd k) := ⟨(Nat.div_gcd_pos_of_pos_right h hp.2).ne'⟩
    gaussianMellinRayParts (K := k / h.gcd k) (h / h.gcd k) l Δ u 1 +
      gaussianMellinRayParts (K := k / h.gcd k) (h / h.gcd k) l Δ u (-1)
  else 0

theorem reducedGaussianEstermannPair_eq_mellinParts (u : ℝ) {l Δ φ : ℝ}
    (hl : 1 / 2 < l) (hl' : l < 1) (hΔ : 0 < Δ) (hφ : φ ∈ Ioo 0 Real.pi) (h k : ℕ) :
    reducedGaussianEstermannPair l Δ u φ h k =
      (reducedGaussianMellinParts l Δ u h k).1 + (reducedGaussianMellinParts l Δ u h k).2 := by
  by_cases hp : 0 < h ∧ 0 < k
  · obtain ⟨hh, hk, hcop⟩ := reducedRationalTwist_pos_coprime hp.1 hp.2
    letI : NeZero (k / h.gcd k) := ⟨hk.ne'⟩
    have hplus := (gaussianEstermannRay_eq_residue_add_mellin hh hcop u hl hl' hΔ hφ
      (Or.inl rfl : (1:ℤ) = 1 ∨ (1:ℤ) = -1)).2.2
    have hminus := (gaussianEstermannRay_eq_residue_add_mellin hh hcop u hl hl' hΔ hφ
      (Or.inr rfl : (-1:ℤ) = 1 ∨ (-1:ℤ) = -1)).2.2
    simp only [reducedGaussianEstermannPair, reducedGaussianMellinParts, dif_pos hp,
      Prod.fst_add, Prod.snd_add, gaussianMellinRayParts, hplus, hminus]
    abel
  · simp [reducedGaussianEstermannPair, reducedGaussianMellinParts, hp]

/-- The original mollifier coefficient functional on a finite twist family. -/
def mollifiedGaussianTwistSum (σ y ε l : ℝ) (S : ℕ → ℕ → ℂ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌊y^(1+ε)⌋₊, ∑ k ∈ Finset.Icc 1 ⌊y^(1+ε)⌋₊,
    ((mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
      (h:ℂ)^((1-2*l:ℝ):ℂ)/(k:ℂ)) * S h k

/-- The finite signed Estermann sum splits before any growth estimate
in the mollifier length or the Gaussian center is applied. -/
theorem mollifiedGaussianEstermannValue_eq_mellinParts (σ y ε u : ℝ) {l Δ φ : ℝ}
    (hl : 1 / 2 < l) (hl' : l < 1) (hΔ : 0 < Δ) (hφ : φ ∈ Ioo 0 Real.pi) :
    mollifiedGaussianEstermannValue σ y ε l Δ u φ =
      mollifiedGaussianTwistSum σ y ε l (fun h k => (reducedGaussianMellinParts l Δ u h k).1) +
      mollifiedGaussianTwistSum σ y ε l (fun h k => (reducedGaussianMellinParts l Δ u h k).2) := by
  unfold mollifiedGaussianEstermannValue mollifiedGaussianTwistSum
  simp_rw [reducedGaussianEstermannPair_eq_mellinParts u hl hl' hΔ hφ, mul_add,
    Finset.sum_add_distrib]

/-- Exact Gaussian moment on every near-line evaluation line. -/
theorem mollifiedGaussianMoment_eq_mellinParts (σ ε u : ℝ) {y l Δ : ℝ}
    (hy : 0 < y) (hl : 1 / 2 < l) (hl' : l < 1) (hΔ : 0 < Δ) :
    (mollifiedGaussianMoment σ y ε l Δ u : ℂ) =
      mollifiedGaussianTwistSum σ y ε l (fun h k => (reducedGaussianMellinParts l Δ u h k).1) +
      mollifiedGaussianTwistSum σ y ε l (fun h k => (reducedGaussianMellinParts l Δ u h k).2) -
      ((2*Real.sqrt Real.pi/Δ : ℝ) : ℂ) * mollifiedGaussianPoleCoeff σ y ε l Δ u := by
  have hφ : Real.pi/2 ∈ Ioo 0 Real.pi := by constructor <;> linarith [Real.pi_pos]
  rw [mollifiedGaussianMoment_eq_estermann σ ε u hy (by linarith) hl' hΔ hφ,
    mollifiedGaussianEstermannValue_eq_mellinParts σ y ε u hl hl' hΔ hφ]

/-- The remaining arithmetic upper bound. Cancellation between the residues
and the shifted vertical contribution is allowed in this one-sided bound. -/
def UniformGaussianMellinPartsBound (θ ε δ : ℝ) : Prop :=
  ∃ η C H : ℝ, 0 < η ∧ 0 ≤ C ∧ 1 < H ∧
    ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
      1/2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1/2 + η →
      ∀ u ∈ Icc (T - T ^ (1-δ)*Real.log T) (2*T + T ^ (1-δ)*Real.log T),
        let M := reducedGaussianMellinParts σ (T^(1-δ)) u
        (mollifiedGaussianTwistSum σ (T^θ) ε σ (fun h k => (M h k).1)).re +
          (mollifiedGaussianTwistSum σ (T^θ) ε σ (fun h k => (M h k).2)).re ≤
          1 + C * T ^ (-(2*θ)*(σ-1/2))

theorem uniformGaussianMollifiedMoment_iff_mellinParts {θ ε δ : ℝ}
    (hθ : 0 < θ) (hδ : 0 < δ) (hδhi : δ ≤ 1) :
    UniformGaussianMollifiedMoment θ ε δ ↔ UniformGaussianMellinPartsBound θ ε δ := by
  have hφ : Real.pi/2 ∈ Ioo 0 Real.pi := by constructor <;> linarith [Real.pi_pos]
  rw [uniformGaussianMollifiedMoment_iff_estermann_real hθ hδ hδhi hφ]
  constructor <;> rintro ⟨η,C,H,hη,hC,hH,hb⟩ <;>
    refine ⟨min η (1/4), C, H, lt_min hη (by norm_num), hC, hH, ?_⟩ <;>
    intro T hT σ hσ hση u hu
  all_goals
    have ht := hH.trans_le hT
    have hσlo : 1/2 < σ := by
      have := one_div_pos.mpr (Real.log_pos (Real.one_lt_rpow ht hθ))
      linarith
    have hσhi : σ < 1 := by linarith [min_le_right η (1/4:ℝ)]
    have hΔ : 0 < T^(1-δ) := Real.rpow_pos_of_pos (by linarith) _
    have hh := hb T hT σ hσ (hση.trans (by linarith [min_le_left η (1/4:ℝ)])) u hu
    simpa only [mollifiedGaussianEstermannValue_eq_mellinParts σ (T^θ) ε u hσlo hσhi hΔ hφ,
      Complex.add_re] using hh

/-- Cofinal upper bounds on the actual signed residue and vertical terms give
the full Conrey--Baluyot range. No independent Ingham input occurs here. -/
theorem conreyBaluyotDensity_of_cofinal_mellinParts
    (hm : ∀ a : ℝ, 0 < a → a < 8 / 7 →
      ∃ θ ε δ : ℝ, a ≤ 2*θ ∧ θ < 4/7 ∧ 0 ≤ ε ∧ 0 < δ ∧ δ ≤ 1 ∧
        UniformGaussianMellinPartsBound θ ε δ) :
    ActualZeroOrdinate.ConreyBaluyotDensityHypothesis := by
  apply conreyBaluyotDensity_of_cofinal_gaussianMollifiedMoments
  intro a ha ha'
  obtain ⟨θ,ε,δ,hlo,hhi,hε,hδ,hδhi,hparts⟩ := hm a ha ha'
  exact ⟨θ, ε, δ, hlo, hhi, hε, hδ, hδhi,
    (uniformGaussianMollifiedMoment_iff_mellinParts (by linarith) hδ hδhi).2 hparts⟩

end RiemannResearch.Analysis.ConreyBaluyot
