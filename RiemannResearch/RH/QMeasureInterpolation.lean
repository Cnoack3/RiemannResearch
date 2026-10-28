/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import RiemannResearch.RH.QShiftedReciprocalBounds
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp


/-!
# Actual projections along the Q/Pareto measure interpolation

Source: the user's change-of-measure and linear-interpolation argument,
28 October 2026; the formal construction uses Mathlib's Banach fixed-point
theorem. For any closed Q-Hilbert subspace S and r orthogonal to S, the
constructed displacement solves d_t = t Π_S B(r+d_t), for 0 <= t <= 1.
The exact trial identity certifies the projection for density I-tB.

The full two-parameter identity retains the signed metric change and the
nonnegative metric remainder. The small-parameter expansion gives a quadratic
Hilbert error. The literal probability mixture (1-s)Q+sP is identified by a
positive scalar and the reparametrization t = s*zeta(2)/(1-s+s*zeta(2)).

No physical boundedness of the projected source or displacement is assumed
or proved. The construction is generic in S and therefore applies separately
to the full-generator and squarefree spaces.
-/

noncomputable section
namespace RiemannResearch.RH.QMeasureInterpolation
open ZetaTwoHilbert QShiftedReciprocal

variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]

def response (r : QHilbert) (t : ℝ) (d : QHilbert) : QHilbert :=
  t • S.starProjection (B (r + d))

theorem projected_B_norm_le_half (f : QHilbert) :
    ‖S.starProjection (B f)‖ ≤ (1 / 2 : ℝ) * ‖f‖ := by
  calc
    _ ≤ ‖S.starProjection‖ * ‖B f‖ := S.starProjection.le_opNorm _
    _ ≤ ‖B f‖ := by
      simpa using mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le S) (norm_nonneg (B f))
    _ ≤ _ := B_norm_le_half f

theorem response_sub (r x y : QHilbert) (t : ℝ) :
    response S r t x - response S r t y =
      t • S.starProjection (B (x - y)) := by
  have harg : B (r + x) - B (r + y) = B (x - y) := by
    rw [← map_sub]
    congr 1
    abel
  unfold response
  rw [← smul_sub, ← map_sub, harg]

theorem response_contracting (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ContractingWith (1 / 2 : NNReal) (response S r t) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  rw [dist_eq_norm, response_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht0, dist_eq_norm]
  change t * ‖S.starProjection (B (x - y))‖ ≤ (1 / 2 : ℝ) * ‖x - y‖
  calc
    _ ≤ t * ((1 / 2 : ℝ) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (projected_B_norm_le_half S (x - y)) ht0
    _ ≤ _ := by nlinarith [norm_nonneg (x - y)]

def displacement (r : QHilbert) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : QHilbert :=
  ContractingWith.fixedPoint (response S r t) (response_contracting S r t ht0 ht1)

theorem displacement_fixed_point (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    displacement S r t ht0 ht1 =
      t • S.starProjection (B (r + displacement S r t ht0 ht1)) := by
  have h := ContractingWith.fixedPoint_isFixedPt (response_contracting S r t ht0 ht1)
  exact h.symm

theorem displacement_mem (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    displacement S r t ht0 ht1 ∈ S := by
  rw [displacement_fixed_point]
  exact S.smul_mem _ (S.starProjection_apply_mem _)

theorem displacement_unique (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (d : QHilbert)
    (hd : d = t • S.starProjection (B (r + d))) :
    d = displacement S r t ht0 ht1 := by
  exact (response_contracting S r t ht0 ht1).fixedPoint_unique hd.symm

theorem displacement_zero (r : QHilbert) :
    displacement S r 0 (by norm_num) (by norm_num) = 0 := by
  exact (displacement_unique S r 0 (by norm_num) (by norm_num) 0 (by simp)).symm

theorem weighted_residual_mem_orthogonal (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : r ∈ Sᗮ) :
    r + displacement S r t ht0 ht1 -
      t • B (r + displacement S r t ht0 ht1) ∈ Sᗮ := by
  let d := displacement S r t ht0 ht1
  have hp := Submodule.sub_starProjection_mem_orthogonal (K := S) (B (r + d))
  have hd : d = t • S.starProjection (B (r + d)) :=
    displacement_fixed_point S r t ht0 ht1
  have he : r + d - t • B (r + d) =
      r - t • (B (r + d) - S.starProjection (B (r + d))) := by
    rw [smul_sub, ← hd]
    abel
  change r + d - t • B (r + d) ∈ Sᗮ
  rw [he]
  exact Sᗮ.sub_mem hr (Sᗮ.smul_mem t hp)

theorem normal_equation (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : r ∈ Sᗮ)
    (v : QHilbert) (hv : v ∈ S) :
    inner ℝ v (r + displacement S r t ht0 ht1) =
      t * inner ℝ v (B (r + displacement S r t ht0 ht1)) := by
  have h := Submodule.inner_right_of_mem_orthogonal hv
    (weighted_residual_mem_orthogonal S r t ht0 ht1 hr)
  rw [inner_sub_right, inner_smul_right] at h
  linarith

/-- Energy for the equivalent measure with density `1-t/(n+1)` relative to Q. -/
def energy (t : ℝ) (f : QHilbert) : ℝ :=
  ‖f‖ ^ 2 - t * inner ℝ f (B f)

theorem energy_lower (t : ℝ) (f : QHilbert) (ht : 0 ≤ t) :
    (1 - t / 2) * ‖f‖ ^ 2 ≤ energy t f := by
  have hb := twice_B_inner_le_norm_sq f
  have hm := mul_nonneg ht (sub_nonneg.mpr hb)
  dsimp only [energy]
  nlinarith

theorem energy_nonneg (t : ℝ) (f : QHilbert) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ energy t f := by
  calc
    0 ≤ (1 - t / 2) * ‖f‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    _ ≤ _ := energy_lower t f ht0

/-- Exact two-parameter energy identity, retaining the squared metric remainder. -/
theorem energy_comparison_exact (s t : ℝ) (rs rt : QHilbert)
    (hnormal : inner ℝ (rs - rt) rt = t * inner ℝ (rs - rt) (B rt)) :
    energy s rs = energy t rt + (t - s) * inner ℝ rs (B rs) +
      energy t (rs - rt) := by
  have hsym : inner ℝ rt (B rs) = inner ℝ rs (B rt) := by
    rw [← B_symmetric, real_inner_comm]
  simp only [inner_sub_left, real_inner_self_eq_norm_sq] at hnormal
  simp only [energy, norm_sub_sq_real, map_sub, inner_sub_left, inner_sub_right, hsym]
  nlinarith [hnormal]

/-- Exact comparison along the actual Banach-constructed projection path. -/
theorem interpolation_energy_exact (r : QHilbert) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : r ∈ Sᗮ) :
    energy s (r + displacement S r s hs0 hs1) =
      energy t (r + displacement S r t ht0 ht1) +
      (t - s) * inner ℝ (r + displacement S r s hs0 hs1)
        (B (r + displacement S r s hs0 hs1)) +
      energy t (displacement S r s hs0 hs1 - displacement S r t ht0 ht1) := by
  have he : (r + displacement S r s hs0 hs1) -
      (r + displacement S r t ht0 ht1) =
      displacement S r s hs0 hs1 - displacement S r t ht0 ht1 := by abel
  have hm : (r + displacement S r s hs0 hs1) -
      (r + displacement S r t ht0 ht1) ∈ S := by
    rw [he]
    exact S.sub_mem (displacement_mem S r s hs0 hs1) (displacement_mem S r t ht0 ht1)
  have hn := normal_equation S r t ht0 ht1 hr _ hm
  have h := energy_comparison_exact s t (r + displacement S r s hs0 hs1)
    (r + displacement S r t ht0 ht1) hn
  simpa only [he] using h

theorem interpolation_energy_antitone (r : QHilbert) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : r ∈ Sᗮ) (hst : s ≤ t) :
    energy t (r + displacement S r t ht0 ht1) ≤
      energy s (r + displacement S r s hs0 hs1) := by
  have he := interpolation_energy_exact S r s t hs0 hs1 ht0 ht1 hr
  have hp := mul_nonneg (sub_nonneg.mpr hst)
    (B_positive (r + displacement S r s hs0 hs1))
  have hn := energy_nonneg t
    (displacement S r s hs0 hs1 - displacement S r t ht0 ht1) ht0 ht1
  linarith

theorem interpolation_energy_lower (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : r ∈ Sᗮ) :
    (1 - t / 2) * ‖r‖ ^ 2 ≤ energy t (r + displacement S r t ht0 ht1) := by
  have ho : inner ℝ (displacement S r t ht0 ht1) r = 0 :=
    Submodule.inner_right_of_mem_orthogonal (displacement_mem S r t ht0 ht1) hr
  have hn : ‖r‖ ^ 2 ≤ ‖r + displacement S r t ht0 ht1‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_comm, ho]
    nlinarith [sq_nonneg ‖displacement S r t ht0 ht1‖]
  exact (mul_le_mul_of_nonneg_left hn (by linarith : 0 ≤ 1 - t / 2)).trans
    (energy_lower t (r + displacement S r t ht0 ht1) ht0)

theorem interpolation_energy_upper (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : r ∈ Sᗮ) :
    energy t (r + displacement S r t ht0 ht1) ≤ energy t r := by
  have he : r - (r + displacement S r t ht0 ht1) =
      -displacement S r t ht0 ht1 := by abel
  have hm : r - (r + displacement S r t ht0 ht1) ∈ S := by
    rw [he]
    exact S.neg_mem (displacement_mem S r t ht0 ht1)
  have hn := normal_equation S r t ht0 ht1 hr _ hm
  have hi := energy_comparison_exact t t r (r + displacement S r t ht0 ht1) hn
  have hp := energy_nonneg t (r - (r + displacement S r t ht0 ht1)) ht0 ht1
  simp only [sub_self, zero_mul, add_zero] at hi
  linarith

theorem displacement_expansion (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    displacement S r t ht0 ht1 =
      t • S.starProjection (B r) +
      t • S.starProjection (B (displacement S r t ht0 ht1)) := by
  calc
    _ = t • S.starProjection (B (r + displacement S r t ht0 ht1)) :=
      displacement_fixed_point S r t ht0 ht1
    _ = _ := by rw [map_add, map_add, smul_add]

/-- The orthogonal baseline improves the coarse response bound by a factor two. -/
theorem displacement_norm_le (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : r ∈ Sᗮ) :
    ‖displacement S r t ht0 ht1‖ ≤ (t / 2) * ‖r‖ := by
  have hn := norm_add_le (t • S.starProjection (B r))
    (t • S.starProjection (B (displacement S r t ht0 ht1)))
  rw [← displacement_expansion S r t ht0 ht1] at hn
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hn
  have h1 := mul_le_mul_of_nonneg_left (projected_B_norm_le_quarter S hr) ht0
  have h2 := mul_le_mul_of_nonneg_left
    (projected_B_norm_le_half S (displacement S r t ht0 ht1)) ht0
  have h3 := mul_le_mul_of_nonneg_right ht1
    (norm_nonneg (displacement S r t ht0 ht1))
  nlinarith

/-- Exact first-order response with its feedback remainder retained. -/
theorem displacement_first_order_remainder (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    displacement S r t ht0 ht1 - t • S.starProjection (B r) =
      t • S.starProjection (B (displacement S r t ht0 ht1)) := by
  calc
    _ = (t • S.starProjection (B r) +
        t • S.starProjection (B (displacement S r t ht0 ht1))) -
        t • S.starProjection (B r) :=
      congrArg (fun x => x - t • S.starProjection (B r))
        (displacement_expansion S r t ht0 ht1)
    _ = _ := by abel

/-- Uniform quadratic Hilbert-norm error in the first-order interpolation response. -/
theorem displacement_first_order_bound (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : r ∈ Sᗮ) :
    ‖displacement S r t ht0 ht1 - t • S.starProjection (B r)‖ ≤
      (t ^ 2 / 4) * ‖r‖ := by
  rw [displacement_first_order_remainder, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht0]
  calc
    _ ≤ t * ((1 / 2 : ℝ) * ‖displacement S r t ht0 ht1‖) :=
      mul_le_mul_of_nonneg_left
        (projected_B_norm_le_half S (displacement S r t ht0 ht1)) ht0
    _ ≤ t * ((1 / 2 : ℝ) * ((t / 2) * ‖r‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (displacement_norm_le S r t ht0 ht1 hr)
          (by norm_num)) ht0
    _ = _ := by ring

open ZetaTwoProbability ZetaTwoParetoTransfer

/-- Scalar factor for the literal probability mixture (1-s)Q+sP. -/
def mixtureScale (s : ℝ) : ℝ := 1 - s + s * zetaTwo

/-- Reparametrization of the literal probability mixture by the density I-tB. -/
def mixtureParameter (s : ℝ) : ℝ := s * zetaTwo / mixtureScale s

theorem mixtureScale_pos (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < mixtureScale s := by
  by_cases hs : s = 0
  · simp [mixtureScale, hs]
  · have hp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hz := mul_pos hp zetaTwo_pos
    dsimp only [mixtureScale]
    linarith

theorem mixtureParameter_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ mixtureParameter s :=
  div_nonneg (mul_nonneg hs0 zetaTwo_pos.le) (mixtureScale_pos s hs0 hs1).le

theorem mixtureParameter_le_one (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    mixtureParameter s ≤ 1 := by
  apply (div_le_one (mixtureScale_pos s hs0 hs1)).mpr
  dsimp only [mixtureScale]
  linarith

theorem mixtureParameter_pos (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    0 < mixtureParameter s :=
  div_pos (mul_pos hs0 zetaTwo_pos) (mixtureScale_pos s hs0.le hs1)

/-- Exact energy identity for the literal probability mixture. -/
theorem mixture_energy_exact (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (f : QHilbert) :
    (1 - s) * ‖f‖ ^ 2 + s * ‖toPareto f‖ ^ 2 =
      mixtureScale s * energy (mixtureParameter s) f := by
  have hp := pareto_inner_identity f f
  simp only [real_inner_self_eq_norm_sq] at hp
  rw [hp]
  have hc : mixtureScale s ≠ 0 := ne_of_gt (mixtureScale_pos s hs0 hs1)
  unfold energy mixtureParameter
  field_simp [hc]
  dsimp only [mixtureScale]
  ring



/-- Exact comparison with every admissible trial, certifying the minimizer. -/
theorem interpolation_trial_exact (r : QHilbert) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : r ∈ Sᗮ)
    (v : QHilbert) (hv : v ∈ S) :
    energy t (r + v) = energy t (r + displacement S r t ht0 ht1) +
      energy t (v - displacement S r t ht0 ht1) := by
  have he : (r + v) - (r + displacement S r t ht0 ht1) =
      v - displacement S r t ht0 ht1 := by abel
  have hm : (r + v) - (r + displacement S r t ht0 ht1) ∈ S := by
    rw [he]
    exact S.sub_mem hv (displacement_mem S r t ht0 ht1)
  have hn := normal_equation S r t ht0 ht1 hr _ hm
  have hi := energy_comparison_exact t t (r + v)
    (r + displacement S r t ht0 ht1) hn
  simpa only [he, sub_self, zero_mul, add_zero] using hi

theorem mixtureParameter_zero : mixtureParameter 0 = 0 := by
  simp [mixtureParameter, mixtureScale]

theorem mixtureParameter_one : mixtureParameter 1 = 1 := by
  simp [mixtureParameter, mixtureScale, ne_of_gt ZetaTwoProbability.zetaTwo_pos]


end RiemannResearch.RH.QMeasureInterpolation
