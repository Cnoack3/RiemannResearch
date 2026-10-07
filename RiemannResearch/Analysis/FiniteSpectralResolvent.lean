/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteSpectralMomentUpper
import RiemannResearch.Analysis.FiniteHeadTailSpectralRealization

/-!
# Complete-source spectral resolvents and exact variational certificates

Source: user-requested actual-source contrast work, 7 October 2026.
This development supplies exact finite resolvent and full Hilbert energy
identities. It constructs the literal frame source using the head adjoint.
The Pareto consumer in RH/ParetoActualSpectralResolvent.lean discharges the
arithmetic trial estimates. No strict double-log saving is assumed here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteSpectralBudget
variable {ι : Type*}

def sourceResolvent (s : Finset ι) (w lam : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, w i / (t + lam i)

def correctionResolvent (s : Finset ι) (w lam : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, (w i * lam i / (1 + lam i)) / (t + lam i)

/-- Source loss when the full physical-tail penalty is weakened to 1/t. -/
def sourceDeficit (s : Finset ι) (w lam : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, w i * lam i / (t + lam i)

theorem sourceDeficit_eq_mass_sub_resolvent
    (s : Finset ι) (w lam : ι → ℝ) (t : ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : 0 < t) :
    sourceDeficit s w lam t = mass s w - t * sourceResolvent s w lam t := by
  unfold sourceDeficit mass sourceResolvent
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : t + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
  field_simp [hd]
  ring

theorem sourceDeficit_nonneg
    (s : Finset ι) (w lam : ι → ℝ) (t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : 0 < t) :
    0 ≤ sourceDeficit s w lam t := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (by linarith [hlam i hi])

/-- The moving high spectrum is controlled by the literal regularization
deficit; every source component remains in that deficit. -/
theorem highMass_le_two_mul_sourceDeficit
    (s : Finset ι) (w lam : ι → ℝ) (t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : 0 < t) :
    highMass s w lam t ≤ 2 * sourceDeficit s w lam t := by
  unfold highMass sourceDeficit
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hd : 0 < t + lam i := by linarith [hlam i hi]
  by_cases hti : t ≤ lam i
  · rw [if_pos hti]
    have hh : w i * (t + lam i) ≤ 2 * (w i * lam i) := by
      nlinarith [mul_nonneg (hw i hi) (sub_nonneg.mpr hti)]
    calc
      w i ≤ (2 * (w i * lam i)) / (t + lam i) := (le_div_iff₀ hd).mpr hh
      _ = _ := by ring
  · rw [if_neg hti]
    exact mul_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) hd.le)

/-- Exact regularization identity, including t=1. -/
theorem correctionResolvent_source_identity
    (s : Finset ι) (w lam : ι → ℝ) (t : ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : 0 < t) :
    (t - 1) * correctionResolvent s w lam t =
      t * sourceResolvent s w lam t - sourceResolvent s w lam 1 := by
  unfold correctionResolvent sourceResolvent
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd₁ : 1 + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
  have hdt : t + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
  field_simp [hd₁, hdt]
  ring

theorem correctionResolvent_one
    (s : Finset ι) (w lam : ι → ℝ) :
    correctionResolvent s w lam 1 = optimizerTail s w lam := by
  unfold correctionResolvent optimizerTail
  apply Finset.sum_congr rfl
  intro i hi
  simp only [div_div, pow_two]

theorem correctionResolvent_nonneg
    (s : Finset ι) (w lam : ι → ℝ) (t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : 0 < t) :
    0 ≤ correctionResolvent s w lam t := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg
    (div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (by linarith [hlam i hi]))
    (by linarith [hlam i hi])

/-- Every source component remains present in the cap resolvent gap. -/
theorem correctionResolvent_cap_difference
    (s : Finset ι) (w lam : ι → ℝ) (t L : ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : 0 < t) (hL : 0 ≤ L) :
    correctionResolvent s w lam t - correction s w lam / (t + L) =
      ∑ i ∈ s, (w i * lam i / (1 + lam i)) *
        (L - lam i) / ((t + lam i) * (t + L)) := by
  unfold correctionResolvent correction
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd₁ : 1 + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
  have hdt : t + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
  have hdL : t + L ≠ 0 := ne_of_gt (by linarith)
  field_simp [hd₁, hdt, hdL]
  ring

private theorem scalar_doubleLog_rational_contrast
    (x L r t : ℝ) (hx : 0 ≤ x) (hxL : x ≤ L)
    (hr : 0 < r) (hrL : r ≤ L) (ht : 0 < t) :
    (doubleLog L - doubleLog r) * (t * (r - x) / (r * (x + t))) ≤
      doubleLog L - doubleLog x := by
  have hΔ : 0 ≤ doubleLog L - doubleLog r :=
    sub_nonneg.mpr (doubleLog_mono_nonneg hr.le hrL)
  have hgap : 0 ≤ doubleLog L - doubleLog x :=
    sub_nonneg.mpr (doubleLog_mono_nonneg hx hxL)
  have hden : 0 < r * (x + t) := mul_pos hr (by linarith)
  by_cases hxr : x ≤ r
  · have hratio : t * (r - x) / (r * (x + t)) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    have hbound := mul_le_mul_of_nonneg_left hratio hΔ
    have hmono := doubleLog_mono_nonneg hx hxr
    linarith
  · have hratio : t * (r - x) / (r * (x + t)) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ht.le (by linarith)) hden.le
    exact (mul_nonpos_of_nonneg_of_nonpos hΔ hratio).trans hgap

/-- A finite rational certificate for the actual complete cap contrast.
The theorem contains the full resolvent, rather than a screened mass. -/
theorem doubleLogCapContrast_ge_resolvent_certificate
    (s : Finset ι) (w lam : ι → ℝ) (L r t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hcap : ∀ i ∈ s, lam i ≤ L)
    (hr : 0 < r) (hrL : r ≤ L) (ht : 0 < t) :
    (doubleLog L - doubleLog r) * (t / r) *
      ((r + t) * correctionResolvent s w lam t - correction s w lam) ≤
        doubleLogCapContrast s w lam L := by
  calc
    _ = ∑ i ∈ s, (w i * lam i / (1 + lam i)) *
        ((doubleLog L - doubleLog r) *
          (t * (r - lam i) / (r * (lam i + t)))) := by
      unfold correctionResolvent correction
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hd₁ : 1 + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
      have hdt : t + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
      have hdt' : lam i + t ≠ 0 := by simpa [add_comm] using hdt
      field_simp [hd₁, hdt, hdt', ne_of_gt hr]
      ring
    _ ≤ _ := by
      unfold doubleLogCapContrast
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (scalar_doubleLog_rational_contrast (lam i) L r t
          (hlam i hi) (hcap i hi) hr hrL ht)
        (div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (by linarith [hlam i hi]))

/-- Exact signed quadratic certificate in diagonal coordinates. -/
theorem sourceResolvent_trial_completion
    (s : Finset ι) (a c lam : ι → ℝ) (t : ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : 0 < t) :
    sourceResolvent s (fun i => (a i) ^ 2) lam t -
      2 * (∑ i ∈ s, a i * c i) +
      (∑ i ∈ s, (t + lam i) * (c i) ^ 2) =
        ∑ i ∈ s, (t + lam i) * (a i / (t + lam i) - c i) ^ 2 := by
  unfold sourceResolvent
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : t + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
  field_simp [hd]
  ring

theorem sourceResolvent_ge_signed_trial
    (s : Finset ι) (a c lam : ι → ℝ) (t : ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : 0 < t) :
    2 * (∑ i ∈ s, a i * c i) -
      (∑ i ∈ s, (t + lam i) * (c i) ^ 2) ≤
        sourceResolvent s (fun i => (a i) ^ 2) lam t := by
  have h := sourceResolvent_trial_completion s a c lam t hlam ht
  have hn : 0 ≤ ∑ i ∈ s, (t + lam i) * (a i / (t + lam i) - c i) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by linarith [hlam i hi]) (sq_nonneg _)
  linarith

/-- Direct full-source contrast certificate; the signed high mass deficit
is retained before estimating it. -/
theorem doubleLogCapContrast_ge_correction_sub_highMass
    (s : Finset ι) (w lam : ι → ℝ) (L r : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hcap : ∀ i ∈ s, lam i ≤ L) (hr : 0 ≤ r) (hrL : r ≤ L) :
    (doubleLog L - doubleLog r) * (correction s w lam - highMass s w lam r) ≤
      doubleLogCapContrast s w lam L := by
  have hΔ : 0 ≤ doubleLog L - doubleLog r :=
    sub_nonneg.mpr (doubleLog_mono_nonneg hr hrL)
  unfold correction highMass doubleLogCapContrast
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hc : 0 ≤ w i * lam i / (1 + lam i) :=
    div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (by linarith [hlam i hi])
  have hg : 0 ≤ doubleLog L - doubleLog (lam i) :=
    sub_nonneg.mpr (doubleLog_mono_nonneg (hlam i hi) (hcap i hi))
  by_cases hri : r ≤ lam i
  · rw [if_pos hri]
    have hcweight : w i * lam i / (1 + lam i) ≤ w i := by
      apply (div_le_iff₀ (by linarith [hlam i hi] : 0 < 1 + lam i)).mpr
      nlinarith [hw i hi]
    exact (mul_nonpos_of_nonneg_of_nonpos hΔ (sub_nonpos.mpr hcweight)).trans
      (mul_nonneg hc hg)
  · rw [if_neg hri, sub_zero]
    have hphi := doubleLog_mono_nonneg (hlam i hi) (le_of_lt (lt_of_not_ge hri))
    have hgap : doubleLog L - doubleLog r ≤ doubleLog L - doubleLog (lam i) :=
      sub_le_sub_left hphi _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hgap hc

end RiemannResearch.Analysis.FiniteSpectralBudget

namespace RiemannResearch.Analysis.FiniteHeadTailSpectralRealization
variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def regularizedHead (A : E →L[ℝ] H) (t : ℝ) (x : E) : E :=
  ∑ i, (inner ℝ (eigenBasis A i) x / (t + eigenvalue A i)) • eigenBasis A i

def regularizedEnergy (A : E →L[ℝ] H) (t : ℝ) (c : E) : ℝ :=
  t * ‖c‖ ^ 2 + ‖A c‖ ^ 2

def headResolvent (A : E →L[ℝ] H) (t : ℝ) (x : E) : ℝ :=
  inner ℝ x (regularizedHead A t x)

theorem headResolvent_eq_sourceResolvent
    (A : E →L[ℝ] H) (t : ℝ) (x : E) :
    headResolvent A t x =
      FiniteSpectralBudget.sourceResolvent Finset.univ
        (fun i => (inner ℝ (eigenBasis A i) x) ^ 2) (eigenvalue A) t := by
  unfold headResolvent regularizedHead FiniteSpectralBudget.sourceResolvent
  rw [inner_sum]
  simp only [real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm x (eigenBasis A i)]
  ring

/-- The head adjoint constructs the literal source weights of the full
physical head-tail frame. -/
theorem headResolvent_eq_frame_sourceResolvent
    (J : E →ₗᵢ[ℝ] H) (A : E →L[ℝ] H) (t : ℝ) (v : H) :
    headResolvent A t (J.toContinuousLinearMap.adjoint v) =
      FiniteSpectralBudget.sourceResolvent Finset.univ
        (sourceWeight (fun i => J (eigenBasis A i)) v) (eigenvalue A) t := by
  rw [headResolvent_eq_sourceResolvent]
  unfold FiniteSpectralBudget.sourceResolvent sourceWeight source
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  have hh : inner ℝ (eigenBasis A i) (J.toContinuousLinearMap.adjoint v) =
      inner ℝ (J (eigenBasis A i)) v :=
    J.toContinuousLinearMap.adjoint_inner_right (eigenBasis A i) v
  rw [hh]

theorem headResolvent_smul (A : E →L[ℝ] H) (t q : ℝ) (x : E) :
    headResolvent A t (q • x) = q ^ 2 * headResolvent A t x := by
  rw [headResolvent_eq_sourceResolvent, headResolvent_eq_sourceResolvent]
  unfold FiniteSpectralBudget.sourceResolvent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [real_inner_smul_right]
  ring

private theorem regularizedHead_normal_basis
    (A : E →L[ℝ] H) (t : ℝ) (x : E) (ht : 0 < t)
    (j : Fin (Module.finrank ℝ E)) :
    t * inner ℝ (regularizedHead A t x) (eigenBasis A j) +
      inner ℝ (A (regularizedHead A t x)) (A (eigenBasis A j)) =
        inner ℝ x (eigenBasis A j) := by
  have hh : inner ℝ (regularizedHead A t x) (eigenBasis A j) =
      inner ℝ (eigenBasis A j) x / (t + eigenvalue A j) := by
    unfold regularizedHead
    rw [sum_inner]
    simp only [real_inner_smul_left,
      orthonormal_iff_ite.mp (eigenBasis A).orthonormal]
    simp [mul_ite]
  have htail : inner ℝ (A (regularizedHead A t x)) (A (eigenBasis A j)) =
      (inner ℝ (eigenBasis A j) x / (t + eigenvalue A j)) * eigenvalue A j := by
    unfold regularizedHead
    rw [map_sum, sum_inner]
    simp only [map_smul, real_inner_smul_left, tail_basis_inner]
    simp [mul_ite]
  rw [hh, htail, real_inner_comm x (eigenBasis A j)]
  have hd : t + eigenvalue A j ≠ 0 :=
    ne_of_gt (by linarith [eigenvalue_nonneg A j])
  field_simp [hd]

/-- The complete physical-tail energy form satisfies the normal equation. -/
theorem regularizedHead_normal
    (A : E →L[ℝ] H) (t : ℝ) (x c : E) (ht : 0 < t) :
    t * inner ℝ (regularizedHead A t x) c +
      inner ℝ (A (regularizedHead A t x)) (A c) = inner ℝ x c := by
  rw [← (eigenBasis A).sum_repr c]
  simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ((eigenBasis A).repr c i) *
        (t * inner ℝ (regularizedHead A t x) (eigenBasis A i) +
          inner ℝ (A (regularizedHead A t x)) (A (eigenBasis A i))) := by ring
    _ = _ := by rw [regularizedHead_normal_basis A t x ht i]

/-- Exact signed source completion: both physical energy squares survive. -/
theorem headResolvent_trial_completion
    (A : E →L[ℝ] H) (t : ℝ) (x c : E) (ht : 0 < t) :
    headResolvent A t x - 2 * inner ℝ x c + regularizedEnergy A t c =
      regularizedEnergy A t (regularizedHead A t x - c) := by
  have hnorm (u v : E) : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * inner ℝ u v := by
    rw [sub_eq_add_neg, norm_add_sq_real]
    simp only [norm_neg, inner_neg_right]
    ring
  have hnormH (u v : H) : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * inner ℝ u v := by
    rw [sub_eq_add_neg, norm_add_sq_real]
    simp only [norm_neg, inner_neg_right]
    ring
  have hn := regularizedHead_normal A t x c ht
  have hy := regularizedHead_normal A t x (regularizedHead A t x) ht
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hy
  unfold headResolvent regularizedEnergy
  rw [hnorm, map_sub, hnormH]
  nlinarith only [hn, hy]

theorem headResolvent_ge_signed_trial
    (A : E →L[ℝ] H) (t : ℝ) (x c : E) (ht : 0 < t) :
    2 * inner ℝ x c - regularizedEnergy A t c ≤ headResolvent A t x := by
  have h := headResolvent_trial_completion A t x c ht
  have hn : 0 ≤ regularizedEnergy A t (regularizedHead A t x - c) := by
    exact add_nonneg (mul_nonneg ht.le (sq_nonneg _)) (sq_nonneg _)
  linarith

/-- Exact physical variational loss at positive head penalty t. This
retains both the head error square and the whole physical-tail square. -/
theorem physical_regularized_loss_identity
    (J : E →ₗᵢ[ℝ] H) (A : E →L[ℝ] H) (t : ℝ) (v : H) (c : E)
    (ht : 0 < t) :
    t * ‖v - J c‖ ^ 2 + ‖A c‖ ^ 2 =
      t * ‖v‖ ^ 2 - headResolvent A t (t • J.toContinuousLinearMap.adjoint v) +
        regularizedEnergy A t
          (regularizedHead A t (t • J.toContinuousLinearMap.adjoint v) - c) := by
  have hnorm : ‖v - J c‖ ^ 2 = ‖v‖ ^ 2 + ‖c‖ ^ 2 - 2 * inner ℝ v (J c) := by
    rw [sub_eq_add_neg, norm_add_sq_real]
    simp only [norm_neg, inner_neg_right, J.norm_map]
    ring
  have hpair : inner ℝ v (J c) = inner ℝ (J.toContinuousLinearMap.adjoint v) c := by
    exact (J.toContinuousLinearMap.adjoint_inner_left c v).symm
  have h := headResolvent_trial_completion A t
    (t • J.toContinuousLinearMap.adjoint v) c ht
  simp only [real_inner_smul_left] at h
  rw [hnorm, hpair]
  unfold regularizedEnergy at h ⊢
  nlinarith only [h]

end RiemannResearch.Analysis.FiniteHeadTailSpectralRealization
