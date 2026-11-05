/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QHarmonicResolventApproximation
import RiemannResearch.RH.MertensFullDisplacement
import RiemannResearch.Analysis.DyadicBlockSummability
import RiemannResearch.Analysis.DyadicBlockDecomposition

/-! # The full Lee–Leong moment on dyadic resolvent approximants
Use depth j on the physical shell [2^j,2^(j+1)). The error of this
diagonal substitution is absolutely summable even before damping.
Resolvent depth is finite; the closure projection inside the resolvent is
still an infinite-dimensional operator. -/
noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis ZetaTwoProbability ZetaTwoHilbert
open QSquarefreeDisplacementRigidity QSquarefreeDisplacementResolvent

/-- Absolute weighted harmonic mass of the j-th shell. -/
def resolventMomentShell (w : ℕ → ℝ) (u : QHilbert) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ j), w (2 ^ j + i) *
    |qSequence u (2 ^ j + i) / ((2 ^ j + i : ℕ) : ℝ)|

private theorem shell_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (u : QHilbert) (j : ℕ) : 0 ≤ resolventMomentShell w u j :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw _) (abs_nonneg _))

private theorem shell_triangle {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (u v : QHilbert) (j : ℕ) :
    resolventMomentShell w u j ≤ resolventMomentShell w v j +
      resolventMomentShell w (u - v) j := by
  unfold resolventMomentShell
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  let n := 2 ^ j + i
  have hp : qSequence (u - v) n = qSequence u n - qSequence v n :=
    congrFun (map_sub qSequenceLinear u v) n
  change w n * |qSequence u n / (n : ℝ)| ≤ w n * |qSequence v n / (n : ℝ)| +
    w n * |qSequence (u-v) n / (n : ℝ)|
  rw [← mul_add, hp, sub_div]
  apply mul_le_mul_of_nonneg_left _ (hw n)
  calc
    _ = |qSequence v n / (n : ℝ) +
      (qSequence u n / (n : ℝ) - qSequence v n / (n : ℝ))| := by congr 1 <;> ring
    _ ≤ _ := abs_add_le _ _

private theorem shell_sub_comm (w : ℕ → ℝ) (u v : QHilbert) (j : ℕ) :
    resolventMomentShell w (v-u) j = resolventMomentShell w (u-v) j := by
  unfold resolventMomentShell
  apply Finset.sum_congr rfl
  intro i _
  let n := 2 ^ j + i
  have hp : qSequence (u - v) n = qSequence u n - qSequence v n :=
    congrFun (map_sub qSequenceLinear u v) n
  have hq : qSequence (v - u) n = qSequence v n - qSequence u n :=
    congrFun (map_sub qSequenceLinear v u) n
  change w n * |qSequence (v-u) n / (n : ℝ)| = w n * |qSequence (u-v) n / (n : ℝ)|
  rw [hp, hq, abs_div, abs_div, abs_sub_comm]

/-- The physical mass lost to depth j has a summable geometric bound. -/
theorem resolventMomentShell_error_le (w : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hwC : ∀ n, w n ≤ C) (j : ℕ) :
    resolventMomentShell w (displacement - resolventApprox j) j ≤
      (C * Real.sqrt zetaTwo * ‖displacement‖) * (Real.sqrt 2 / 3) ^ j := by
  classical
  let v := displacement - resolventApprox j
  let t := (Finset.range (2 ^ j)).image (fun i : ℕ => 2 ^ j + i)
  have hinj : Function.Injective (fun i : ℕ => 2 ^ j + i) := by
    intro i k h; dsimp at h; omega
  have hcard : t.card = 2 ^ j := by
    simpa [t] using Finset.card_image_of_injective (Finset.range (2 ^ j)) hinj
  have himage : (∑ i ∈ Finset.range (2 ^ j),
      |qSequence v (2 ^ j + i) / ((2 ^ j + i : ℕ) : ℝ)|) =
      ∑ n ∈ t, |qSequence v n / (n : ℝ)| := by
    unfold t
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => hinj h
  have hsg : (Real.sqrt (2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsqrt : Real.sqrt (zetaTwo * (t.card : ℝ)) =
      Real.sqrt zetaTwo * (Real.sqrt 2) ^ j := by
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, Real.sqrt_mul zetaTwo_pos.le, ← hsg,
      Real.sqrt_sq (by positivity)]
  have h := physicalHarmonic_finset_le v t
  rw [hsqrt] at h
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ j), C *
        |qSequence v (2 ^ j + i) / ((2 ^ j + i : ℕ) : ℝ)| :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hwC _) (abs_nonneg _))
    _ = C * ∑ n ∈ t, |qSequence v n / (n : ℝ)| := by rw [← Finset.mul_sum, himage]
    _ ≤ C * (Real.sqrt zetaTwo * Real.sqrt 2 ^ j * ‖v‖) :=
      mul_le_mul_of_nonneg_left h hC
    _ ≤ C * (Real.sqrt zetaTwo * Real.sqrt 2 ^ j *
        ((1 / 3 : ℝ) ^ j * ‖displacement‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (resolvent_error_norm_le j)
        (by positivity)) hC
    _ = _ := by rw [div_eq_mul_inv (Real.sqrt 2), mul_pow]; simp only [one_div]; ring

private theorem summable_moment_iff_shell (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    Summable (fun n : ℕ => w n * |qSequence displacement n / (n : ℝ)|) ↔
      Summable (resolventMomentShell w displacement) := by
  let a (n : ℕ) := w n * |qSequence displacement n / (n : ℝ)|
  have ha (n : ℕ) : 0 ≤ a n := mul_nonneg (hw n) (abs_nonneg _)
  constructor
  · intro h
    apply (DyadicBlockDecomposition.summable_scaledDyadicBlock a 1 ha h).congr
    intro j
    simp only [DyadicBlockDecomposition.scaledDyadicBlock, one_mul, resolventMomentShell, a]
  · intro h
    exact DyadicWeightedContrast.summable_of_dyadic_block_majorant a _ ha
      (shell_nonneg hw displacement) h (fun _ => le_rfl)

/-- Any nonnegative bounded damping may be tested on a single resolvent
depth per shell; no Mertens or approximation theorem is used. -/
theorem summable_harmonic_iff_resolventMomentShell (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (C : ℝ) (hC : 0 ≤ C) (hwC : ∀ n, w n ≤ C) :
    Summable (fun n : ℕ => w n * |qSequence displacement n / (n : ℝ)|) ↔
      Summable (fun j => resolventMomentShell w (resolventApprox j) j) := by
  rw [summable_moment_iff_shell w hw]
  have hbase : Real.sqrt 2 / 3 < 1 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ Real.sqrt 2 / 3) hbase).mul_left
    (C * Real.sqrt zetaTwo * ‖displacement‖)
  have he := resolventMomentShell_error_le w C hC hwC
  constructor
  · intro hs
    apply Summable.of_nonneg_of_le (fun j => shell_nonneg hw _ j) _ (hs.add hg)
    intro j
    have ht := shell_triangle hw (resolventApprox j) displacement j
    rw [shell_sub_comm w displacement (resolventApprox j) j] at ht
    exact ht.trans (add_le_add le_rfl (he j))
  · intro hs
    apply Summable.of_nonneg_of_le (shell_nonneg hw displacement) _ (hs.add hg)
    intro j
    exact (shell_triangle hw displacement (resolventApprox j) j).trans
      (add_le_add le_rfl (he j))

/-- Damping normalized to match the repository's Q-probability convention. -/
def fullResolventDamping (δ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(leeLeongFullDisplacementExponent δ n)) / zetaTwo

private theorem full_damping_bounded (δ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, fullResolventDamping δ n ≤ C := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually
    (leeLeongFullProfile_sub_sqrt_eventually_mono δ))
  let w := fullResolventDamping δ
  have hw (n : ℕ) : 0 ≤ w n := div_nonneg (Real.exp_pos _).le zetaTwo_pos.le
  let H := ∑ i ∈ Finset.range N, w i
  have hH : 0 ≤ H := Finset.sum_nonneg (fun i _ => hw i)
  refine ⟨w N + H, add_nonneg (hw N) hH, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hmn := hN N le_rfl (n : ℝ) (by exact_mod_cast hn)
    have hle : w n ≤ w N := div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg hmn)) zetaTwo_pos.le
    exact hle.trans (le_add_of_nonneg_right hH)
  · have hx : w n ≤ H := Finset.single_le_sum (fun i _ => hw i)
        (Finset.mem_range.mpr (by omega : n < N))
    exact hx.trans (le_add_of_nonneg_left (hw N))

/-- The precise full Lee–Leong absolute moment is equivalent to a series
of explicit-depth dyadic shell masses. -/
theorem leeLeong_full_moment_iff_resolvent_shells (δ : ℝ) :
    Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullDisplacementExponent δ n))) * |qSequence displacement n|) ↔
      Summable (fun j => resolventMomentShell (fullResolventDamping δ) (resolventApprox j) j) := by
  obtain ⟨C, hC, hwC⟩ := full_damping_bounded δ
  rw [← summable_harmonic_iff_resolventMomentShell (fullResolventDamping δ)
    (fun n => div_nonneg (Real.exp_pos _).le zetaTwo_pos.le) C hC hwC]
  have hfun : (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullDisplacementExponent δ n))) * |qSequence displacement n|) =
      (fun n : ℕ => fullResolventDamping δ n * |qSequence displacement n / (n : ℝ)|) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [positiveQWeight]
    · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      simp only [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
      unfold positiveQWeight fullResolventDamping
      field_simp [hn', zetaTwo_pos.ne'] <;> ring
  rw [hfun]

/-- Only the Mertens input is needed in the direction toward RH. -/
theorem riemannHypothesis_of_leeLeong_full_resolvent_shells
    (hLL : LeeLeongMertensEstimate) (δ : ℝ) (hδ : 0 < δ)
    (hs : Summable (fun j =>
      resolventMomentShell (fullResolventDamping δ) (resolventApprox j) j)) :
    RiemannHypothesis :=
  riemannHypothesis_of_leeLeong_full_moment hLL δ hδ
    ((leeLeong_full_moment_iff_resolvent_shells δ).mpr hs)

/-- Under the indicated published inputs this finite-depth shell test is
equivalent to the Riemann hypothesis. -/
theorem riemannHypothesis_iff_leeLeong_full_resolvent_shells
    (hLL : LeeLeongMertensEstimate) (hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation)
    (δ : ℝ) (hδ : 0 < δ) :
    RiemannHypothesis ↔ Summable (fun j =>
      resolventMomentShell (fullResolventDamping δ) (resolventApprox j) j) :=
  (riemannHypothesis_iff_leeLeong_full_moment hLL hBD δ hδ).trans
    (leeLeong_full_moment_iff_resolvent_shells δ)

/-- An arithmetic target on a single unweighted finite shell per depth:
use the damping only at its left endpoint. -/
theorem riemannHypothesis_of_unweighted_resolvent_shell_budget
    (hLL : LeeLeongMertensEstimate) (δ : ℝ) (hδ : 0 < δ)
    (b : ℕ → ℝ) (hb : Summable b)
    (hbudget : ∀ᶠ j : ℕ in atTop, fullResolventDamping δ (2 ^ j) *
      resolventMomentShell (fun _ => 1) (resolventApprox j) j ≤ b j) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_leeLeong_full_resolvent_shells hLL δ hδ
  apply hb.abs.of_norm_bounded_eventually_nat
  have ht : Tendsto (fun j : ℕ => ((2 ^ j : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    simpa only [one_mul] using DyadicBlockDecomposition.tendsto_scaledDyadicEndpoint 1 (by decide)
  filter_upwards [ht.eventually (leeLeongFullProfile_sub_sqrt_eventually_mono δ), hbudget]
    with j hm hj
  have hw (n : ℕ) : 0 ≤ fullResolventDamping δ n := div_nonneg (Real.exp_pos _).le zetaTwo_pos.le
  rw [Real.norm_eq_abs, abs_of_nonneg (shell_nonneg hw _ j)]
  apply le_trans _ (hj.trans (le_abs_self _))
  unfold resolventMomentShell
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [one_mul]
  have hxy : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ j + i : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right (2 ^ j) i
  have hle : fullResolventDamping δ (2 ^ j + i) ≤ fullResolventDamping δ (2 ^ j) :=
    div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (hm _ hxy))) zetaTwo_pos.le
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

end RiemannResearch.RH.QMertensFirstMoment
