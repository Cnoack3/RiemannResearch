/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PointwiseEnergyDivergence
import RiemannResearch.Analysis.WeightedHeadEnergy
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.Analysis.LogSquareTail
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QHilbertConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cofinal finite-head budgets for convergent Q vectors

Source: the user-provided squarefree moving-head continuation. These statements
are independent of squarefree legality and RH. A polylogarithmic pointwise head
envelope supplies a common head budget; a cofinally bounded head budget supplies
finite weighted energy of the limit.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPolylogTailEnergy
open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis RiemannResearch.Analysis.LogTailWeights

def weightedHeadEnergy (k H : ℕ) (u : QHilbert) : ℝ :=
  ∑ n ∈ Finset.range (H + 1), polylogWeightedEnergyTerm k u n

/-- The signed finite cross term; it need not vanish under the new weight. -/
def weightedHeadCross (k H : ℕ) (f g : QHilbert) : ℝ :=
  ∑ n ∈ Finset.range (H + 1), polylogTailProfile k n * positiveQWeight n *
    qSequence f n * qSequence g n

theorem weightedHeadEnergy_add_exact (k H : ℕ) (f g : QHilbert) :
    weightedHeadEnergy k H (f + g) = weightedHeadEnergy k H f +
      weightedHeadEnergy k H g + 2 * weightedHeadCross k H f g := by
  have hseq (n : ℕ) : qSequence (f + g) n = qSequence f n + qSequence g n := by
    change qSequenceLinear (f + g) n = _
    rw [map_add]
    rfl
  unfold weightedHeadEnergy weightedHeadCross
  simp only [polylogWeightedEnergyTerm, hseq]
  calc
    _ = ∑ n ∈ Finset.range (H + 1),
        (polylogTailProfile k n * positiveQWeight n * qSequence f n ^ 2 +
          polylogTailProfile k n * positiveQWeight n * qSequence g n ^ 2 +
          2 * (polylogTailProfile k n * positiveQWeight n *
            qSequence f n * qSequence g n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- A finite weighted head costs at most its endpoint weight times the
complete Q energy; no physical tail is substituted for that Q energy. -/
theorem weightedHeadEnergy_le_profile_norm_sq (k H : ℕ) (f : QHilbert) :
    weightedHeadEnergy k H f ≤ polylogTailProfile k H * ‖f‖ ^ 2 := by
  unfold weightedHeadEnergy
  calc
    _ ≤ ∑ n ∈ Finset.range (H + 1), polylogTailProfile k H *
        (positiveQWeight n * qSequence f n ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hle : n ≤ H := by have h := Finset.mem_range.mp hn; omega
      have hp := mul_le_mul_of_nonneg_right (polylogTailProfile_monotone k hle)
        (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg (qSequence f n)))
      simpa only [polylogWeightedEnergyTerm, mul_assoc] using hp
    _ = polylogTailProfile k H *
        (∑ n ∈ Finset.range (H + 1), positiveQWeight n * qSequence f n ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ polylogTailProfile k H *
        (∑' n : ℕ, positiveQWeight n * qSequence f n ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (polylogTailProfile_nonneg k H)
      exact (qSequence_square_summable f).sum_le_tsum (Finset.range (H + 1))
        (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
    _ = polylogTailProfile k H * ‖f‖ ^ 2 := by rw [← qNorm_weighted_sq]

/-- The earlier all-stage pointwise condition implies the new energy budget
with one common finite constant, before any limiting argument. -/
theorem polylog_head_envelope_implies_uniform_head_budget
    (u : ℕ → QHilbert) (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ N n : ℕ, 0 < n → n ≤ N →
      |qSequence (u N) n| ≤ C*(6+Real.log (n : ℝ))^m) :
    ∃ D : ℝ, ∀ N : ℕ, weightedHeadEnergy (2*m+2) N (u N) ≤ D := by
  let a : ℕ → ℝ := fun n =>
    (C^2/zetaTwo) * (1 / ((n : ℝ)*(6+Real.log (n : ℝ)) ^ 2))
  have hs0 : Summable (fun n : ℕ =>
      1 / ((n : ℝ)*(6+Real.log (n : ℝ)) ^ 2)) := by
    simpa only [Real.rpow_two] using summable_shifted_log_square
  have hs : Summable a := hs0.mul_left (C^2/zetaTwo)
  refine ⟨∑' n : ℕ, a n, ?_⟩
  intro N
  have hp : weightedHeadEnergy (2*m+2) N (u N) ≤
      ∑ n ∈ Finset.range (N+1), a n := by
    apply Finset.sum_le_sum
    intro n hn
    apply polylogWeightedEnergyTerm_le_log_square
    by_cases hn0 : n = 0
    · subst n
      simp only [qSequence_zero, abs_zero, Nat.cast_zero, Real.log_zero, add_zero]
      positivity
    · exact hu N n (Nat.pos_of_ne_zero hn0) (by
        have hh := Finset.mem_range.mp hn
        omega)
  exact hp.trans (hs.sum_le_tsum (Finset.range (N+1)) (fun n _ => by
    dsimp [a]
    have hz := zetaTwo_pos
    positivity))

theorem weightedEnergy_summable_of_frequently_moving_head_bound
    (k : ℕ) (u : ℕ → QHilbert) (v : QHilbert)
    (hu : Tendsto u atTop (𝓝 v))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hbound : ∃ᶠ N : ℕ in atTop,
      weightedHeadEnergy k (H N) (u N) ≤ C) :
    Summable (polylogWeightedEnergyTerm k v) ∧
      (∑' n : ℕ, polylogWeightedEnergyTerm k v n) ≤ C := by
  have hlim (n : ℕ) : Tendsto
      (fun N => polylogWeightedEnergyTerm k (u N) n)
      atTop (𝓝 (polylogWeightedEnergyTerm k v n)) := by
    have h := (qSequence_tendsto_of_tendsto hu n).pow 2
    simpa only [polylogWeightedEnergyTerm] using
      h.const_mul (polylogTailProfile k n * positiveQWeight n)
  have hhead : Tendsto (fun N => H N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [hH.eventually (eventually_ge_atTop M)] with N hN
    omega
  exact summable_of_frequently_head_bound
    (fun N n => polylogWeightedEnergyTerm k (u N) n)
    (polylogWeightedEnergyTerm k v)
    (fun N n => polylogWeightedEnergyTerm_nonneg k (u N) n)
    hlim (fun N => H N + 1) hhead C hbound

/-- Hilbert convergence suffices for a normalized moving-head energy limit.
This does not assert a bounded unnormalized weighted energy. -/
theorem weightedHeadEnergy_div_profile_tendsto_zero
    (k : ℕ) (u : ℕ → QHilbert) (v : QHilbert)
    (hu : Tendsto u atTop (𝓝 v))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun N => weightedHeadEnergy k (H N) (u N) /
      polylogTailProfile k (H N)) atTop (𝓝 0) := by
  let E : ℕ → ℕ → ℝ := fun j n =>
    positiveQWeight n * qSequence (u j) n ^ 2
  let e : ℕ → ℝ := fun n => positiveQWeight n * qSequence v n ^ 2
  have hE (j n : ℕ) : 0 ≤ E j n :=
    mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)
  have he (n : ℕ) : 0 ≤ e n :=
    mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)
  have habs (j n : ℕ) : |E j n - e n| =
      positiveQWeight n * |qSequence (u j) n ^ 2 - qSequence v n ^ 2| := by
    dsimp [E, e]
    rw [← mul_sub, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n)]
  have hd (j : ℕ) : Summable (fun n => |E j n - e n|) := by
    simpa only [habs] using qSquareL1Dist_summable (u j) v
  have hlim : Tendsto (fun j => ∑' n, |E j n - e n|) atTop (𝓝 0) := by
    simpa only [qSquareL1Dist, habs] using qSquareL1Dist_tendsto_zero hu
  have ht := normalized_weighted_head_tendsto_zero_of_l1
    (polylogTailProfile k) (polylogTailProfile_nonneg k)
    (polylogTailProfile_monotone k) (polylogTailProfile_tendsto_atTop k)
    E e hE he (qSequence_square_summable v) hd hlim H hH
  convert ht using 1
  funext j
  congr 1
  unfold weightedHeadEnergy
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [polylogWeightedEnergyTerm, E]
  ring

/-- Uniformity over every vector in a norm-convergent Q family. -/
theorem weightedHeadEnergy_div_profile_uniformly_small
    (k : ℕ) (u : ℕ → QHilbert) (v : QHilbert)
    (hu : Tendsto u atTop (𝓝 v)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℕ in atTop, ∀ N : ℕ,
      weightedHeadEnergy k H (u N) / polylogTailProfile k H ≤ ε := by
  let E : ℕ → ℕ → ℝ := fun j n =>
    positiveQWeight n * qSequence (u j) n ^ 2
  let e : ℕ → ℝ := fun n => positiveQWeight n * qSequence v n ^ 2
  have hE (j n : ℕ) : 0 ≤ E j n :=
    mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)
  have he (n : ℕ) : 0 ≤ e n :=
    mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)
  have habs (j n : ℕ) : |E j n - e n| =
      positiveQWeight n * |qSequence (u j) n ^ 2 - qSequence v n ^ 2| := by
    dsimp [E, e]
    rw [← mul_sub, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n)]
  have hd (j : ℕ) : Summable (fun n => |E j n - e n|) := by
    simpa only [habs] using qSquareL1Dist_summable (u j) v
  have hlim : Tendsto (fun j => ∑' n, |E j n - e n|) atTop (𝓝 0) := by
    simpa only [qSquareL1Dist, habs] using qSquareL1Dist_tendsto_zero hu
  have ht := normalized_weighted_head_uniformly_small_of_l1
    (polylogTailProfile k) (polylogTailProfile_nonneg k)
    (polylogTailProfile_monotone k) (polylogTailProfile_tendsto_atTop k)
    E e hE he (qSequence_square_summable v) hd hlim ε hε
  filter_upwards [ht] with H hH
  intro N
  simpa only [weightedHeadEnergy, polylogWeightedEnergyTerm, E, mul_assoc] using hH N

/-- Equivalent undivided uniform sub-profile estimate. -/
theorem weightedHeadEnergy_uniform_subprofile
    (k : ℕ) (u : ℕ → QHilbert) (v : QHilbert)
    (hu : Tendsto u atTop (𝓝 v)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℕ in atTop, ∀ N : ℕ,
      weightedHeadEnergy k H (u N) ≤ ε * polylogTailProfile k H := by
  have hsmall := weightedHeadEnergy_div_profile_uniformly_small k u v hu ε hε
  have hpos := (polylogTailProfile_tendsto_atTop k).eventually (eventually_gt_atTop 0)
  filter_upwards [hsmall, hpos] with H hH hHp
  intro N
  exact (div_le_iff₀ hHp).mp (hH N)

/-- Sign change preserves the finite weighted energy. -/
theorem weightedHeadEnergy_neg (k H : ℕ) (f : QHilbert) :
    weightedHeadEnergy k H (-f) = weightedHeadEnergy k H f := by
  unfold weightedHeadEnergy
  apply Finset.sum_congr rfl
  intro n hn
  have hseq : qSequence (-f) n = -qSequence f n := by
    change qSequenceLinear (-f) n = _
    rw [map_neg]
    rfl
  simp only [polylogWeightedEnergyTerm, hseq, neg_sq]

/-- The squared triangle estimate follows after retaining and bounding
the signed finite cross term. -/
theorem weightedHeadEnergy_add_le (k H : ℕ) (f g : QHilbert) :
    weightedHeadEnergy k H (f + g) ≤
      2 * weightedHeadEnergy k H f + 2 * weightedHeadEnergy k H g := by
  have hc : 2 * weightedHeadCross k H f g ≤
      weightedHeadEnergy k H f + weightedHeadEnergy k H g := by
    unfold weightedHeadCross weightedHeadEnergy
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hw : 0 ≤ polylogTailProfile k n * positiveQWeight n :=
      mul_nonneg (polylogTailProfile_nonneg k n) (positiveQWeight_nonneg n)
    dsimp only [polylogWeightedEnergyTerm]
    nlinarith [mul_nonneg hw (sq_nonneg (qSequence f n - qSequence g n))]
  rw [weightedHeadEnergy_add_exact]
  linarith

end RiemannResearch.RH.QPolylogTailEnergy
