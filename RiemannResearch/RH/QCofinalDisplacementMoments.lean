/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCofinalHarmonicWitness
import RiemannResearch.RH.QMertensUniformDefectSlope
import RiemannResearch.Analysis.CofinalLogCutoffs
import RiemannResearch.Analysis.CofinalPrimeResiduePairing
import RiemannResearch.RH.QSignedChargeTail
import RiemannResearch.RH.MertensBaezDuarteConverse
import RiemannResearch.Analysis.FirstMomentTails
import Mathlib.Algebra.Order.Chebyshev
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity

/-!
# Cofinal one-sided harmonic prefixes of the projection displacement

The exact legal defect has the same signed pairing as the constant, and each
prime residue has zero signed pairing. A localized prime probe transfers a
one-sided harmonic prefix to that fixed pairing. Arbitrary logarithmic Mertens
savings suffice for arbitrarily sparse good cutoffs.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSignedTailRigidity
open QAnnihilatorTailEscape RiemannResearch.Analysis RiemannResearch.Analysis.CofinalMoments

/-- At each cutoff the smaller of the positive and negative harmonic masses. -/
def minimumHarmonicPrefix (X : ℕ) : ℝ :=
  min (harmonicSide 1 X) (harmonicSide (-1) X)

theorem harmonicSide_mono (ε : ℝ) : Monotone (harmonicSide ε) := by
  intro X Y h
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right h 1))
  intro n _ _
  exact div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)

theorem minimumHarmonicPrefix_mono : Monotone minimumHarmonicPrefix := by
  intro X Y h
  exact min_le_min (harmonicSide_mono 1 h) (harmonicSide_mono (-1) h)

theorem exists_best_sign (X : ℕ) :
    ∃ ε : ℝ, |ε| = 1 ∧ harmonicSide ε X = minimumHarmonicPrefix X := by
  rcases le_total (harmonicSide 1 X) (harmonicSide (-1) X) with h | h
  · exact ⟨1, abs_one, (min_eq_left h).symm⟩
  · exact ⟨-1, by norm_num, (min_eq_right h).symm⟩

/-- One finite inequality for the actual witness. The prefix takes the cheaper
sign at the outer cutoff; both error terms retain the full charge tails. -/
theorem witness_mean_le_local_harmonic_prefix
    (N p X Y : ℕ) (δ : ℝ) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hs : Squarefree (N + 1)) (hp : p.Prime) (hYX : Y ≤ X) (hYp : Y < p)
    (hlin : ∀ n : ℕ, n ≤ Y → |qSequence (defect N) n| ≤ δ * n) :
    |inner ℝ qOne witness| ≤ 2 * δ * (smoothingMoment + minimumHarmonicPrefix X / zetaTwo) + (δ * (p : ℝ)) * (∑' n : ℕ, if X < n then |signedCoefficient witness n| else 0) + (3 * (N : ℝ)) * (∑' n : ℕ, if Y < n then |signedCoefficient witness n| else 0) := by
  obtain ⟨ε, hε, hside⟩ := exists_best_sign X
  let c := -ε
  have hc : |c| = 1 := by simpa only [c, abs_neg] using hε
  let b := signedCoefficient witness
  have hsumm := (signedCoefficient_summable witness).mul_left c
  have hm := (annihilator_defect_hasSum witness witness_mem_orthogonal N hs).mul_left c
  have hz := (annihilator_prime_hasSum witness witness_mem_orthogonal p hp).mul_left c
  have h := pairing_le_local_residue_head (fun n => c * b n) (qSequence (defect N))
    X Y p (c * inner ℝ qOne witness) δ (3 * (N : ℝ)) hYX hYp hδ hsumm
    (by simpa only [b, mul_assoc] using hm)
    (by simpa only [b, mul_assoc, mul_zero] using hz) hlin
    (fun n _ => QMertensFirstMoment.abs_defect_le_three_mul N n hN)
  simp only [abs_mul, hc, one_mul] at h
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg zero_le_two hδ)
  simpa only [c, b, hside] using witness_prefix_le ε hε X

theorem scaled_charge_tail (X : ℕ) (R : ℝ) (hR : R ^ 2 ≤ (X : ℝ) + 1) :
    R * (∑' n : ℕ, if X < n then |signedCoefficient witness n| else 0) ≤
      ‖witness‖ ^ 2 + 2 / zetaTwo := by
  have e (n : ℕ) :
      (if n ∈ Finset.range (X + 1) then (0 : ℝ) else |signedCoefficient witness n|) =
      (if X < n then |signedCoefficient witness n| else 0) := by
    by_cases h : X < n
    · simp [Finset.mem_range, not_le.mpr h, h]
    · simp [Finset.mem_range, le_of_not_gt h, h]
  simpa only [e] using scaled_absoluteCoefficient_tail_le witness X R hR

/-- At an eighth-power cutoff a legal head of size comparable to k and one
prime test of size comparable to k ^ 4 control both complete tails. -/
theorem witness_mean_eighth_power_bound (A : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      |inner ℝ qOne witness| ≤
        (2 / (6 + Real.log (k : ℝ)) ^ A) * (smoothingMoment + minimumHarmonicPrefix (k ^ 8) / zetaTwo) + 2 * (‖witness‖ ^ 2 + 2 / zetaTwo) / (6 + Real.log (k : ℝ)) ^ A + 6 * (‖witness‖ ^ 2 + 2 / zetaTwo) / (k : ℝ) := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    (QMertensFirstMoment.eventually_abs_defect_le_div_shifted_log_pow A)
  filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk
  have h1 : 1 ≤ k := (le_max_right _ _).trans hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast h1
  obtain ⟨N, p, hs, hkN, hN2, hp, hYp, hp2⟩ :=
    exists_eighth_power_prime_scales (show 0 < k by omega)
  have hN : 0 < N := by omega
  let L := (6 + Real.log (k : ℝ)) ^ A
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hlin (n : ℕ) : |qSequence (defect N) n| ≤ (1 / L) * n := by
    have hNN := hk₀ N ((le_max_left _ _).trans (hk.trans hkN)) n
    have hpow : L ≤ (6 + Real.log (N : ℝ)) ^ A :=
      pow_le_pow_left₀ (by linarith : 0 ≤ 6 + Real.log (k : ℝ))
        (add_le_add_right (Real.log_le_log hkR (by exact_mod_cast hkN)) 6) A
    calc
      _ ≤ _ := hNN
      _ ≤ (n : ℝ) / L := div_le_div_of_nonneg_left (Nat.cast_nonneg n) hL hpow
      _ = _ := by ring
  have hXY : k ^ 4 ≤ k ^ 8 := Nat.pow_le_pow_right h1 (by decide)
  have h := witness_mean_le_local_harmonic_prefix N p (k ^ 8) (k ^ 4) (1 / L)
    hN (one_div_nonneg.mpr hL.le) hs.squarefree hp hXY hYp (fun n _ => hlin n)
  let T := ‖witness‖ ^ 2 + 2 / zetaTwo
  let tailB (X : ℕ) := ∑' n : ℕ, if X < n then |signedCoefficient witness n| else 0
  have ht (X : ℕ) : 0 ≤ tailB X :=
    tsum_nonneg (fun n => by split <;> simp [abs_nonneg])
  have h8 : (k : ℝ) ^ 4 * tailB (k ^ 8) ≤ T := by
    apply scaled_charge_tail
    push_cast
    nlinarith only [show 0 ≤ (1 : ℝ) by norm_num,
      show ((k : ℝ) ^ 4) ^ 2 = (k : ℝ) ^ 8 by ring]
  have h4 : (k : ℝ) ^ 2 * tailB (k ^ 4) ≤ T := by
    apply scaled_charge_tail
    push_cast
    nlinarith only [show 0 ≤ (1 : ℝ) by norm_num,
      show ((k : ℝ) ^ 2) ^ 2 = (k : ℝ) ^ 4 by ring]
  have hpR : (p : ℝ) ≤ 2 * (k : ℝ) ^ 4 := by exact_mod_cast hp2
  have hNR : (N : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hN2
  have ht8 : (1 / L * (p : ℝ)) * tailB (k ^ 8) ≤ 2 * T / L := by
    apply (le_div_iff₀ hL).2
    calc
      _ = (p : ℝ) * tailB (k ^ 8) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hpR (ht _)
      _ ≤ 2 * T := by dsimp only [tailB] at *; linarith
  have ht4 : (3 * (N : ℝ)) * tailB (k ^ 4) ≤ 6 * T / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    calc
      _ ≤ (3 * (2 * (k : ℝ)) * tailB (k ^ 4)) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNR (by norm_num)) (ht _)) hkR.le
      _ = 6 * ((k : ℝ) ^ 2 * tailB (k ^ 4)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by norm_num)
  change _ ≤ (2 / L) * _ + 2 * T / L + 6 * T / (k : ℝ)
  rw [show 2 / L = 2 * (1 / L) by ring]
  exact h.trans (add_le_add (add_le_add le_rfl ht8) ht4)

/-- Vanishing of the faithful residual is equivalent to a polylogarithmic
bound for the smaller physical harmonic mass at arbitrarily large cutoffs. -/
theorem residual_zero_iff_cofinal_harmonic_polylog :
    limitingResidual = 0 ↔ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B := by
  constructor
  · intro hr
    refine ⟨0, 0, le_rfl, le_rfl, (Eventually.of_forall ?_).frequently⟩
    intro X
    simp [minimumHarmonicPrefix, harmonicSide, displacement_eq_zero_of_residual_eq_zero hr,
      show qSequence (0:QHilbert) = 0 from map_zero qSequenceLinear]
  · rintro ⟨B, C, hB, hC, hgood⟩
    obtain ⟨A, hBA⟩ := exists_nat_ge B
    let T := ‖witness‖ ^ 2 + 2 / zetaTwo
    let C' := (C * (16 : ℝ) ^ B) / zetaTwo
    have hT : 0 ≤ T := add_nonneg (sq_nonneg _) (div_nonneg zero_le_two zetaTwo_pos.le)
    have hC' : 0 ≤ C' := div_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) zetaTwo_pos.le
    apply residual_eq_zero_of_witness_mean_zero
    apply eq_zero_of_frequently_abs_le (f := fun k : ℕ =>
      (2 / (6 + Real.log (k : ℝ)) ^ (A + 2)) * (smoothingMoment + C'*(Real.log (k : ℝ)) ^ B) + 2 * T / (6 + Real.log (k : ℝ)) ^ (A + 2) + 6 * T / (k : ℝ)) _ (tendsto_budget A B _ C' T hB hBA
        smoothingMoment_nonneg hC' hT)
    apply ((frequently_eighth_power_log_bound minimumHarmonicPrefix_mono hB hC hgood).and_eventually
      ((witness_mean_eighth_power_bound (A + 2)).and (eventually_ge_atTop 1))).mono
    rintro k ⟨h, hb, hk⟩
    have hl : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
    refine hb.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    simpa only [C', div_mul_eq_mul_div] using div_le_div_of_nonneg_right h zetaTwo_pos.le

/-- A polylogarithmic bound along arbitrary cofinal cutoffs for either sign
of the actual physical displacement implies Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_cofinal_harmonic_polylog (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis := by
  have hr := residual_zero_iff_cofinal_harmonic_polylog.mpr ⟨B, C, hB, hC, h⟩
  have hm : qOne ∈ closure := Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSignedTailRigidity
open QAnnihilatorTailEscape RiemannResearch.Analysis

/-- A positive finite mixture of prime remainders, with the cutoff and the
legal head chosen independently. The tail loses only a harmonic factor. -/
theorem witness_mean_le_capped_harmonic_prefix (N X : ℕ) (δ : ℝ) (hN : 0<N)
    (hδ : 0 ≤ δ) (hs : Squarefree (N + 1))
    (hlin : ∀ n : ℕ, |qSequence (defect N) n| ≤ δ * n) :
    |inner ℝ qOne witness| ≤ 2 * δ * (smoothingMoment + minimumHarmonicPrefix X / zetaTwo) + (2 * ((3 * (N : ℝ)) * (harmonic (X + 1) : ℝ)) + 3 * (N : ℝ)) * (∑' n : ℕ, if X<n then |signedCoefficient witness n| else 0) := by
  obtain ⟨ε, hε, hside⟩ := exists_best_sign X
  let c := -ε
  have hc : |c|=1 := by simpa only [c, abs_neg] using hε
  let b := signedCoefficient witness
  have hm := (annihilator_defect_hasSum witness witness_mem_orthogonal N hs).mul_left c
  have hz (p : ℕ) (hp : p.Prime) :=
    (annihilator_prime_hasSum witness witness_mem_orthogonal p hp).mul_left c
  have h := pairing_le_clipped_residue_mixture (fun n => c * b n) (qSequence (defect N)) X
    (c * inner ℝ qOne witness) δ (3 * (N : ℝ)) hδ ((signedCoefficient_summable witness).mul_left c)
    (by simpa only [b, mul_assoc] using hm)
    (fun p hp => by simpa only [b, mul_assoc, mul_zero] using hz p hp)
    hlin (fun n => QMertensFirstMoment.abs_defect_le_three_mul N n hN)
  simp only [abs_mul, hc, one_mul] at h
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg zero_le_two hδ)
  simpa only [c, b, hside] using witness_prefix_le ε hε X

theorem witness_charge_tail_le_div_sqrt (X : ℕ) :
    (∑' n : ℕ, if X<n then |signedCoefficient witness n| else 0) ≤ (‖witness‖ ^ 2 + 2 / zetaTwo) / Real.sqrt ((X : ℝ) + 1) := by
  apply (le_div_iff₀ (Real.sqrt_pos.2 (by positivity))).mpr
  rw [mul_comm]
  exact scaled_charge_tail X _ (Real.sq_sqrt (by positivity)).le

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoOptimizerStage ZetaTwoHilbert

/-- Any fixed exponent and nonnegative coefficient give the same criterion for
vanishing of the projection residual. -/
theorem residual_zero_iff_fixed_cofinal_harmonic_polylog (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    limitingResidual = 0 ↔
      ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B := by
  constructor
  · intro hr
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
    have hh : minimumHarmonicPrefix X = 0 := by
      simp [minimumHarmonicPrefix, harmonicSide, displacement_eq_zero_of_residual_eq_zero hr,
        show qSequence (0:QHilbert) = 0 from map_zero qSequenceLinear]
    rw [hh]
    exact mul_nonneg hC (Real.rpow_nonneg hlog _)
  · exact fun h => residual_zero_iff_cofinal_harmonic_polylog.mpr ⟨B, C, hB, hC, h⟩

/-- A nonzero residual forces the minimum of the two sign masses to escape every
fixed polylogarithmic scale over the entire sequence of cutoffs. -/
theorem minimumHarmonicPrefix_div_log_tendsto_of_residual_ne_zero
    (hr : limitingResidual ≠ 0) (B : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun X : ℕ => minimumHarmonicPrefix X / (Real.log (X : ℝ)) ^ B) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  let C' := max C 0
  have hn : ¬ ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ C' * (Real.log (X : ℝ)) ^ B :=
    fun h => hr ((residual_zero_iff_fixed_cofinal_harmonic_polylog B C' hB (le_max_right _ _)).mpr h)
  have hgt : ∀ᶠ X : ℕ in atTop, C' * (Real.log (X : ℝ)) ^ B < minimumHarmonicPrefix X := by
    simpa only [Filter.Frequently, not_not, not_le] using hn
  have hl : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hgt, hl.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hlog
  exact (le_max_left C 0).trans ((le_div_iff₀ (Real.rpow_pos_of_pos hlog _)).mpr hX.le)

/-- Failure of RH forces both of the physical sign masses to grow faster
than every fixed power of the logarithm. -/
theorem minimumHarmonicPrefix_div_log_tendsto_of_not_RH
    (hRH : ¬ RiemannHypothesis) (B : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun X : ℕ => minimumHarmonicPrefix X / (Real.log (X : ℝ)) ^ B) atTop atTop :=
  minimumHarmonicPrefix_div_log_tendsto_of_residual_ne_zero
    (fun hr => hRH (QMertensFirstMoment.rh_of_zero_projection_residual hr)) B hB

/-- Báez-Duarte's natural-dilation approximation (Theorem 2) supplies the
converse from RH to squarefree projection residual zero. The resulting
physical equivalence is valid for each fixed nonnegative exponent and coefficient. -/
theorem riemannHypothesis_iff_fixed_cofinal_harmonic_polylog
    (hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    RiemannHypothesis ↔
      ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B :=
  ⟨fun hRH => (residual_zero_iff_fixed_cofinal_harmonic_polylog B C hB hC).mp
    (QMertensFirstMoment.residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH),
   riemannHypothesis_of_cofinal_harmonic_polylog B C hB hC⟩

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

/-! # An unconditional sub-square-root bound for absolute harmonic prefixes

The weighted square summability of any physical Q-vector, without a Mertens
or arithmetic sign assumption, gives a little-o bound on its harmonic mass.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis

/-- A square-summable sequence has absolute partial sums of size `o(√X)`.
This nonnegative formulation also applies to the coordinatewise absolute values. -/
theorem sum_range_div_sqrt_tendsto_zero_of_summable_sq (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hs : Summable (fun j => a j ^ 2)) :
    Tendsto (fun X : ℕ => (∑ j ∈ Finset.range X, a j) / Real.sqrt (X : ℝ))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := half_pos hε
  have hsq := sq_pos_of_pos hh
  obtain ⟨K, hK⟩ := ((rawTail_tendsto_zero hs).eventually (gt_mem_nhds hsq)).exists
  let A := ∑ j ∈ Finset.range K, a j
  have hrt : Tendsto (fun X : ℕ => Real.sqrt (X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop (1 : ℕ),
    (hrt.const_div_atTop A).eventually (gt_mem_nhds hh)] with X hKX hX hp
  let L := X - K
  let T := ∑ j ∈ Finset.range L, a (j + K)
  have hsplit : (∑ j ∈ Finset.range X, a j) = A + T := by
    change (∑ j ∈ Finset.range X, a j) = (∑ j ∈ Finset.range K, a j) + ∑ j ∈ Finset.range L, a (j + K)
    conv_lhs => rw [show X = K + L by dsimp [L]; omega, Finset.sum_range_add]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [Nat.add_comm K j])
  have hpart : (∑ j ∈ Finset.range L, a (j + K) ^ 2) ≤ ∑' j : ℕ, a (j + K) ^ 2 :=
    ((summable_nat_add_iff K).mpr hs).sum_le_tsum _ (fun _ _ => sq_nonneg _)
  have hcs : T ^ 2 ≤ (L : ℝ) * ∑ j ∈ Finset.range L, a (j + K) ^ 2 := by
    simpa only [T, Finset.card_range] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.range L) (f := fun j => a (j + K)))
  have hpow : T ^ 2 ≤ (Real.sqrt (X : ℝ) * (ε / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg X)]
    exact hcs.trans (mul_le_mul (by exact_mod_cast (Nat.sub_le X K)) (hpart.trans hK.le)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg X))
  have htn : 0 ≤ T := Finset.sum_nonneg (fun j _ => ha (j + K))
  have htx := (sq_le_sq₀ htn (mul_nonneg (Real.sqrt_nonneg _) hh.le)).mp hpow
  have hrt₀ : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < X by omega))
  have hsmall : T / Real.sqrt (X : ℝ) ≤ ε / 2 := (div_le_iff₀ hrt₀).mpr (by
    simpa only [mul_comm] using htx)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg
    (Finset.sum_nonneg (fun j _ => ha j)) hrt₀.le), hsplit, add_div]
  linarith only [hp, hsmall]

end RiemannResearch.Analysis

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability

/-- The complete absolute physical harmonic mass is sub-square-root for every
Q-vector, including the actual displacement. -/
theorem absolute_harmonicPrefix_div_sqrt_tendsto_zero (u : QHilbert) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.range (X + 1), |qSequence u n| / (n : ℝ)) / Real.sqrt (X : ℝ)) atTop (𝓝 0) := by
  let a := fun j : ℕ => |qSequence u (j + 1)| / ((j : ℝ) + 1)
  have ha (j : ℕ) : 0 ≤ a j := div_nonneg (abs_nonneg _) (by positivity)
  have hs : Summable (fun j => a j ^ 2) := by
    have he := (summable_nat_add_iff (f := fun n => positiveQWeight n * qSequence u n ^ 2) 1).mpr
      (qSequence_square_summable u)
    apply (he.mul_left zetaTwo).congr
    intro j
    dsimp only [a, positiveQWeight]
    rw [Nat.cast_add, Nat.cast_one, div_pow, sq_abs]
    field_simp [zetaTwo_pos.ne', (show (j : ℝ) + 1 ≠ 0 by positivity)]
  have hpre (X : ℕ) : (∑ n ∈ Finset.range (X + 1), |qSequence u n| / (n : ℝ)) =
      ∑ j ∈ Finset.range X, a j := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, div_zero, add_zero, a]
  simpa only [hpre] using Analysis.sum_range_div_sqrt_tendsto_zero_of_summable_sq a ha hs

/-- The unconditional estimate on the physical displacement's smaller sign. -/
theorem minimumHarmonicPrefix_div_sqrt_tendsto_zero :
    Tendsto (fun X : ℕ => minimumHarmonicPrefix X / Real.sqrt (X : ℝ)) atTop (𝓝 0) := by
  have hn (ε : ℝ) (X : ℕ) : 0 ≤ harmonicSide ε X :=
    Finset.sum_nonneg (fun n _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n))
  apply squeeze_zero (fun X => div_nonneg (le_min (hn _ X) (hn _ X)) (Real.sqrt_nonneg _)) _
    (absolute_harmonicPrefix_div_sqrt_tendsto_zero displacement)
  intro X
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply (min_le_left (harmonicSide 1 X) _).trans
  apply Finset.sum_le_sum
  intro n _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  simp only [one_mul]
  exact max_le (le_abs_self _) (abs_nonneg _)

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
