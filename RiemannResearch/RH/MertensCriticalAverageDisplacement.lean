/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MertensAveragePowerEndpoint
import RiemannResearch.RH.MertensFirstMomentEnvelope
import RiemannResearch.RH.MertensPowerCriterion
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QSquarefreeResidualTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Cesàro displacement growth at the critical Mertens exponent

The finite signed Schur pairing of the canonical heads is eventually constant
along a cofinal family of legal cutoffs. The critical power row bound tests
this identity against the actual projection displacement.
-/
noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open RiemannResearch.Analysis ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QAnnihilatorTailEscape QSquarefreeResidualTail ZetaTwoOptimizerStage

/-- Little-o for the average at the critical exponent forces RH under the two-part power
estimate for a cofinal family of canonical heads. -/
theorem riemannHypothesis_of_power_defect_and_critical_prefix
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (a β C : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hcrit : (1+a)*β = a)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hdef : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      |1 - Pareto.canonicalMobiusHead (q j) (n+1)| ≤
        C * min (q j : ℝ) (((n:ℝ)+1) * (q j:ℝ)^(-a)))
    (hd : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
      ∑ n ∈ Finset.range k, |qSequence displacement (n+1)| ≤ η * (k:ℝ)^(1+β)) : RiemannHypothesis := by
  let D (j n : ℕ) := qSequence (defect (q j)) (n+1)
  have hD (j n : ℕ) : D j n = 1 - Pareto.canonicalMobiusHead (q j) (n+1) := by
    change qSequenceLinear (qOne - QMobiusExactHead.exactHead (q j)) (n+1) = _
    rw [map_sub]
    change qSequence qOne (n+1) - qSequence (QMobiusExactHead.exactHead (q j)) (n+1) = _
    rw [qSequence_qOne, QMobiusExactHead.exactHead_sequence]
    simp [qOneSequence]
  have hhead (j n : ℕ) (hn : n+1 ≤ q j) : D j n = 0 := by
    rw [hD, Pareto.canonicalMobiusHead_exact (q j) (n+1) (by omega) hn, sub_self]
  let w (n : ℕ) := qSequence witness (n+1)
  obtain ⟨A,hA⟩ := B_physical_bounded pResidual
  have hbound (n : ℕ) : |w n| ≤ A + |qSequence displacement (n+1)| := by
    have he : w n = qSequence (B pResidual) (n+1) - qSequence displacement (n+1) := by
      change qSequenceLinear (B pResidual - displacement) (n+1) = _
      rw [map_sub]
      rfl
    rw [he]
    have hh := abs_sub_le (qSequence (B pResidual) (n+1)) 0 (qSequence displacement (n+1))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    linarith only [hh,hA (n+1)]
  have hw (η : ℝ) (hη : 0 < η) : ∀ᶠ k : ℕ in atTop,
      ∑ n ∈ Finset.range k, |w n| ≤ η * (k:ℝ)^(1+β) := by
    have hp : Tendsto (fun k : ℕ => (k:ℝ)^β) atTop atTop :=
      (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
    have hη2 : 0 < η/2 := half_pos hη
    filter_upwards [hp.eventually (eventually_ge_atTop (A/(η/2))), hd (η/2) hη2,
      eventually_ge_atTop (1:ℕ)] with k hkp hkd hk
    have hkr : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hkp' := mul_le_mul_of_nonneg_left ((div_le_iff₀ hη2).mp hkp) hkr.le
    have hE : (k:ℝ)^(1+β) = (k:ℝ) * (k:ℝ)^β := by rw [Real.rpow_add hkr, Real.rpow_one]
    have hB : (k:ℝ)*A ≤ (η/2)*(k:ℝ)^(1+β) := by rw [hE]; linarith only [hkp']
    calc
      _ ≤ ∑ n ∈ Finset.range k, (A+|qSequence displacement (n+1)|) :=
        Finset.sum_le_sum (fun n _ => hbound n)
      _ = (k:ℝ)*A + ∑ n ∈ Finset.range k, |qSequence displacement (n+1)| := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by linarith only [hB,hkd]
  have hlim := (power_defect_pairing_tendsto_zero_of_critical_prefix D w q a β C
    ha hβ hβ1 hC hcrit hq hhead (by simpa only [hD] using hdef) hw).const_mul (1/zetaTwo)
  simp only [mul_zero] at hlim
  have heq (j : ℕ) : (1/zetaTwo) * (∑' n : ℕ, D j n * w n / ((n:ℝ)+1)^2) =
      inner ℝ (defect (q j)) witness := by
    rw [qInner_weighted, (qSequence_product_summable (defect (q j)) witness).tsum_eq_zero_add]
    simp only [qSequence_zero, mul_zero, zero_add, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [D, w, positiveQWeight, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
    ring
  have hevent : (fun j => (1/zetaTwo) * (∑' n : ℕ, D j n * w n / ((n:ℝ)+1)^2)) =ᶠ[atTop]
      (fun _ : ℕ => inner ℝ qOne witness) := by
    filter_upwards [hlegal] with j hj
    rw [heq, defect, inner_sub_left, Submodule.inner_right_of_mem_orthogonal
      (squarefree_exactHead_mem_closure (q j) hj) witness_mem_orthogonal, sub_zero]
  exact QMertensFirstMoment.rh_of_zero_projection_residual
    (residual_eq_zero_of_witness_mean_zero
      (tendsto_nhds_unique tendsto_const_nhds (hlim.congr' hevent)))

/-- An ordinary Mertens power estimate and critical little-o growth of the unsigned
displacement prefix imply RH. The condition permits exceptional physical sites. -/
theorem riemannHypothesis_of_mertens_power_and_critical_prefix
    (s C : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 0 < n →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M (n : ℝ)| ≤ C*(n:ℝ)^s)
    (hd : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
      ∑ n ∈ Finset.range k, |qSequence displacement (n+1)| ≤ η * (k:ℝ)^(1+(1-s)/(2-s))) :
    RiemannHypothesis := by
  obtain ⟨q,K,hq,hK,hlegal,hdef⟩ := exists_cofinal_power_defect_of_mertens_power s C hs hs1 hC hM
  have hpos : 0 < 2 - s := by linarith
  apply riemannHypothesis_of_power_defect_and_critical_prefix q hq (1-s) ((1-s)/(2-s)) K
    (by linarith) (div_pos (sub_pos.mpr hs1) hpos) ((div_lt_one hpos).2 (by linarith))
    hK _ hlegal hdef hd
  field_simp [hpos.ne']
  <;> ring

/-- An ordinary big-O estimate below the critical average exponent implies
the endpoint little-o estimate. The displacement hypothesis allows arbitrary
individual sites. -/
theorem riemannHypothesis_of_mertens_power_and_subcritical_prefix
    (s γ C D : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hγ : γ < (1-s)/(2-s))
    (hM : ∀ n : ℕ, 0 < n →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M (n : ℝ)| ≤ C * (n : ℝ) ^ s)
    (hd : ∀ᶠ k : ℕ in atTop, ∑ n ∈ Finset.range k, |qSequence displacement (n+1)| ≤
      D * (k : ℝ) ^ (1+γ)) : RiemannHypothesis := by
  let β := (1-s)/(2-s)
  have hg : 0 < β-γ := sub_pos.mpr hγ
  apply riemannHypothesis_of_mertens_power_and_critical_prefix s C hs hs1 hC hM
  intro η hη
  have hp : Tendsto (fun k : ℕ => (k : ℝ) ^ (β-γ)) atTop atTop :=
    (tendsto_rpow_atTop hg).comp tendsto_natCast_atTop_atTop
  filter_upwards [hd, hp.eventually (eventually_ge_atTop (D/η)),
    eventually_ge_atTop (1 : ℕ)] with k hk hkη hk1
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hD : D ≤ (k : ℝ) ^ (β-γ) * η := (div_le_iff₀ hη).mp hkη
  change _ ≤ η * (k : ℝ) ^ (1+β)
  apply hk.trans
  calc
    _ ≤ ((k : ℝ) ^ (β-γ) * η) * (k : ℝ) ^ (1+γ) :=
      mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hk0.le _)
    _ = η * (k : ℝ) ^ (1+β) := by
      have hpow : (k : ℝ) ^ (β - γ) * (k : ℝ) ^ (1 + γ) = (k : ℝ) ^ (1 + β) := by
        rw [← Real.rpow_add hk0, show β - γ + (1 + γ) = 1 + β by ring]
      rw [← hpow]
      ring

/-- A rational specialization for displacements with absolute prefix
O(X^(10/9)). Liu, arXiv:2610.12234v2, gives a zero-free boundary below
0.87499. Gerhold, Acta Arith. 142 (2010), Proposition 3, then yields the
Mertens premise on paper. The premise is explicit in this project. -/
theorem riemannHypothesis_of_mertens_87499_and_ten_ninths_prefix
    (C D : ℝ) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 0 < n →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M (n : ℝ)| ≤
        C * (n : ℝ) ^ (87499 / 100000 : ℝ))
    (hd : ∀ᶠ k : ℕ in atTop, ∑ n ∈ Finset.range k, |qSequence displacement (n+1)| ≤
      D * (k : ℝ) ^ (10 / 9 : ℝ)) : RiemannHypothesis := by
  apply riemannHypothesis_of_mertens_power_and_subcritical_prefix
    (87499 / 100000) (1 / 9) C D (by norm_num) (by norm_num) hC (by norm_num) hM
  simpa only [show 1 + (1 / 9 : ℝ) = 10 / 9 by norm_num] using hd

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
