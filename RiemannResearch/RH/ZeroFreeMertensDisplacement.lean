/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualQuasiRiemannSupport
import RiemannResearch.RH.MertensCriticalAverageDisplacement
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zero-free half-planes and the physical displacement prefix

Gerhold, "Asymptotic estimates for some number theoretic power series",
Acta Arith. 142 (2010), Proposition 3(i) ⇒ (ii) (arXiv:0905.2070,
Proposition 2), gives a Mertens power bound with every positive exponent
loss from a fixed zero-free half-plane.
<https://fam.tuwien.ac.at/~sgerhold/pub_files/papers/mu_ogf.pdf>

The hypothesis below uses positive integer cutoffs in that bound.
The finite initial segment is handled in Lean. The displacement prefix is a
separate estimate for the repository's canonical physical sequence.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open RiemannResearch.Analysis.ActualZeroOrdinate
open RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.Analysis ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QAnnihilatorTailEscape QSquarefreeResidualTail ZetaTwoOptimizerStage

/-- Integer-cutoff version of Gerhold's zero-free to Mertens implication.
Both the eventual height and the constant may depend on the exponent loss. -/
def GerholdMertensInput : Prop :=
  ∀ η : ℝ, 1 / 2 ≤ η → η < 1 → ZetaZeroFreeHalfPlane η →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |M (n : ℝ)| ≤ C * (n : ℝ) ^ (η + ε)

/-- Passing from the paper's asymptotic bound to a bound at every positive
integer preserves the power. -/
theorem GerholdMertensInput.integer_power (hG : GerholdMertensInput)
    {η s : ℝ} (hη : 1 / 2 ≤ η) (hη1 : η < 1) (hz : ZetaZeroFreeHalfPlane η)
    (hs : η < s) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      |M (n : ℝ)| ≤ C * (n : ℝ) ^ s := by
  obtain ⟨A, hA, ha⟩ := hG η hη hη1 hz (s - η) (sub_pos.mpr hs)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ha
  let B := ∑ j ∈ Finset.range N, |M (j : ℝ)|
  refine ⟨max A B, hA.trans (le_max_left _ _),?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ (n : ℝ) ^ s := Real.one_le_rpow hn1 (by linarith)
  by_cases hcut : N ≤ n
  · have h := hN n hcut
    rw [show η + (s - η) = s by ring] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hx))
  · have hb : |M (n : ℝ)| ≤ B :=
      Finset.single_le_sum (f := fun j : ℕ => |M (j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hcut))
    exact hb.trans ((le_max_right A B).trans
      (le_mul_of_one_le_right (hA.trans (le_max_left A B)) hx))

/-- An interior exponent satisfying both strict inequalities exists precisely
where the limiting displacement exponent leaves room for Gerhold's loss. -/
theorem exists_mertens_exponent_for_prefix {η γ : ℝ} (hη : η < 1)
    (hγ : γ < (1 - η) / (2 - η)) :
    ∃ s : ℝ, η < s ∧ s < 1 ∧ γ < (1 - s) / (2 - s) := by
  have hc : ContinuousAt (fun s : ℝ => (1 - s) / (2 - s)) η :=
    (continuousAt_const.sub continuousAt_id).div (continuousAt_const.sub continuousAt_id)
      (by dsimp; linarith)
  have hg : ∀ᶠ s : ℝ in 𝓝[>] η, γ < (1 - s) / (2 - s) :=
    (hc.tendsto.mono_left nhdsWithin_le_nhds).eventually (Ioi_mem_nhds hγ)
  have hlo : ∀ᶠ s : ℝ in 𝓝[>] η, η < s := self_mem_nhdsWithin
  have hhi : ∀ᶠ s : ℝ in 𝓝[>] η, s < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hη)
  exact (hlo.and (hhi.and hg)).exists

/-- The limiting exponent is the exact supremum over all admissible
Mertens powers strictly to the right of the zero-free boundary. -/
theorem exists_mertens_exponent_for_prefix_iff {η γ : ℝ} (hη : η < 1) :
    (∃ s : ℝ, η < s ∧ s < 1 ∧ γ < (1 - s) / (2 - s)) ↔ γ < (1 - η) / (2 - η) := by
  constructor
  · rintro ⟨s, hs, hs1, hγ⟩
    apply hγ.trans
    apply (div_lt_div_iff₀ (by linarith : 0 < 2 - s) (by linarith : 0 < 2 - η)).mpr
    nlinarith
  · exact exists_mertens_exponent_for_prefix hη

/-- Any big-O displacement prefix with an exponent strictly below the limiting
threshold implies RH under Gerhold's implication and the actual zero-free region. -/
theorem riemannHypothesis_of_zeroFree_and_subcritical_prefix
    (hG : GerholdMertensInput) {η γ D : ℝ} (hη : 1 / 2 ≤ η) (hη1 : η < 1)
    (hz : ZetaZeroFreeHalfPlane η) (hγ : γ < (1 - η) / (2 - η))
    (hd : ∀ᶠ k : ℕ in atTop, ∑ n ∈ Finset.range k, |qSequence displacement (n + 1)| ≤
      D * (k : ℝ) ^ (1 + γ)) : RiemannHypothesis := by
  obtain ⟨s, hs, hs1, hgs⟩ := exists_mertens_exponent_for_prefix hη1 hγ
  obtain ⟨C, hC, hM⟩ := hG.integer_power hη hη1 hz hs
  exact riemannHypothesis_of_mertens_power_and_subcritical_prefix
    s γ C D (by linarith) hs1 hC hgs hM hd


/-- The zeta specialization of the external Bebel PR 143 Dirichlet certificate
and Liu's Hecke theorem uses the same degree-nine algebraic boundary B*.
<https://github.com/GTimG/QuasiRiemannTracker/pull/143>
<https://hexagonmath.org/2611.00421v1> -/
theorem riemannHypothesis_of_continuumContact_and_prefix
    (hG : GerholdMertensInput) (hz : ContinuumContactNonvanishing)
    {γ D : ℝ} (hγ : γ < (1 - continuumContact) / (2 - continuumContact))
    (hd : ∀ᶠ k : ℕ in atTop, ∑ n ∈ Finset.range k, |qSequence displacement (n + 1)| ≤
      D * (k : ℝ) ^ (1 + γ)) : RiemannHypothesis := by
  have hlo := continuumContact_mem.1
  have hhi := continuumContact_mem.2
  apply riemannHypothesis_of_zeroFree_and_subcritical_prefix hG _ _ hz hγ hd <;> linarith

/-- The weighted p-moment uses the physical positive sites and the same
quadratic decay as the Q inner product. -/
def PhysicalDisplacementMoment (p : ℝ) : Prop :=
  Summable fun n : ℕ => |qSequence displacement (n + 1)| ^ p / ((n : ℝ) + 1) ^ 2

/-- A finite weighted p-moment gives an unsigned prefix of order k^(1+1/p).
The pointwise estimate uses the cutoff k^(1/p) and needs no pointwise bound
on the physical sequence. -/
theorem prefix_of_quadratically_weighted_moment (d : ℕ → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hsum : Summable fun n : ℕ => |d n| ^ p / ((n : ℝ) + 1) ^ 2) :
    ∀ k : ℕ, 0 < k → ∑ n ∈ Finset.range k, |d n| ≤
      (1 + ∑' n : ℕ, |d n| ^ p / ((n : ℝ) + 1) ^ 2) * (k : ℝ) ^ (1 + 1 / p) := by
  intro k hk
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let R := (k : ℝ) ^ (1 / p)
  have hR : 0 < R := Real.rpow_pos_of_pos hk0 _
  have hRp : R ^ p = (k : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_mul hk0.le, div_mul_cancel₀ _ hp0.ne', Real.rpow_one]
  let f (n : ℕ) := |d n| ^ p / ((n : ℝ) + 1) ^ 2
  have hf (n : ℕ) : 0 ≤ f n := div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have ho (n : ℕ) : |d n| ≤ R + R * (|d n| ^ p / (k : ℝ)) := by
    by_cases h : |d n| ≤ R
    · exact h.trans (le_add_of_nonneg_right (mul_nonneg hR.le
        (div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hk0.le)))
    · have hz : 1 ≤ |d n| / R := (one_le_div hR).mpr (le_of_lt (lt_of_not_ge h))
      have hpow := Real.rpow_le_rpow_of_exponent_le hz hp
      rw [Real.rpow_one, Real.div_rpow (abs_nonneg _) hR.le, hRp] at hpow
      calc
        |d n| = R * (|d n| / R) := by field_simp
        _ ≤ R * (|d n| ^ p / (k : ℝ)) := mul_le_mul_of_nonneg_left hpow hR.le
        _ ≤ _ := le_add_of_nonneg_left hR.le
  have hterm (n : ℕ) (hn : n ∈ Finset.range k) :
      |d n| ≤ R + (R * (k : ℝ)) * f n := by
    have hnk : (n : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ (k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnk 2
    have hpart : |d n| ^ p / (k : ℝ) ≤ (k : ℝ) * f n := by
      calc
        _ = (k : ℝ) * (|d n| ^ p / (k : ℝ) ^ 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _) (by positivity) hsq) hk0.le
    rw [mul_assoc]
    exact (ho n).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpart hR.le))
  calc
    _ ≤ ∑ n ∈ Finset.range k, (R + (R * (k : ℝ)) * f n) := Finset.sum_le_sum hterm
    _ = (k : ℝ) * R + (R * (k : ℝ)) * ∑ n ∈ Finset.range k, f n := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (k : ℝ) * R + (R * (k : ℝ)) * ∑' n, f n :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum _ (fun n _ => hf n)) (mul_nonneg hR.le hk0.le))
    _ = _ := by rw [Real.rpow_add hk0, Real.rpow_one]; dsimp [R, f]; ring

/-- A finite physical moment with reciprocal order below the propagated
threshold suffices for RH. Both the zero-free and the Mertens inputs are
explicit. -/
theorem riemannHypothesis_of_zeroFree_and_displacement_moment
    (hG : GerholdMertensInput) {η p : ℝ} (hη : 1 / 2 ≤ η) (hη1 : η < 1)
    (hz : ZetaZeroFreeHalfPlane η) (hp : 1 ≤ p) (hcrit : 1 / p < (1 - η) / (2 - η))
    (hm : PhysicalDisplacementMoment p) : RiemannHypothesis := by
  apply riemannHypothesis_of_zeroFree_and_subcritical_prefix hG hη hη1 hz hcrit
    (D := 1 + ∑' n : ℕ, |qSequence displacement (n + 1)| ^ p / ((n : ℝ) + 1) ^ 2)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  exact prefix_of_quadratically_weighted_moment
    (fun n => qSequence displacement (n + 1)) hp hm k hk

/-- The certificate B* < 7/8 makes the ninth physical moment sufficient. -/
theorem riemannHypothesis_of_continuumContact_and_ninth_moment
    (hG : GerholdMertensInput) (hz : ContinuumContactNonvanishing)
    (hm : PhysicalDisplacementMoment 9) : RiemannHypothesis := by
  have hlo := continuumContact_mem.1
  have hhi := continuumContact_mem.2
  apply riemannHypothesis_of_zeroFree_and_displacement_moment hG _ _ hz (by norm_num) _ hm
  · linarith
  · linarith
  · apply (lt_div_iff₀ (by linarith : 0 < 2 - continuumContact)).mpr
    linarith

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
