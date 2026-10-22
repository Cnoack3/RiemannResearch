import RiemannResearch.RH.NaturalMobiusResidualCriterion
import RiemannResearch.RH.ThresholdHilbertL1
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# One-sided harmonic masses of the physical projection residual

Source: direct finite-subsum argument developed in
`RH/DilationTailAndChargeObstructions20260924.md`, Section 2.
No mathematical novelty is claimed.

For an annihilator of every residue generator, summability of either
physical signed first moment forces summability of the absolute first
moment. For the actual projection residual, the existing unconditional
raw-Mobius test limit then forces residual vanishing.

The contrapositive is an unconditional restriction on failure of RH:
both nonnegative physical signed-mass series are nonsummable.
Summability of either actual series is OPEN; it is not supplied as an axiom.
These are physical coordinates, distinct from Möbius-charge sign masses.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- A finite negative first moment forces a finite full first moment for an
annihilator of all residue generators. -/
theorem summable_physical_moment_of_negative_part
    (f : ThresholdHilbert)
    (ho : ∀ (d : ℕ) (hd : 1 < d),
      inner ℝ (normalizedResidueHilbert d (by omega)) f = 0)
    (hn : Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      max (-hilbertSequence f k) 0)) :
    Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      |hilbertSequence f k|) := by
  let p : ℕ → ℝ := fun k : ℕ => positiveWeight k * max (hilbertSequence f k) 0
  let n : ℕ → ℝ := fun k : ℕ => positiveWeight k * max (-hilbertSequence f k) 0
  have hp0 (k : ℕ) : 0 ≤ p k := mul_nonneg (positiveWeight_nonneg k) (le_max_right _ _)
  have hn0 (k : ℕ) : 0 ≤ n k := mul_nonneg (positiveWeight_nonneg k) (le_max_right _ _)
  have hl1 := hilbertL1Norm_summable f
  have hp : Summable p := by
    apply Summable.of_nonneg_of_le hp0 _ hl1
    intro k
    dsimp [p]
    exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
      (positiveWeight_nonneg k)
  have hns : Summable n := by
    apply Summable.of_nonneg_of_le hn0 _ hl1
    intro k
    dsimp [n]
    exact mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _))
      (positiveWeight_nonneg k)
  have hnm : Summable (fun k : ℕ => (k : ℝ) * n k) := by
    simpa only [n, mul_assoc, mul_left_comm, mul_comm] using hn
  have hpairs (d : ℕ) (hd : 1 < d) :
      (∑' k : ℕ, residueFraction d k * p k) =
        ∑' k : ℕ, residueFraction d k * n k := by
    have hg0 (k : ℕ) : 0 ≤ residueFraction d k := by
      unfold residueFraction; positivity
    have hg1 (k : ℕ) : residueFraction d k ≤ 1 :=
      (le_abs_self _).trans (residueFraction_abs_le_one d k (by omega))
    have hps : Summable (fun k : ℕ => residueFraction d k * p k) := by
      apply Summable.of_nonneg_of_le (fun k : ℕ => mul_nonneg (hg0 k) (hp0 k)) _ hp
      intro k
      exact (mul_le_mul_of_nonneg_right (hg1 k) (hp0 k)).trans_eq (one_mul _)
    have hnn : Summable (fun k : ℕ => residueFraction d k * n k) := by
      apply Summable.of_nonneg_of_le (fun k : ℕ => mul_nonneg (hg0 k) (hn0 k)) _ hns
      intro k
      exact (mul_le_mul_of_nonneg_right (hg1 k) (hn0 k)).trans_eq (one_mul _)
    have he (k : ℕ) : residueFraction d k * p k - residueFraction d k * n k =
        positiveWeight k * (residueFraction d k * hilbertSequence f k) := by
      dsimp [p, n]
      by_cases hk : 0 ≤ hilbertSequence f k
      · rw [max_eq_left hk, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (le_of_not_ge hk), max_eq_left (by linarith)]
        ring
    have hz := ho d hd
    rw [hilbert_inner_weighted, normalizedResidueHilbert_sequence] at hz
    change (∑' k : ℕ, positiveWeight k *
      (residueFraction d k * hilbertSequence f k)) = 0 at hz
    have ht := hps.tsum_sub hnn
    simp_rw [he] at ht
    linarith
  have hpm : Summable (fun k : ℕ => (k : ℝ) * p k) := by
    apply summable_of_sum_range_le (fun k : ℕ => mul_nonneg (Nat.cast_nonneg k) (hp0 k))
      (c := ∑' k : ℕ, (k : ℝ) * n k)
    intro K
    let d := K + 2
    have hd : 1 < d := by dsimp [d]; omega
    have hd0 : (0 : ℝ) < d := by positivity
    have hg0 (k : ℕ) : 0 ≤ (d : ℝ) * residueFraction d k := by
      unfold residueFraction; positivity
    have hgk (k : ℕ) : (d : ℝ) * residueFraction d k ≤ k := by
      calc
        _ = ((k % d : ℕ) : ℝ) := by
          unfold residueFraction
          field_simp [ne_of_gt hd0]
        _ ≤ (k : ℝ) := by exact_mod_cast Nat.mod_le k d
    have hnres : Summable (fun k : ℕ => (d : ℝ) * residueFraction d k * n k) := by
      apply Summable.of_nonneg_of_le
        (fun k : ℕ => mul_nonneg (hg0 k) (hn0 k)) _ hnm
      intro k
      exact mul_le_mul_of_nonneg_right (hgk k) (hn0 k)
    have hpres : Summable (fun k : ℕ => (d : ℝ) * residueFraction d k * p k) := by
      apply Summable.of_nonneg_of_le
        (fun k : ℕ => mul_nonneg (hg0 k) (hp0 k)) _ (hp.mul_left (d : ℝ))
      intro k
      have hb := (le_abs_self (residueFraction d k)).trans
        (residueFraction_abs_le_one d k (by omega))
      exact mul_le_mul_of_nonneg_right (by nlinarith [hd0]) (hp0 k)
    have he : (∑' k : ℕ, (d : ℝ) * residueFraction d k * p k) =
        ∑' k : ℕ, (d : ℝ) * residueFraction d k * n k := by
      simp_rw [mul_assoc]
      rw [tsum_mul_left, tsum_mul_left, hpairs d hd]
    calc
      (∑ k ∈ Finset.range K, (k : ℝ) * p k) =
          ∑ k ∈ Finset.range K, (d : ℝ) * residueFraction d k * p k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkd : k < d := by have := Finset.mem_range.mp hk; dsimp [d]; omega
        simp only [residueFraction, Nat.mod_eq_of_lt hkd]
        field_simp [ne_of_gt hd0]
      _ ≤ ∑' k : ℕ, (d : ℝ) * residueFraction d k * p k :=
        hpres.sum_le_tsum (Finset.range K) (fun k _ => mul_nonneg (hg0 k) (hp0 k))
      _ = ∑' k : ℕ, (d : ℝ) * residueFraction d k * n k := he
      _ ≤ ∑' k : ℕ, (k : ℝ) * n k :=
        hnres.tsum_le_tsum
          (fun k : ℕ => mul_le_mul_of_nonneg_right (hgk k) (hn0 k)) hnm
  have hs := hpm.add hnm
  apply hs.congr
  intro k
  dsimp [p, n]
  by_cases hk : 0 ≤ hilbertSequence f k
  · rw [max_eq_left hk, max_eq_right (by linarith), abs_of_nonneg hk]
    ring
  · rw [max_eq_right (le_of_not_ge hk), max_eq_left (by linarith),
      abs_of_nonpos (le_of_not_ge hk)]
    ring

theorem summable_physical_moment_of_positive_part
    (f : ThresholdHilbert)
    (ho : ∀ (d : ℕ) (hd : 1 < d),
      inner ℝ (normalizedResidueHilbert d (by omega)) f = 0)
    (hp : Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      max (hilbertSequence f k) 0)) :
    Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      |hilbertSequence f k|) := by
  have he (k : ℕ) : hilbertSequence (-f) k = -hilbertSequence f k := by
    cases k with
    | zero => simp
    | succ k => simp [hilbertSequence, neg_div]
  have hn : Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      max (-hilbertSequence (-f) k) 0) := by
    simpa only [he, neg_neg] using hp
  have h := summable_physical_moment_of_negative_part (-f) (by
    intro d hd
    rw [inner_neg_right, ho d hd, neg_zero]) hn
  simpa only [he, abs_neg] using h

namespace CoefficientStabilization

theorem limitResidual_eq_zero_of_summable_physical_moment
    (hs : Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      |hilbertSequence limitResidual k|)) : limitResidual = 0 := by
  have ht := rawMobiusResidual_inner_tendsto_of_summable_test limitResidual hs
  have hc : Tendsto (fun _ : ℕ => limitEnergy) atTop (𝓝 0) := by
    simpa only [rawMobiusResidual_inner_limitResidual] using ht
  exact limitResidual_zero_iff_energy_zero.mpr
    (tendsto_nhds_unique tendsto_const_nhds hc)

theorem limitResidual_eq_zero_of_summable_negative_physical_moment
    (hs : Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      max (-hilbertSequence limitResidual k) 0)) : limitResidual = 0 := by
  apply limitResidual_eq_zero_of_summable_physical_moment
  apply summable_physical_moment_of_negative_part limitResidual _ hs
  intro d hd
  apply limitResidual_mem_orthogonal
  exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (normalizedResidue_mem_atomSpan d (by omega))


theorem limitResidual_eq_zero_of_summable_positive_physical_moment
    (hs : Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      max (hilbertSequence limitResidual k) 0)) : limitResidual = 0 := by
  apply limitResidual_eq_zero_of_summable_physical_moment
  apply summable_physical_moment_of_positive_part limitResidual _ hs
  intro d hd
  apply limitResidual_mem_orthogonal
  exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (normalizedResidue_mem_atomSpan d (by omega))

theorem not_RH_physical_sign_masses_nonsummable (hRH : ¬ RiemannHypothesis) :
    (¬ Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      max (hilbertSequence limitResidual k) 0)) ∧
    (¬ Summable (fun k : ℕ => positiveWeight k * (k : ℝ) *
      max (-hilbertSequence limitResidual k) 0)) := by
  have hn : limitResidual ≠ 0 := by
    intro hz
    exact hRH (riemannHypothesis_of_firstCoordinate_zero
      (firstCoordinate_zero_iff_residual_zero.mpr hz))
  exact ⟨fun hs => hn (limitResidual_eq_zero_of_summable_positive_physical_moment hs),
    fun hs => hn (limitResidual_eq_zero_of_summable_negative_physical_moment hs)⟩

end CoefficientStabilization
end RiemannResearch.RH.Pareto
