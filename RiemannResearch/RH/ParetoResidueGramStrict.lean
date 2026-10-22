import RiemannResearch.RH.ParetoFiniteGram

/-!
# Independence and strict positivity for the complete residue Gram form

Source: `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`, Section 7.
Möbius difference gives the actual coefficient-recovery functional. This proves
strict positivity of the genuine infinite-tail Gram form, rather than imposing
positive definiteness as an assumption on an unspecified matrix.

-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Möbius difference isolates every nontrivial residue coefficient. -/
theorem residue_finset_coefficient (s : Finset ℕ) (c : ℕ → ℝ)
    (n : ℕ) (hn : 1 < n) (hns : n ∈ s) :
    mobiusDifference n (fun k => ∑ d ∈ s, c d * residue d k) = -(n : ℝ) * c n := by
  rw [mobiusDifference_sum]
  simp_rw [mobiusDifference_residue n _ hn]
  rw [Finset.sum_eq_single n]
  · simp
    ring
  · intro d hd hdn
    simp [Ne.symm hdn]
  · exact fun h => (h hns).elim

/-- No nonzero finite real combination of residues of conductors above 1 vanishes. -/
theorem residue_finset_independent (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 < n)
    (hz : ∀ k, (∑ d ∈ s, c d * residue d k) = 0) :
    ∀ n ∈ s, c n = 0 := by
  intro n hn
  have hcoef := residue_finset_coefficient s c n (hs n hn) hn
  have hzero : mobiusDifference n (fun k => ∑ d ∈ s, c d * residue d k) = 0 := by
    simp [mobiusDifference, hz]
  rw [hzero] at hcoef
  have hnpos : 0 < n := lt_trans Nat.zero_lt_one (hs n hn)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
  exact (mul_eq_zero.mp hcoef.symm).resolve_left (neg_ne_zero.mpr hn0)

theorem residue_finset_eq_zero_iff (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 < n) :
    (∀ k, (∑ d ∈ s, c d * residue d k) = 0) ↔ ∀ n ∈ s, c n = 0 := by
  constructor
  · exact residue_finset_independent s c hs
  · intro hc k
    exact Finset.sum_eq_zero (fun n hn => by rw [hc n hn, zero_mul])

/-- The complete Pareto self-inner-product detects all positive coordinates. -/
theorem paretoInner_self_zero_iff_positive {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) :
    paretoInner f f = 0 ↔ ∀ k, 0 < k → f k = 0 := by
  have hsum := weighted_summable_of_bounded (bounded_product hf hf)
  constructor
  · intro hz k hk
    have hle := hsum.sum_le_tsum ({k} : Finset ℕ)
      (fun j _ => mul_nonneg (positiveWeight_nonneg j) (mul_self_nonneg (f j)))
    simp only [Finset.sum_singleton] at hle
    change positiveWeight k * (f k * f k) ≤ paretoInner f f at hle
    rw [hz] at hle
    have hw : 0 < positiveWeight k := by
      unfold positiveWeight
      have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
      positivity
    have hsqle : f k * f k ≤ 0 :=
      le_of_mul_le_mul_left (show positiveWeight k * (f k * f k) ≤
        positiveWeight k * 0 by simpa using hle) hw
    have hsq : f k * f k = 0 := le_antisymm hsqle (mul_self_nonneg (f k))
    exact mul_self_eq_zero.mp hsq
  · intro hz
    unfold paretoInner
    calc
      (∑' k, positiveWeight k * (f k * f k)) = ∑' _k : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro k
        by_cases hk : k = 0
        · subst k
          simp [positiveWeight]
        · rw [hz k (Nat.pos_of_ne_zero hk)]
          ring
      _ = 0 := by simp

/-- An explicit complete Gram quadratic form indexed by distinct conductors
`n+2`; the index offset discharges all positivity and trivial-residue issues. -/
def residueGramQuadratic (s : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, c i * c j * paretoInner (residue (i + 2)) (residue (j + 2))

theorem residueGramQuadratic_eq_inner (s : Finset ℕ) (c : ℕ → ℝ) :
    residueGramQuadratic s c =
      paretoInner (fun k => ∑ i ∈ s, c i * residue (i + 2) k)
        (fun k => ∑ i ∈ s, c i * residue (i + 2) k) := by
  symm
  exact paretoInner_finsetCombination s c (fun i k => residue_abs_le (i + 2) k (by omega))

/-- Strict positivity for every nonzero coefficient vector; every mixed
covariance and the entire infinite Pareto tail are retained. -/
theorem residueGramQuadratic_pos (s : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∃ i ∈ s, c i ≠ 0) : 0 < residueGramQuadratic s c := by
  rw [residueGramQuadratic_eq_inner]
  let f : ℕ → ℝ := fun k => ∑ i ∈ s, c i * residue (i + 2) k
  have hb := bounded_finsetCombination s c
    (fun i k => residue_abs_le (i + 2) k (by omega))
  have hnonneg := paretoInner_self_nonneg f
  by_contra hpos
  have hzero : paretoInner f f = 0 := by
    change ¬ 0 < paretoInner f f at hpos
    exact le_antisymm (le_of_not_gt hpos) hnonneg
  have hvalues := (paretoInner_self_zero_iff_positive hb).mp hzero
  obtain ⟨i, hi, hci⟩ := hc
  have hcoef : mobiusDifference (i + 2) f = -((i + 2 : ℕ) : ℝ) * c i := by
    change mobiusDifference (i + 2) (fun k => ∑ j ∈ s, c j * residue (j + 2) k) = _
    rw [mobiusDifference_sum]
    simp_rw [mobiusDifference_residue (i + 2) _ (by omega)]
    rw [Finset.sum_eq_single i]
    · simp
      ring
    · intro j hj hji
      simp [Ne.symm hji]
    · exact fun h => (h hi).elim
  have hf0 : f 0 = 0 := by simp [f, residue]
  have hall : ∀ k, f k = 0 := by
    intro k
    by_cases hk : k = 0
    · simpa [hk] using hf0
    · exact hvalues k (Nat.pos_of_ne_zero hk)
  have hdefzero : mobiusDifference (i + 2) f = 0 := by simp [mobiusDifference, hall]
  rw [hdefzero] at hcoef
  have hcast : ((i + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  exact hci ((mul_eq_zero.mp hcoef.symm).resolve_left (neg_ne_zero.mpr hcast))

/-- The four-term gauge identity for the actual unnormalized seeds. -/
theorem twoSeed_square_gauge (n k : ℕ) :
    dilation n (residue 2) k - dilation (3 * n) (residue 2) k -
      dilation n (residue 3) k + dilation (2 * n) (residue 3) k = 0 := by
  simp only [residue_mul_floor]
  have h6 : 3 * n * 2 = 2 * n * 3 := by ring
  rw [h6, Nat.mul_comm n 2, Nat.mul_comm n 3]
  ring

end
end RiemannResearch.RH.Pareto
