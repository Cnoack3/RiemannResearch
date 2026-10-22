import RiemannResearch.RH.ParetoSieveBoundaryNorm
import RiemannResearch.RH.ParetoMobiusSieveBoundary

/-!
# Unbounded signed sieve boundary norms

Source: user-provided continuation, Section 27, equation (27.7).
For every integer Y ≥ 8 the full signed boundary norm is at least cY²Y/128.
The elementary prime-product rate then proves divergence. No cancellation
estimate for an actual certificate is assumed or supplied.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem sieveResidue_bounded (P n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, ∀ k, |sieveResidue P n k| ≤ C := by
  refine ⟨∑ d ∈ P.divisors,
    |(ArithmeticFunction.moebius d : ℝ) / ((n * d : ℕ) : ℝ)| *
      ((n * d : ℕ) : ℝ), ?_⟩
  intro k
  rw [sieveResidue_eq_finiteSignedResidueTest]
  exact finiteSignedResidueTest_abs_le P.divisors (fun d => n * d)
    (fun d => (ArithmeticFunction.moebius d : ℝ) / ((n * d : ℕ) : ℝ))
    (fun d hd => Nat.mul_pos hn (Nat.pos_of_mem_divisors hd)) k

theorem paretoBoundaryNormSq_summable {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    Summable (fun j => positiveWeight (j + (K + 1)) *
      (g K - g (j + (K + 1))) ^ 2) := by
  have hs := (summable_nat_add_iff (K + 1)).mpr
    (paretoBoundaryKernel_square_summable hg K)
  apply hs.congr
  intro j
  simp [paretoBoundaryKernel, show K < j + (K + 1) by omega]

/-- The manuscript's lower bound for every cutoff, with its stated constant. -/
theorem factorialSieve_boundaryNormSq_lower (Y : ℕ) (hY : 8 ≤ Y) :
    (sieveReciprocal Y.factorial) ^ 2 * (Y : ℝ) / 128 ≤
      paretoBoundaryNormSq (sieveResidue Y.factorial 1) (Y / 2) := by
  let c : ℝ := sieveReciprocal Y.factorial
  let K : ℕ := Y / 2
  let L : ℕ := (3 * Y + 3) / 4
  let s : Finset ℕ := Finset.Ico (L - (K + 1)) (Y - K)
  have hK : 0 < K := by dsimp [K]; omega
  have hKY : K ≤ Y := by dsimp [K]; omega
  have hLK : K + 1 ≤ L := by dsimp [K, L]; omega
  have hLY : L ≤ Y := by dsimp [L]; omega
  have hcard : s.card = Y - L + 1 := by
    dsimp [s]
    rw [Nat.card_Ico]
    omega
  have hcardN : Y ≤ 4 * s.card := by
    rw [hcard]
    dsimp [L]
    omega
  obtain ⟨C, hg⟩ := sieveResidue_bounded Y.factorial 1 (by decide)
  have hs := paretoBoundaryNormSq_summable hg K
  have hhead (t : ℕ) (ht : 0 < t) (htY : t ≤ Y) :
      sieveResidue Y.factorial 1 t = c * (t : ℝ) - 1 := by
    rw [sieveResidue_exact _ _ _ (Nat.factorial_pos Y) (by decide)]
    simp only [Nat.div_one, Nat.cast_one, div_one]
    rw [sieveRoughCount_factorial_head Y t ht htY]
  have hterm (j : ℕ) (hj : j ∈ s) :
      c ^ 2 / 32 ≤ positiveWeight (j + (K + 1)) *
        (sieveResidue Y.factorial 1 K - sieveResidue Y.factorial 1 (j + (K + 1))) ^ 2 := by
    have hj' := Finset.mem_Ico.mp hj
    let k : ℕ := j + (K + 1)
    have hklo : L ≤ k := by dsimp [k]; omega
    have hkhi : k ≤ Y := by dsimp [k]; omega
    have hk : 0 < k := by omega
    have hgapN : Y + 4 * K ≤ 4 * k := by
      dsimp [K, L] at *
      omega
    have hgapR : (Y : ℝ) ≤ 4 * ((k : ℝ) - (K : ℝ)) := by
      have hx : (Y : ℝ) + 4 * (K : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hgapN
      linarith
    have hdiff : sieveResidue Y.factorial 1 K - sieveResidue Y.factorial 1 k =
        c * ((K : ℝ) - (k : ℝ)) := by
      rw [hhead K hK hKY, hhead k hk hkhi]
      ring
    change c ^ 2 / 32 ≤ positiveWeight k *
      (sieveResidue Y.factorial 1 K - sieveResidue Y.factorial 1 k) ^ 2
    rw [hdiff]
    have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hkYR : (k : ℝ) ≤ Y := by exact_mod_cast hkhi
    have hden : (k : ℝ) * ((k : ℝ) + 1) ≤ 2 * (Y : ℝ) ^ 2 := by
      have hproduct := mul_nonneg (sub_nonneg.mpr hkYR)
        (show 0 ≤ (Y : ℝ) + (k : ℝ) by positivity)
      nlinarith
    have hdist : (Y : ℝ) ^ 2 ≤ 16 * ((K : ℝ) - (k : ℝ)) ^ 2 := by
      have hproduct := mul_nonneg (sub_nonneg.mpr hgapR)
        (show 0 ≤ 4 * ((k : ℝ) - (K : ℝ)) + (Y : ℝ) by linarith)
      nlinarith
    have hweight : positiveWeight k * (c * ((K : ℝ) - (k : ℝ))) ^ 2 =
        (c * ((K : ℝ) - (k : ℝ))) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
      unfold positiveWeight
      ring
    rw [hweight]
    apply (le_div_iff₀ (mul_pos hkR (by positivity))).mpr
    have hmul1 := mul_le_mul_of_nonneg_left hden (sq_nonneg c)
    have hmul2 := mul_le_mul_of_nonneg_left hdist (sq_nonneg c)
    nlinarith
  have hlower : (s.card : ℝ) * (c ^ 2 / 32) ≤
      ∑ j ∈ s, positiveWeight (j + (K + 1)) *
        (sieveResidue Y.factorial 1 K - sieveResidue Y.factorial 1 (j + (K + 1))) ^ 2 := by
    calc
      _ = ∑ j ∈ s, c ^ 2 / 32 := by simp
      _ ≤ _ := Finset.sum_le_sum hterm
  have hupper := hs.sum_le_tsum s (fun j hj =>
    mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
  have htotal := hlower.trans hupper
  change (s.card : ℝ) * (c ^ 2 / 32) ≤
    paretoBoundaryNormSq (sieveResidue Y.factorial 1) K at htotal
  have hcardR : (Y : ℝ) ≤ 4 * (s.card : ℝ) := by exact_mod_cast hcardN
  have hmul := mul_le_mul_of_nonneg_left hcardR (sq_nonneg c)
  change c ^ 2 * (Y : ℝ) / 128 ≤ paretoBoundaryNormSq (sieveResidue Y.factorial 1) K
  nlinarith

/-- Equation (27.7), with all integer cutoffs rather than a subsequence. -/
theorem factorialSieve_boundaryNormSq_tendsto_atTop :
    Tendsto (fun Y : ℕ =>
      paretoBoundaryNormSq (sieveResidue Y.factorial 1) (Y / 2)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [tendsto_atTop.1 factorialSieveReciprocal_square_mul_tendsto_atTop
    (128 * B), eventually_ge_atTop 8] with Y hrate hY
  have hlower := factorialSieve_boundaryNormSq_lower Y hY
  linarith

end
end RiemannResearch.RH.Pareto
