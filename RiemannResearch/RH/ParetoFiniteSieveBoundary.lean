import RiemannResearch.RH.ParetoSignedTails
import RiemannResearch.Analysis.SummableDiscreteAbel
import RiemannResearch.RH.ParetoSequenceCertificates

/-!
# The exact finite signed Pareto sieve boundary

Source: Christian Noack's
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Sections 25 and 27, including the September 19 non-Lean continuation.

The cutoff identity below only needs the actual Pareto square summability.
It does not assume absolute summability of the integrated signed tails.
Every boundary retains the complete signed bounded test, so finite arithmetic
linear combinations keep all of their mixed terms. The general sieve theorem
specializes to coefficients mu(d)/(n*d) and moduli n*d. Nothing here asserts
that the boundary is uniformly small when the moduli grow with the cutoff.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

/-- The entire signed boundary after the physical cutoff `K`. -/
def paretoFiniteBoundary (h g : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑' j, signedCoefficient h (j + (K + 1)) *
    (g K - g (j + (K + 1)))

theorem paretoFiniteBoundary_summable {h g : ℕ → ℝ} {C : ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    Summable (fun j => signedCoefficient h (j + (K + 1)) *
      (g K - g (j + (K + 1)))) := by
  apply summable_bounded_product
    ((summable_nat_add_iff (K + 1)).mpr (signedCoefficient_summable hs))
  intro j
  exact (abs_sub (g K) (g (j + (K + 1)))).trans
    (add_le_add (hg K) (hg (j + (K + 1))))

/-- Finite summation by parts with the exact infinite Pareto boundary. -/
theorem pareto_finite_abel_boundary {h g : ℕ → ℝ} {C : ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (hg : ∀ k, |g k| ≤ C) (hgzero : g 0 = 0) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1),
      anchoredSignedTail h k * (g k - g (k - 1))) =
      paretoInner h g + paretoFiniteBoundary h g K := by
  have hb := signedCoefficient_summable hs
  have hp : Summable (fun k => signedCoefficient h k * g k) :=
    summable_bounded_product hb hg
  have hbt : Summable (fun j => signedCoefficient h (j + (K + 1))) :=
    (summable_nat_add_iff (K + 1)).mpr hb
  have hpt : Summable (fun j => signedCoefficient h (j + (K + 1)) *
      g (j + (K + 1))) :=
    (summable_nat_add_iff (K + 1)).mpr hp
  have hboundary : paretoFiniteBoundary h g K =
      signedTail h (K + 1) * g K -
        ∑' j, signedCoefficient h (j + (K + 1)) * g (j + (K + 1)) := by
    unfold paretoFiniteBoundary
    simp_rw [mul_sub]
    rw [(hbt.mul_right (g K)).tsum_sub hpt, tsum_mul_right]
    rfl
  have hinner : (∑' k, signedCoefficient h k * g k) = paretoInner h g := by
    unfold paretoInner
    apply tsum_congr
    intro k
    unfold signedCoefficient
    ring
  have hsplit := hp.sum_add_tsum_nat_add (K + 1)
  rw [hinner] at hsplit
  have habel := ordered_abel_finite (anchoredSignedTail h) g
    (anchoredSignedTail_zero h) (K + 1)
  have hfinite :
      (∑ k ∈ Finset.range (K + 1),
        (anchoredSignedTail h k - anchoredSignedTail h (k + 1)) * g k) =
        ∑ k ∈ Finset.range (K + 1), signedCoefficient h k * g k := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp [hgzero]
    · rw [anchoredSignedTail_difference hs (Nat.pos_of_ne_zero hk0)]
  rw [hfinite, anchoredSignedTail_pos h (by omega)] at habel
  simp only [Nat.add_sub_cancel] at habel
  linarith

/-- The finite residue equation with its full signed tail. The divisibility
sum is finite; its separate convergence is not assumed. -/
theorem pareto_finite_residue_boundary {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (d K : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.range (K + 1), anchoredSignedTail h k) -
      (d : ℝ) * (∑ k ∈ Finset.range (K + 1),
        if d ∣ k then anchoredSignedTail h k else 0) =
      paretoInner h (residue d) + paretoFiniteBoundary h (residue d) K := by
  have ha := pareto_finite_abel_boundary hs
    (fun k => residue_abs_le d k hd) (by simp [residue]) K
  have hj (k : ℕ) : anchoredSignedTail h k *
      (residue d k - residue d (k - 1)) =
      anchoredSignedTail h k -
        (d : ℝ) * (if d ∣ k then anchoredSignedTail h k else 0) := by
    by_cases hk : k = 0
    · subst k
      simp [anchoredSignedTail_zero]
    · rw [residue_difference d k (Nat.pos_of_ne_zero hk)]
      split_ifs <;> ring
  simpa only [hj, Finset.sum_sub_distrib, ← Finset.mul_sum] using ha

/-- An arbitrary finite signed residue test, including the normalized
Möbius sieve after taking `c d = mu(d)/(n*d)` and `q d = n*d`. -/
def finiteSignedResidueTest (s : Finset ℕ) (q : ℕ → ℕ) (c : ℕ → ℝ)
    (k : ℕ) : ℝ := ∑ d ∈ s, c d * residue (q d) k

theorem finiteSignedResidueTest_abs_le (s : Finset ℕ) (q : ℕ → ℕ)
    (c : ℕ → ℝ) (hq : ∀ d ∈ s, 0 < q d) (k : ℕ) :
    |finiteSignedResidueTest s q c k| ≤ ∑ d ∈ s, |c d| * (q d : ℝ) := by
  unfold finiteSignedResidueTest
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro d hd
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (residue_abs_le (q d) k (hq d hd)) (abs_nonneg _)

theorem finiteSignedResidueTest_difference (s : Finset ℕ) (q : ℕ → ℕ)
    (c : ℕ → ℝ) (k : ℕ) (hk : 0 < k) :
    finiteSignedResidueTest s q c k - finiteSignedResidueTest s q c (k - 1) =
      (∑ d ∈ s, c d) -
        ∑ d ∈ s, if q d ∣ k then c d * (q d : ℝ) else 0 := by
  unfold finiteSignedResidueTest
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_sub, residue_difference (q d) k hk]
  split_ifs <;> ring

/-- The exact finite sieve boundary, expressed in weighted divisibility
channels. Its coefficients and boundary are the same signed test. -/
theorem pareto_finite_signed_sieve_boundary {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (s : Finset ℕ) (q : ℕ → ℕ) (c : ℕ → ℝ)
    (hq : ∀ d ∈ s, 0 < q d) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), anchoredSignedTail h k *
      (∑ d ∈ s, if q d ∣ k then c d * (q d : ℝ) else 0)) =
      (∑ d ∈ s, c d) * (∑ k ∈ Finset.range (K + 1), anchoredSignedTail h k) -
        paretoInner h (finiteSignedResidueTest s q c) -
        paretoFiniteBoundary h (finiteSignedResidueTest s q c) K := by
  have hz : finiteSignedResidueTest s q c 0 = 0 := by
    simp [finiteSignedResidueTest, residue]
  have ha := pareto_finite_abel_boundary hs
    (finiteSignedResidueTest_abs_le s q c hq) hz K
  have hj (k : ℕ) : anchoredSignedTail h k *
      (finiteSignedResidueTest s q c k - finiteSignedResidueTest s q c (k - 1)) =
      (∑ d ∈ s, c d) * anchoredSignedTail h k -
        anchoredSignedTail h k *
          (∑ d ∈ s, if q d ∣ k then c d * (q d : ℝ) else 0) := by
    by_cases hk : k = 0
    · subst k
      simp [anchoredSignedTail_zero]
    · rw [finiteSignedResidueTest_difference s q c k (Nat.pos_of_ne_zero hk)]
      ring
  simp only [hj, Finset.sum_sub_distrib, ← Finset.mul_sum] at ha
  linarith

/-- The finite signed sieve is a member of the actual full legal span. -/
theorem finiteSignedResidueTest_mem_legal (s : Finset ℕ) (q : ℕ → ℕ)
    (c : ℕ → ℝ) (hq : ∀ d ∈ s, 0 < q d) :
    finiteSignedResidueTest s q c ∈ legalSeedSpan {n : ℕ | 0 < n} := by
  have hr (d : ℕ) (hd : d ∈ s) :
      residue (q d) ∈ legalSeedSpan {n : ℕ | 0 < n} := by
    simpa only [dilation_one] using
      (dilation_generator_mem {n : ℕ | 0 < n}
        (a := q d) (m := 1) (hq d hd) (by omega))
  have hsum : (∑ d ∈ s, c d • residue (q d)) ∈
      legalSeedSpan {n : ℕ | 0 < n} :=
    Submodule.sum_mem _ (fun d hd => Submodule.smul_mem _ _ (hr d hd))
  convert hsum using 1
  funext k
  simp [finiteSignedResidueTest]

/-- For an actual legal annihilator the inner-product term vanishes, leaving
exactly the manuscript's finite signed boundary. -/
theorem LegalAnnihilator.finite_signed_sieve_boundary {h : ℕ → ℝ}
    (hh : LegalAnnihilator {n : ℕ | 0 < n} h)
    (s : Finset ℕ) (q : ℕ → ℕ) (c : ℕ → ℝ)
    (hq : ∀ d ∈ s, 0 < q d) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), anchoredSignedTail h k *
      (∑ d ∈ s, if q d ∣ k then c d * (q d : ℝ) else 0)) =
      (∑ d ∈ s, c d) * (∑ k ∈ Finset.range (K + 1), anchoredSignedTail h k) -
        paretoFiniteBoundary h (finiteSignedResidueTest s q c) K := by
  rw [pareto_finite_signed_sieve_boundary hh.1 s q c hq K,
    hh.2 _ (finiteSignedResidueTest_mem_legal s q c hq), sub_zero]

/-- A fixed bounded test has vanishing boundary. This assertion has fixed
`g` and `C`; it supplies no uniform estimate for growing arithmetic sieves. -/
theorem paretoFiniteBoundary_tendsto_zero {h g : ℕ → ℝ} {C : ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (hg : ∀ k, |g k| ≤ C) (hgzero : g 0 = 0) :
    Filter.Tendsto (paretoFiniteBoundary h g) Filter.atTop (nhds 0) := by
  have he (k : ℕ) :
      (anchoredSignedTail h k - anchoredSignedTail h (k + 1)) * g k =
        signedCoefficient h k * g k := by
    by_cases hk : k = 0
    · subst k
      simp [hgzero]
    · rw [anchoredSignedTail_difference hs (Nat.pos_of_ne_zero hk)]
  have hd : Summable (fun k =>
      (anchoredSignedTail h k - anchoredSignedTail h (k + 1)) * g k) := by
    simpa only [he] using
      summable_bounded_product (signedCoefficient_summable hs) hg
  have hinner : (∑' k,
      (anchoredSignedTail h k - anchoredSignedTail h (k + 1)) * g k) =
        paretoInner h g := by
    simp_rw [he]
    unfold paretoInner
    apply tsum_congr
    intro k
    unfold signedCoefficient
    ring
  have ht := ordered_abel_tendsto (anchoredSignedTail_zero h)
    (anchoredSignedTail_tendsto_zero hs) hd hg
  rw [hinner] at ht
  have hsucc : Filter.Tendsto (fun K : ℕ => K + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun K hK => by omega⟩
  have ht' := (ht.comp hsucc).sub
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => paretoInner h g)
      Filter.atTop (nhds (paretoInner h g)))
  simpa only [Function.comp_apply, pareto_finite_abel_boundary hs hg hgzero,
    add_sub_cancel_left, sub_self] using ht'

end
end RiemannResearch.RH.Pareto
