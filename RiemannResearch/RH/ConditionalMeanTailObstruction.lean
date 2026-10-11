import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.RH.ConditionalMeanHeadObstruction

/-!
# Compulsory head mass plus the signed Mellin tail obstruction

Source: user-requested mathematical completion, `CofinalMinimumProof.md`,
Section 4. The exact signed tail is isolated before Cauchy--Schwarz.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

theorem exact_head_tail_dual_obstruction
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (N : ℕ) {g : ℕ → ℝ} (hg : g ∈ conditionalHeadClass N) :
    ‖partialSum (mellinSecond s) N‖ ^ 2 ≤
      dualTail s N * (conditionalMeanSquare g - (N : ℝ) / ((N : ℝ) + 2)) := by
  have hA : ∀ a ∈ (Set.Ici 1 : Set ℕ), 0 < a := by intro a ha; exact ha
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded (Set.Ici 1) hA hg.1
  let F : ℕ → ℂ := fun n => (g n : ℂ)
  have hb (n : ℕ) (hn : 0 < n) : ‖F n‖ ≤ B := by
    simpa only [F, Complex.norm_real, Real.norm_eq_abs] using hB n
  have hsum := bounded_second_pairing_summable s (by linarith) F B hb
  have hsplit := hsum.sum_add_tsum_nat_add N
  have hpref : (∑ k ∈ Finset.range N, mellinSecond s (k + 1) * mean F (k + 1)) =
      partialSum (mellinSecond s) N := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkN := Finset.mem_range.mp hk
    rw [mean_eq_one_of_head F (k + 1) (Nat.succ_pos _) ?_, mul_one]
    intro n hn hnk
    simp only [F, hg.2 n hn (hnk.trans (by omega)), Complex.ofReal_one]
  rw [hpref, legal_second_pairing_zero (Set.Ici 1) hA s hs hs1 hz hg.1] at hsplit
  have he : (∑' k : ℕ, mellinSecond s (k + N + 1) * mean F (k + N + 1)) =
      -partialSum (mellinSecond s) N := by linear_combination hsplit
  have henergy := bounded_mean_energy_summable F B hb
  have htail : Summable (fun k : ℕ => conditionalWeight (k + N) *
      ‖mean F (k + N + 1)‖ ^ 2) :=
    henergy.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hbound := Analysis.WeightedPairing.pairing_norm_sq_le
    (fun k => conditionalWeight (k + N)) (fun k => conditionalWeight_pos _)
    (fun k => mellinSecond s (k + N + 1)) (fun k => mean F (k + N + 1))
    (dualTail_summable s hs N) htail
  rw [he, norm_neg] at hbound
  have hEsplit := conditionalMeanSquare_exact_head_split N hg
  have ht : (∑' k : ℕ, conditionalWeight (k + N) * ‖mean F (k + N + 1)‖ ^ 2) =
      conditionalMeanSquare g - (N : ℝ) / ((N : ℝ) + 2) := by
    simp only [F, mean_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    linarith
  rw [ht] at hbound
  exact hbound

/-- The genuine infimum has the sharp additive head-plus-tail obstruction. -/
theorem conditionalHeadMinimum_ge_head_add_dual
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (N : ℕ) (ht : 0 < dualTail s N) :
    (N : ℝ) / ((N : ℝ) + 2) + ‖partialSum (mellinSecond s) N‖ ^ 2 / dualTail s N ≤
      conditionalHeadMinimum N := by
  apply le_csInf (conditionalHeadEnergies_nonempty N)
  rintro x ⟨g, hg, rfl⟩
  have h := exact_head_tail_dual_obstruction s hs hs1 hz N hg
  have hdiv : ‖partialSum (mellinSecond s) N‖ ^ 2 / dualTail s N ≤
      conditionalMeanSquare g - (N : ℝ) / ((N : ℝ) + 2) := by
    apply (div_le_iff₀ ht).mpr
    simpa only [mul_comm] using h
  linarith

/-- Positivity of the dual tail is eventually forced by normalization and
unconditional finite interpolation; it is not an extra arithmetic premise. -/
theorem dualTail_pos_eventually_of_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop, 0 < dualTail s N := by
  filter_upwards [mellinSecond_prefix_eventually s hs] with N hN
  obtain ⟨g, hg⟩ := conditionalHeadClass_nonempty N
  have h := exact_head_tail_dual_obstruction s hs hs1 hz N hg
  by_contra hnot
  have hzT : dualTail s N = 0 := le_antisymm (le_of_not_gt hnot) (dualTail_nonneg s N)
  rw [hzT, zero_mul] at h
  linarith

end RiemannResearch.RH.Pareto
