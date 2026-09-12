import RiemannResearch.Analysis.SummableDiscreteAbel
import RiemannResearch.Analysis.SummableMultiples
import RiemannResearch.RH.ParetoSignedTails
import RiemannResearch.RH.DyadicResidueJumps

/-!
# Grouped signed-tail equations without absolute tail summability

Source: user-provided two-seed signed-tail and canonical-correlation research,
September 11–12, 2026 (problem and signed equations). The finite reindexing,
ordered Abel limit, and summability proofs here were developed for this
formalization.

Every weighted L2 sequence has absolutely summable signed coefficients.
Consequently its fixed-width grouped tail differences are summable, even when
the tail itself is not summable. The actual dyadic and triadic pairings equal
the grouped series below. Their positive and negative channels are never
separated as infinite sums.

No RH assumption or tail-summability provider is used. Inverting the
simultaneous grouped equations in the full weighted L2 class remains open.
-/

open scoped BigOperators
open Filter

namespace RiemannResearch.RH.Pareto
theorem paretoInner_eq_limit_ordered_signedTail_jumps {h g : ℕ → ℝ} {C : ℝ}
    (hs : Summable (fun k => positiveWeight k*h k^2))
    (hg : ∀ n, |g n| ≤ C) (hgzero : g 0 = 0) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      anchoredSignedTail h n*(g n-g (n-1)))
      atTop (nhds (paretoInner h g)) := by
  have he : (fun n => (anchoredSignedTail h n-anchoredSignedTail h (n+1))*g n) =
      (fun n => signedCoefficient h n*g n) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [hgzero]
    · rw [anchoredSignedTail_difference hs (Nat.pos_of_ne_zero hn)]
  have hd : Summable (fun n =>
      (anchoredSignedTail h n-anchoredSignedTail h (n+1))*g n) := by
    rw [he]
    exact RiemannResearch.Analysis.summable_bounded_product
      (signedCoefficient_summable hs) hg
  have ht := RiemannResearch.Analysis.ordered_abel_tendsto
    (anchoredSignedTail_zero h) (anchoredSignedTail_tendsto_zero hs) hd hg
  rw [he] at ht
  convert ht using 1
  unfold paretoInner signedCoefficient
  congr 2
  funext n
  ring
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto

theorem paretoInner_eq_limit_signed_divisibility_jumps {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k*h k^2))
    (m a : ℕ) (ha : 0 < a) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, anchoredSignedTail h n *
      ((if m ∣ n then (m : ℝ) else 0) -
        (if m*a ∣ n then ((m*a : ℕ) : ℝ) else 0)))
      atTop (nhds (paretoInner h (dilation m (residue a)))) := by
  have hg : ∀ k, |dilation m (residue a) k| ≤ (m : ℝ)*(a : ℝ) := by
    apply dilation_abs_le
    intro k
    simp only [residue, abs_of_nonneg (Nat.cast_nonneg (k%a) : (0:ℝ) ≤ (k%a:ℕ))]
    exact_mod_cast (Nat.mod_lt k ha).le
  have ht := paretoInner_eq_limit_ordered_signedTail_jumps hs hg
    (by simp [dilation, residue])
  convert ht using 1
  funext N
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hz : n = 0
  · subst n
    simp [anchoredSignedTail_zero]
  · rw [dilation_residue_difference m a n (Nat.pos_of_ne_zero hz)]

theorem LegalAnnihilator.ordered_signed_divisibility_jumps_tendsto_zero
    {S : Set ℕ} {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    {a m : ℕ} (haS : a ∈ S) (ha : 0 < a) (hm : 0 < m) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, anchoredSignedTail h n *
      ((if m ∣ n then (m : ℝ) else 0) -
        (if m*a ∣ n then ((m*a : ℕ) : ℝ) else 0)))
      atTop (nhds 0) := by
  have ht := paretoInner_eq_limit_signed_divisibility_jumps hh.1 m a ha
  rw [hh.2 _ (dilation_generator_mem S haS hm)] at ht
  exact ht
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
theorem binary_grouped_signedTail_summable {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k*h k^2))
    {m : ℕ} (hm : 0 < m) :
    Summable (fun j => anchoredSignedTail h (m*(2*j+1)) -
      anchoredSignedTail h (m*(2*j+2))) := by
  have ht := signedTail_shift_difference_summable hs (q := 2*m) (by omega) m m
  convert ht using 1
  funext j
  rw [anchoredSignedTail_pos h (by positivity),
      anchoredSignedTail_pos h (by positivity)]
  congr 2 <;> ring

theorem triadic_grouped_signedTail_summable {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k*h k^2))
    {m : ℕ} (hm : 0 < m) :
    Summable (fun j => anchoredSignedTail h (m*(3*j+1)) +
      anchoredSignedTail h (m*(3*j+2)) - 2*anchoredSignedTail h (m*(3*j+3))) := by
  have h1 := signedTail_shift_difference_summable hs (q := 3*m) (by omega) m (2*m)
  have h2 := signedTail_shift_difference_summable hs (q := 3*m) (by omega) (2*m) m
  convert h1.add h2 using 1
  funext j
  rw [anchoredSignedTail_pos h (by positivity),
      anchoredSignedTail_pos h (by positivity),
      anchoredSignedTail_pos h (by positivity)]
  have e1 : m*(3*j+1) = 3*m*j+m := by ring
  have e2 : m*(3*j+2) = 3*m*j+2*m := by ring
  have e3 : m*(3*j+3) = 3*m*j+m+2*m := by ring
  have e4 : 3*m*j+2*m+m = 3*m*j+m+2*m := by ring
  rw [e1, e2, e3, e4]
  ring
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
private theorem multiple_cutoff_tendsto {m a : ℕ} (hm : 0 < m) (ha : 0 < a) :
    Tendsto (fun K : ℕ => (m*a)*K+1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with K hK
  have hma : 1 ≤ m*a := Nat.mul_pos hm ha
  nlinarith

theorem dyadic_pairing_eq_grouped_signedTail {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k*h k^2))
    {m : ℕ} (hm : 0 < m) :
    paretoInner h (dilation m (residue 2)) =
      (m : ℝ)*(∑' j, (anchoredSignedTail h (m*(2*j+1)) -
        anchoredSignedTail h (m*(2*j+2)))) := by
  have he : ∀ K, (∑ n ∈ Finset.range ((m*2)*K+1), anchoredSignedTail h n *
      ((if m ∣ n then (m : ℝ) else 0) -
        (if m*2 ∣ n then ((m*2 : ℕ) : ℝ) else 0))) =
      (m : ℝ)*(∑ j ∈ Finset.range K, (anchoredSignedTail h (m*(2*j+1)) -
        anchoredSignedTail h (m*(2*j+2)))) := by
    intro K
    rw [finite_signed_divisibility_sum _ hm (by norm_num)]
    have hb := binary_block_sum (fun j => anchoredSignedTail h (m*j))
      (by simp [anchoredSignedTail_zero]) K
    simpa only [Nat.cast_ofNat] using congrArg (fun x : ℝ => (m : ℝ)*x) hb
  have ht := (paretoInner_eq_limit_signed_divisibility_jumps hs m 2 (by norm_num)).comp
    (multiple_cutoff_tendsto hm (by norm_num : 0 < 2))
  have ht' : Tendsto (fun K => (m : ℝ)*(∑ j ∈ Finset.range K,
      (anchoredSignedTail h (m*(2*j+1)) - anchoredSignedTail h (m*(2*j+2)))))
      atTop (nhds (paretoInner h (dilation m (residue 2)))) := by
    simpa only [Function.comp_def, he] using ht
  exact tendsto_nhds_unique ht'
    ((binary_grouped_signedTail_summable hs hm).hasSum.tendsto_sum_nat.const_mul (m : ℝ))

theorem triadic_pairing_eq_grouped_signedTail {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k*h k^2))
    {m : ℕ} (hm : 0 < m) :
    paretoInner h (dilation m (residue 3)) =
      (m : ℝ)*(∑' j, (anchoredSignedTail h (m*(3*j+1)) +
        anchoredSignedTail h (m*(3*j+2)) - 2*anchoredSignedTail h (m*(3*j+3)))) := by
  have he : ∀ K, (∑ n ∈ Finset.range ((m*3)*K+1), anchoredSignedTail h n *
      ((if m ∣ n then (m : ℝ) else 0) -
        (if m*3 ∣ n then ((m*3 : ℕ) : ℝ) else 0))) =
      (m : ℝ)*(∑ j ∈ Finset.range K, (anchoredSignedTail h (m*(3*j+1)) +
        anchoredSignedTail h (m*(3*j+2)) - 2*anchoredSignedTail h (m*(3*j+3)))) := by
    intro K
    rw [finite_signed_divisibility_sum _ hm (by norm_num)]
    have hb := triadic_block_sum (fun j => anchoredSignedTail h (m*j))
      (by simp [anchoredSignedTail_zero]) K
    simpa only [Nat.cast_ofNat] using congrArg (fun x : ℝ => (m : ℝ)*x) hb
  have ht := (paretoInner_eq_limit_signed_divisibility_jumps hs m 3 (by norm_num)).comp
    (multiple_cutoff_tendsto hm (by norm_num : 0 < 3))
  have ht' : Tendsto (fun K => (m : ℝ)*(∑ j ∈ Finset.range K,
      (anchoredSignedTail h (m*(3*j+1)) + anchoredSignedTail h (m*(3*j+2)) -
        2*anchoredSignedTail h (m*(3*j+3)))))
      atTop (nhds (paretoInner h (dilation m (residue 3)))) := by
    simpa only [Function.comp_def, he] using ht
  exact tendsto_nhds_unique ht'
    ((triadic_grouped_signedTail_summable hs hm).hasSum.tendsto_sum_nat.const_mul (m : ℝ))

theorem LegalAnnihilator.binary_grouped_signedTail_eq_zero
    {S : Set ℕ} {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hS : 2 ∈ S) {m : ℕ} (hm : 0 < m) :
    (∑' j, (anchoredSignedTail h (m*(2*j+1)) -
      anchoredSignedTail h (m*(2*j+2)))) = 0 := by
  have ho := hh.2 _ (dilation_generator_mem S hS hm)
  rw [dyadic_pairing_eq_grouped_signedTail hh.1 hm] at ho
  exact (mul_eq_zero.mp ho).resolve_left (by positivity)

theorem LegalAnnihilator.triadic_grouped_signedTail_eq_zero
    {S : Set ℕ} {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hS : 3 ∈ S) {m : ℕ} (hm : 0 < m) :
    (∑' j, (anchoredSignedTail h (m*(3*j+1)) +
      anchoredSignedTail h (m*(3*j+2)) - 2*anchoredSignedTail h (m*(3*j+3)))) = 0 := by
  have ho := hh.2 _ (dilation_generator_mem S hS hm)
  rw [triadic_pairing_eq_grouped_signedTail hh.1 hm] at ho
  exact (mul_eq_zero.mp ho).resolve_left (by positivity)
end RiemannResearch.RH.Pareto
