import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.RH.ParetoNewPacketPeriodicity

/-!
# Complete periodic packet Gram matrices as weighted Green forms

Source: the user's primitive-conductor / Green-kernel calculation,
22 September 2026. The argument combines exact periodic Pareto regrouping
with finite summation of the Ramanujan charges. The residue weights are
`progressionWeight L k`, each of which contains its entire infinite
arithmetic progression. Thus the finite Green expression is the full
inner product, rather than a truncation at the end of the period.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Green kernel associated to an arbitrary weight on the positive finite interval. -/
def weightedPrefixGreenKernel (L : ℕ) (w : ℕ → ℝ) (m n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 (L+1), if max m n ≤ k then w k else 0

/-- The periodic Green kernel contains the full weights of all congruence classes. -/
def periodicGreenKernel (L m n : ℕ) : ℝ :=
  weightedPrefixGreenKernel L (progressionWeight L) m n

theorem periodicGreenKernel_symm (L m n : ℕ) :
    periodicGreenKernel L m n = periodicGreenKernel L n m := by
  simp only [periodicGreenKernel, weightedPrefixGreenKernel, max_comm]

/-- Inside the positive interval, the kernel is the sum of complete residue weights. -/
theorem periodicGreenKernel_eq_interval (L m n : ℕ) (hm : 0 < m) (_hn : 0 < n) :
    periodicGreenKernel L m n =
      ∑ k ∈ Finset.Ico (max m n) (L+1), progressionWeight L k := by
  unfold periodicGreenKernel weightedPrefixGreenKernel
  rw [← Finset.sum_filter]
  have hset : (Finset.Ico 1 (L+1)).filter (fun k => max m n ≤ k) =
      Finset.Ico (max m n) (L+1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, max_le_iff]
    omega
  rw [hset]

theorem periodicGreenKernel_nonneg (L m n : ℕ) (hL : 0 < L) :
    0 ≤ periodicGreenKernel L m n := by
  unfold periodicGreenKernel weightedPrefixGreenKernel
  apply Finset.sum_nonneg
  intro k hk
  by_cases hmn : max m n ≤ k
  · simp only [if_pos hmn]
    exact (progressionWeight_pos L k hL (by
      have := (Finset.mem_Ico.mp hk).1
      omega)).le
  · simp only [if_neg hmn, le_refl]

private theorem periodicGreen_sum_prefix_indicator (f : ℕ → ℝ) (L k : ℕ)
    (hk : k ≤ L) :
    (∑ m ∈ Finset.Ico 1 (L+1), if m ≤ k then f m else 0) =
      ∑ m ∈ Finset.Ico 1 (k+1), f m := by
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico]
  omega

private theorem periodicGreen_finite_prefix_gram
    (s : Finset ℕ) (a b w : ℕ → ℝ) :
    (∑ k ∈ s, w k *
        ((∑ m ∈ s, if m ≤ k then a m else 0) *
          (∑ n ∈ s, if n ≤ k then b n else 0))) =
      ∑ m ∈ s, ∑ n ∈ s, a m * b n *
        (∑ k ∈ s, if max m n ≤ k then w k else 0) := by
  calc
    _ = ∑ k ∈ s, ∑ m ∈ s, ∑ n ∈ s,
        (if m ≤ k then a m else 0) * (if n ≤ k then b n else 0) * w k := by
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ m ∈ s, ∑ n ∈ s, ∑ k ∈ s,
        (if m ≤ k then a m else 0) * (if n ≤ k then b n else 0) * w k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hm : m ≤ k <;> by_cases hn : n ≤ k <;>
        simp [hm, hn]

/-- Finite cumulative charges give a Green form for any finite weight. -/
theorem weighted_green_gram_of_prefix (L : ℕ) (F G c d w : ℕ → ℝ)
    (hF : ∀ k, F k = -∑ m ∈ Finset.Ico 1 (k+1), c m)
    (hG : ∀ k, G k = -∑ m ∈ Finset.Ico 1 (k+1), d m) :
    (∑ k ∈ Finset.Ico 1 (L+1), w k * (F k * G k)) =
      ∑ m ∈ Finset.Ico 1 (L+1), ∑ n ∈ Finset.Ico 1 (L+1),
        c m * d n * weightedPrefixGreenKernel L w m n := by
  calc
    _ = ∑ k ∈ Finset.Ico 1 (L+1), w k *
        ((∑ m ∈ Finset.Ico 1 (L+1), if m ≤ k then c m else 0) *
          (∑ n ∈ Finset.Ico 1 (L+1), if n ≤ k then d n else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkL : k ≤ L := by
        have := (Finset.mem_Ico.mp hk).2
        omega
      rw [periodicGreen_sum_prefix_indicator _ L k hkL,
        periodicGreen_sum_prefix_indicator _ L k hkL, hF k, hG k]
      ring
    _ = _ := by
      exact periodicGreen_finite_prefix_gram (Finset.Ico 1 (L+1)) c d w

private theorem periodicGreen_sum_fin_positive (L : ℕ) (f : ℕ → ℝ) :
    (∑ r : Fin L, f (r.val+1)) = ∑ k ∈ Finset.Ico 1 (L+1), f k := by
  classical
  refine Finset.sum_bij (fun r _ => r.val+1) ?_ ?_ ?_ ?_
  · intro r _
    simp only [Finset.mem_Ico]
    constructor
    · omega
    · exact Nat.add_lt_add_right r.isLt 1
  · intro r _ s _ hrs
    apply Fin.ext
    omega
  · intro k hk
    have hk' := Finset.mem_Ico.mp hk
    refine ⟨⟨k-1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega
  · intro r _
    rfl

/-- A full periodic inner product is exactly one finite Green form; no tail is removed. -/
theorem periodic_paretoInner_green_of_prefix
    (L : ℕ) (hL : 0 < L) (F G c d : ℕ → ℝ) {C D : ℝ}
    (hFb : ∀ k, |F k| ≤ C) (hGb : ∀ k, |G k| ≤ D)
    (hFp : ∀ k, F (k+L) = F k) (hGp : ∀ k, G (k+L) = G k)
    (hF : ∀ k, F k = -∑ m ∈ Finset.Ico 1 (k+1), c m)
    (hG : ∀ k, G k = -∑ m ∈ Finset.Ico 1 (k+1), d m) :
    paretoInner F G =
      ∑ m ∈ Finset.Ico 1 (L+1), ∑ n ∈ Finset.Ico 1 (L+1),
        c m * d n * periodicGreenKernel L m n := by
  rw [periodic_paretoInner_mixed L hL F G hFb hGb hFp hGp,
    periodicGreen_sum_fin_positive L (fun k => progressionWeight L k * (F k * G k))]
  exact weighted_green_gram_of_prefix L F G c d (progressionWeight L) hF hG

/-- The full packet Gram entry is `Cᵀ K C` at any common period of the conductors. -/
theorem ramanujanPacket_periodic_green_gram (L q r : ℕ)
    (hL : 0 < L) (hq : 1 < q) (hr : 1 < r) (hqL : q ∣ L) (hrL : r ∣ L) :
    paretoInner (ramanujanPacket q) (ramanujanPacket r) =
      ∑ m ∈ Finset.Ico 1 (L+1), ∑ n ∈ Finset.Ico 1 (L+1),
        ramanujanSum q m * ramanujanSum r n * periodicGreenKernel L m n := by
  exact periodic_paretoInner_green_of_prefix L hL
    (ramanujanPacket q) (ramanujanPacket r) (ramanujanSum q) (ramanujanSum r)
    (ramanujanPacket_abs_le q) (ramanujanPacket_abs_le r)
    (ramanujanPacket_period_of_dvd q L hqL)
    (ramanujanPacket_period_of_dvd r L hrL)
    (fun k => ramanujanPacket_prefix q k hq) (fun k => ramanujanPacket_prefix r k hr)

/-- Arbitrary finite signed packet combinations have the same complete-period Green form. -/
theorem packetCombination_periodic_green_gram
    (L : ℕ) (s t : Finset ℕ) (a b : ℕ → ℝ) (hL : 0 < L)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q)
    (hsL : ∀ q ∈ s, q ∣ L) (htL : ∀ q ∈ t, q ∣ L) :
    paretoInner (fun k => ∑ q ∈ s, a q * ramanujanPacket q k)
      (fun k => ∑ q ∈ t, b q * ramanujanPacket q k) =
      ∑ m ∈ Finset.Ico 1 (L+1), ∑ n ∈ Finset.Ico 1 (L+1),
        (∑ q ∈ s, a q * ramanujanSum q m) *
          (∑ q ∈ t, b q * ramanujanSum q n) * periodicGreenKernel L m n := by
  obtain ⟨C, hC⟩ := packetCombination_bounded s a
  obtain ⟨D, hD⟩ := packetCombination_bounded t b
  apply periodic_paretoInner_green_of_prefix L hL _ _ _ _ hC hD
  · intro k
    apply Finset.sum_congr rfl
    intro q hq
    rw [ramanujanPacket_period_of_dvd q L (hsL q hq)]
  · intro k
    apply Finset.sum_congr rfl
    intro q hq
    rw [ramanujanPacket_period_of_dvd q L (htL q hq)]
  · exact packetCombination_prefix s a hs
  · exact packetCombination_prefix t b ht

/-- When the cumulative functions vanish at the end of the period, the complete
inner product is represented on the charge indices `1,...,L-1`.
The weights remain the full-period progression weights. -/
theorem periodic_paretoInner_green_of_prefix_zero_boundary
    (L : ℕ) (hL : 0 < L) (F G c d : ℕ → ℝ) {C D : ℝ}
    (hFb : ∀ k, |F k| ≤ C) (hGb : ∀ k, |G k| ≤ D)
    (hFp : ∀ k, F (k+L) = F k) (hGp : ∀ k, G (k+L) = G k)
    (hF : ∀ k, F k = -∑ m ∈ Finset.Ico 1 (k+1), c m)
    (hG : ∀ k, G k = -∑ m ∈ Finset.Ico 1 (k+1), d m)
    (hFL : F L = 0) (hGL : G L = 0) :
    paretoInner F G =
      ∑ m ∈ Finset.Ico 1 L, ∑ n ∈ Finset.Ico 1 L,
        c m * d n * weightedPrefixGreenKernel (L-1) (progressionWeight L) m n := by
  have hLm : L-1+1 = L := by omega
  rw [periodic_paretoInner_mixed L hL F G hFb hGb hFp hGp,
    periodicGreen_sum_fin_positive L (fun k => progressionWeight L k * (F k * G k)),
    Finset.sum_Ico_succ_top (by omega : 1 ≤ L)]
  simp only [hFL, hGL, mul_zero, add_zero]
  simpa only [hLm] using
    weighted_green_gram_of_prefix (L-1) F G c d (progressionWeight L) hF hG

/-- The actual periodic packet Gram matrix uses `1,...,L-1`; no infinite
Pareto tail is omitted when the zero endpoint of the period is removed. -/
theorem ramanujanPacket_periodic_green_gram_zero_boundary (L q r : ℕ)
    (hL : 0 < L) (hq : 1 < q) (hr : 1 < r) (hqL : q ∣ L) (hrL : r ∣ L) :
    paretoInner (ramanujanPacket q) (ramanujanPacket r) =
      ∑ m ∈ Finset.Ico 1 L, ∑ n ∈ Finset.Ico 1 L,
        ramanujanSum q m * ramanujanSum r n *
          weightedPrefixGreenKernel (L-1) (progressionWeight L) m n := by
  have hq0 : ramanujanPacket q L = 0 := by
    calc
      _ = ramanujanPacket q 0 := by
        simpa only [zero_add] using ramanujanPacket_period_of_dvd q L hqL 0
      _ = 0 := by simp [ramanujanPacket, residue]
  have hr0 : ramanujanPacket r L = 0 := by
    calc
      _ = ramanujanPacket r 0 := by
        simpa only [zero_add] using ramanujanPacket_period_of_dvd r L hrL 0
      _ = 0 := by simp [ramanujanPacket, residue]
  exact periodic_paretoInner_green_of_prefix_zero_boundary L hL
    (ramanujanPacket q) (ramanujanPacket r) (ramanujanSum q) (ramanujanSum r)
    (ramanujanPacket_abs_le q) (ramanujanPacket_abs_le r)
    (ramanujanPacket_period_of_dvd q L hqL)
    (ramanujanPacket_period_of_dvd r L hrL)
    (fun k => ramanujanPacket_prefix q k hq) (fun k => ramanujanPacket_prefix r k hr)
    hq0 hr0

end
end RiemannResearch.RH.Pareto
