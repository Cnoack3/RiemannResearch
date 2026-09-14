import RiemannResearch.RH.RoughComponentExhaustion
import RiemannResearch.RH.ParetoBoundedInteraction

/-!
# Forced local Möbius charges and escape from finite arithmetic components

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
section 7. All limits concern actual divisor-inverted coordinate functionals.
The balance hypotheses below are finite arithmetic endpoint membership tests,
not hypotheses about vanishing limiting errors or RH.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open Filter FiniteSeedComponentCharge PositiveSeedCone TwoSeedThreshold

noncomputable section

/-- The uniquely determined physical coefficient of the remainder at d>1. -/
def physicalRemainderCoefficient (d : ℕ) (F : ℕ → ℝ) : ℝ :=
  -mobiusDifference d F / (d : ℝ)

/-- Pointwise convergence of zero-anchored packets forces every physical
remainder coefficient separately; no interchange of an infinite sum occurs. -/
theorem physicalRemainderCoefficient_tendsto {F : ℕ → ℕ → ℝ}
    (hzero : ∀ j, F j 0 = 0)
    (hpoint : ∀ n, 0 < n → Tendsto (fun j => F j n) atTop (nhds 1))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun j => physicalRemainderCoefficient d (F j)) atTop
      (nhds (-(ArithmeticFunction.moebius d : ℝ) / (d : ℝ))) := by
  have hp (n : ℕ) : Tendsto (fun j => F j n) atTop
      (nhds (if n = 0 then 0 else 1)) := by
    by_cases hn : n = 0
    · subst n
      simpa only [hzero, ↓reduceIte] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · simpa only [if_neg hn] using hpoint n (Nat.pos_of_ne_zero hn)
  have ht := mobiusDifference_tendsto d hp
  rw [mobiusDifference_one d hd] at ht
  exact ht.neg.div_const _

/-- Every fixed finite charge cut has its exact Möbius limiting signal. -/
theorem componentCharge_tendsto_target {F : ℕ → ℕ → ℝ}
    (hzero : ∀ j, F j 0 = 0)
    (hpoint : ∀ n, 0 < n → Tendsto (fun j => F j n) atTop (nhds 1))
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    Tendsto (fun j => componentCharge S (F j)) atTop (nhds (componentSignal S)) := by
  unfold componentCharge componentSignal
  apply tendsto_finsetSum
  intro n hn
  have he := (physicalRemainderCoefficient_tendsto hzero hpoint n (hS n hn)).neg
  simpa only [physicalRemainderCoefficient, neg_div, neg_neg] using he

/-- Any fixed finite closed seed cut with nonzero signal excludes even
pointwise approximation, and therefore excludes Pareto norm approximation. -/
theorem closedComponent_no_pointwise_limit {ι : Type*}
    (S : Finset ℕ) (s : ℕ → Finset ι) (a m : ℕ → ι → ℕ) (c : ℕ → ι → ℝ)
    (hS : ∀ n ∈ S, 0 < n)
    (ha : ∀ j i, i ∈ s j → 0 < a j i)
    (hm : ∀ j i, i ∈ s j → 0 < m j i)
    (hclosed : ∀ j i, i ∈ s j → (m j i ∈ S ↔ a j i * m j i ∈ S))
    (hSignal : componentSignal S ≠ 0) :
    ¬ (∀ n, 0 < n → Tendsto
      (fun j => seedCombination (s j) (a j) (m j) (c j) n) atTop (nhds 1)) := by
  intro hpoint
  have hz (j : ℕ) : seedCombination (s j) (a j) (m j) (c j) 0 = 0 := by
    simp [seedCombination, certificateGenerator]
  have ht := componentCharge_tendsto_target hz hpoint S hS
  have hc (j : ℕ) : componentCharge S
      (seedCombination (s j) (a j) (m j) (c j)) = 0 :=
    seedCombination_componentCharge_eq_zero S (s j) (a j) (m j) (c j)
      hS (ha j) (hm j) (hclosed j)
  simp only [hc] at ht
  exact hSignal (tendsto_nhds_unique ht tendsto_const_nhds)

/-- Exact finite additivity retains every compensating coordinate. -/
theorem componentCharge_sdiff (H S : Finset ℕ) (hHS : H ⊆ S) (F : ℕ → ℝ) :
    componentCharge (S \ H) F = componentCharge S F - componentCharge H F := by
  unfold componentCharge
  exact eq_sub_of_add_eq (Finset.sum_sdiff hHS)

/-- The full remainder coefficient sum outside a fixed head is exactly its
opposite charge when the whole finite component is balanced. -/
theorem physicalRemainderCoefficient_tail_exact (H S : Finset ℕ)
    (hHS : H ⊆ S) (F : ℕ → ℝ) (hbalance : componentCharge S F = 0) :
    (∑ d ∈ S \ H, physicalRemainderCoefficient d F) = componentCharge H F := by
  have he := componentCharge_sdiff H S hHS F
  rw [hbalance] at he
  calc
    (∑ d ∈ S \ H, physicalRemainderCoefficient d F) =
        -componentCharge (S \ H) F := by
      simp only [physicalRemainderCoefficient, componentCharge, neg_div,
        Finset.sum_neg_distrib]
    _ = componentCharge H F := by rw [he]; ring

/-- Escape of a prescribed signed coefficient sum outside every fixed finite
head. The actual arithmetic endpoint closure establishes balance at every j. -/
theorem seedCombination_physicalCoefficient_tail_tendsto {ι : Type*}
    (H : Finset ℕ) (S : ℕ → Finset ℕ)
    (s : ℕ → Finset ι) (a m : ℕ → ι → ℕ) (c : ℕ → ι → ℝ)
    (hH : ∀ d ∈ H, 0 < d) (hHS : ∀ j, H ⊆ S j)
    (hS : ∀ j d, d ∈ S j → 0 < d)
    (ha : ∀ j i, i ∈ s j → 0 < a j i)
    (hm : ∀ j i, i ∈ s j → 0 < m j i)
    (hclosed : ∀ j i, i ∈ s j → (m j i ∈ S j ↔ a j i * m j i ∈ S j))
    (hpoint : ∀ n, 0 < n → Tendsto
      (fun j => seedCombination (s j) (a j) (m j) (c j) n) atTop (nhds 1)) :
    Tendsto (fun j => ∑ d ∈ S j \ H, physicalRemainderCoefficient d
      (seedCombination (s j) (a j) (m j) (c j))) atTop (nhds (componentSignal H)) := by
  have ht := componentCharge_tendsto_target
    (F := fun j => seedCombination (s j) (a j) (m j) (c j))
    (by intro j; simp [seedCombination, certificateGenerator]) hpoint H hH
  apply ht.congr'
  filter_upwards [] with j
  symm
  apply physicalRemainderCoefficient_tail_exact H (S j) (hHS j)
  exact seedCombination_componentCharge_eq_zero (S j) (s j) (a j) (m j) (c j)
    (hS j) (ha j) (hm j) (hclosed j)

/-- A finite rectangular 2,3-component through equal exponent cutoff L+1. -/
abbrev smoothChargeSet := smoothComponentVertices

/-- The exact nonzero charge persists at every positive exponent cutoff. -/
theorem smoothChargeSet_signal (q L : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6) :
    componentSignal (smoothChargeSet q L) =
      (ArithmeticFunction.moebius q : ℝ) / (3 * (q : ℝ)) := by
  have hcop : Nat.Coprime q (6 ^ (L + 1)) := by
    simpa using (Nat.Coprime.pow 1 (L + 1) hc)
  have hmult (d : ℕ) (hd : d ∈ (6 ^ (L + 1)).divisors) :
      (ArithmeticFunction.moebius (q * d) : ℝ) =
        (ArithmeticFunction.moebius q : ℝ) * (ArithmeticFunction.moebius d : ℝ) := by
    exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (Nat.Coprime.of_dvd_right (Nat.dvd_of_mem_divisors hd) hcop)
  have hsix : 6 ∣ 6 ^ (L + 1) := by
    refine ⟨6 ^ L, ?_⟩
    rw [pow_succ]
    ring
  have hsub : (6 : ℕ).divisors ⊆ (6 ^ (L + 1)).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans hsix, by positivity⟩
  have hreduce : (∑ d ∈ (6 ^ (L + 1)).divisors,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      ∑ d ∈ (6 : ℕ).divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
    symm
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hn : ArithmeticFunction.moebius d = 0 := by
      by_contra hne
      have hsf := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hne
      have hd6 := (hsf.dvd_pow_iff_dvd (by omega : L + 1 ≠ 0)).mp
        (Nat.dvd_of_mem_divisors hd)
      exact hnot (Nat.mem_divisors.mpr ⟨hd6, by omega⟩)
    simp [hn]
  have hm2 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2)
  have hm3 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)
  have hm6 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (by decide : Nat.Coprime 2 3)
  norm_num [hm2, hm3] at hm6
  have hsum : (∑ d ∈ (6 ^ (L + 1)).divisors,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) = (1 : ℝ) / 3 := by
    rw [hreduce, show (6 : ℕ).divisors = {1, 2, 3, 6} by decide]
    norm_num [hm2, hm3, hm6]
  unfold componentSignal smoothChargeSet smoothComponentVertices
  rw [Finset.sum_image]
  · calc
      (∑ d ∈ (6 ^ (L + 1)).divisors,
          (ArithmeticFunction.moebius (q * d) : ℝ) / ((q * d : ℕ) : ℝ)) =
          (ArithmeticFunction.moebius q : ℝ) / (q : ℝ) *
            ∑ d ∈ (6 ^ (L + 1)).divisors,
              (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [hmult d hd, Nat.cast_mul]
        ring
      _ = _ := by rw [hsum]; ring
  · intro d hd e he hde
    exact Nat.eq_of_mul_eq_mul_left hq hde

/-- Every actual two-seed approximating sequence has a nonzero prescribed
compensating physical coefficient sum outside every fixed smooth rectangle.
All geometric closure hypotheses are discharged by finite edge exhaustion. -/
theorem twoSeed_smoothComponent_charge_escapes {ι : Type*}
    (q K : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (s : ℕ → Finset ι) (a m : ℕ → ι → ℕ) (c : ℕ → ι → ℝ)
    (ha : ∀ j i, i ∈ s j → a j i = 2 ∨ a j i = 3)
    (hm : ∀ j i, i ∈ s j → 0 < m j i)
    (hpoint : ∀ n, 0 < n → Tendsto
      (fun j => seedCombination (s j) (a j) (m j) (c j) n) atTop (nhds 1)) :
    ∃ L : ℕ → ℕ, (∀ j, K ≤ L j) ∧
      Tendsto (fun j => ∑ d ∈ smoothChargeSet q (L j) \ smoothChargeSet q K,
        physicalRemainderCoefficient d
          (seedCombination (s j) (a j) (m j) (c j))) atTop
        (nhds ((ArithmeticFunction.moebius q : ℝ) / (3 * (q : ℝ)))) := by
  classical
  have hex (j : ℕ) := smoothComponent_finite_edges_eventually_closed q hq hc
    (s j) (a j) (m j) (ha j)
  choose L hL using hex
  refine ⟨fun j => max K (L j), fun j => le_max_left _ _, ?_⟩
  have hpos (T d : ℕ) (hd : d ∈ smoothChargeSet q T) : 0 < d := by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mul_pos hq (Nat.pos_of_mem_divisors he)
  have ht := seedCombination_physicalCoefficient_tail_tendsto
    (smoothChargeSet q K) (fun j => smoothChargeSet q (max K (L j)))
    s a m c (hpos K)
    (fun j => smoothComponentVertices_mono q K _ (le_max_left _ _))
    (fun j => hpos (max K (L j)))
    (by intro j i hi; rcases ha j i hi with h | h <;> omega) hm
    (fun j => hL j (max K (L j)) (le_max_right _ _)) hpoint
  simpa only [smoothChargeSet_signal q K hq hc] using ht

/-- Forbidding outward seed edges at any one fixed smooth rectangle with
nonzero Möbius root imposes a uniform positive full Pareto error floor.
Inward closure is proved arithmetically and is not an extra hypothesis. -/
theorem bounded_smoothComponent_fullError_lower {ι : Type*}
    (q K : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (hmu : ArithmeticFunction.moebius q ≠ 0)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3) (hm : ∀ i ∈ s, 0 < m i)
    (hcap : ∀ i ∈ s, m i ∈ smoothChargeSet q K →
      a i * m i ∈ smoothChargeSet q K) :
    0 < ((ArithmeticFunction.moebius q : ℝ) / (3 * (q : ℝ))) ^ 2 /
      componentDualNorm (smoothChargeSet q K) (q * 6 ^ (K + 1)) ∧
    ((ArithmeticFunction.moebius q : ℝ) / (3 * (q : ℝ))) ^ 2 /
      componentDualNorm (smoothChargeSet q K) (q * 6 ^ (K + 1)) ≤
        ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have hverts (d : ℕ) (hd : d ∈ smoothChargeSet q K) :
      0 < d ∧ d ≤ q * 6 ^ (K + 1) := by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨Nat.mul_pos hq (Nat.pos_of_mem_divisors he),
      Nat.mul_le_mul_left q (Nat.le_of_dvd (by positivity) (Nat.dvd_of_mem_divisors he))⟩
  have he := closedComponent_seedCombination_fullError_lower
    (smoothChargeSet q K) (q * 6 ^ (K + 1)) s a m c hverts
    (by intro i hi; rcases ha i hi with h | h <;> omega) hm
    (by
      intro i hi
      refine ⟨hcap i hi, ?_⟩
      apply smoothComponentVertices_of_mul_mem q K (a i) (m i) hq hc
      rcases ha i hi with h | h <;> simp [h])
    (by
      rw [smoothChargeSet_signal q K hq hc]
      apply div_ne_zero
      · exact_mod_cast hmu
      · positivity)
  simpa only [smoothChargeSet_signal q K hq hc] using he

end
end RiemannResearch.RH.Pareto
