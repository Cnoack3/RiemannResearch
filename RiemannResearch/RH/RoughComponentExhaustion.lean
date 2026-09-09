import RiemannResearch.RH.RoughComponentHead

/-!
# Automatic finite exhaustion of each rough component of a legal packet

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 8. For a finite two-ratio edge presentation, sufficiently large
smooth divisor rectangles contain both or neither endpoint of every edge.
This discharges the geometric closure hypothesis of seed_component_exact_head;
it supplies no global energy or cancellation bound.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open OneBoundaryRepair FiniteSeedComponentCharge PositiveSeedCone

noncomputable section

theorem smoothComponentVertices_mono (q L K : ℕ) (hLK : L ≤ K) :
    smoothComponentVertices q L ⊆ smoothComponentVertices q K := by
  intro m hm
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
  apply Finset.mem_image.mpr
  refine ⟨d, ?_, rfl⟩
  apply Nat.mem_divisors.mpr
  exact ⟨(Nat.dvd_of_mem_divisors hd).trans
    (pow_dvd_pow 6 (by omega : L + 1 ≤ K + 1)), by positivity⟩

/-- Multiplication by either legal ratio moves a vertex into the next rectangle. -/
theorem smoothComponentVertices_mul_succ (q L a m : ℕ) (ha : a ∣ 6)
    (hm : m ∈ smoothComponentVertices q L) :
    a * m ∈ smoothComponentVertices q (L + 1) := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
  apply Finset.mem_image.mpr
  refine ⟨d * a, ?_, ?_⟩
  · apply Nat.mem_divisors.mpr
    refine ⟨?_, by positivity⟩
    simpa only [pow_succ] using Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd) ha
  · ring

/-- Dividing a component vertex by a legal ratio stays in the same rectangle.
The coprimality of the rough core is used to divide out the core first. -/
theorem smoothComponentVertices_of_mul_mem (q L a m : ℕ) (hq : 0 < q)
    (hc : Nat.Coprime q 6) (ha : a ∣ 6)
    (ham : a * m ∈ smoothComponentVertices q L) :
    m ∈ smoothComponentVertices q L := by
  obtain ⟨d, hd, hqd⟩ := Finset.mem_image.mp ham
  have hqa : Nat.Coprime q a := Nat.Coprime.of_dvd_right ha hc
  have hqdiv : q ∣ a * m := ⟨d, hqd.symm⟩
  obtain ⟨e, hme⟩ := hqa.dvd_of_dvd_mul_left hqdiv
  have hae : a * e = d := by
    apply Nat.eq_of_mul_eq_mul_left hq
    calc
      q * (a * e) = a * m := by rw [hme]; ring
      _ = q * d := hqd.symm
  have hed : e ∣ d := ⟨a, by rw [← hae]; ring⟩
  apply Finset.mem_image.mpr
  refine ⟨e, Nat.mem_divisors.mpr
    ⟨hed.trans (Nat.dvd_of_mem_divisors hd), by positivity⟩, hme.symm⟩

/-- Each individual finite edge is closed at every sufficiently large level. -/
theorem smoothComponent_edge_eventually_closed (q a m : ℕ) (hq : 0 < q)
    (hc : Nat.Coprime q 6) (ha : a ∣ 6) :
    ∃ L : ℕ, ∀ K : ℕ, L ≤ K →
      (m ∈ smoothComponentVertices q K ↔ a * m ∈ smoothComponentVertices q K) := by
  classical
  by_cases hex : ∃ L : ℕ, m ∈ smoothComponentVertices q L
  · obtain ⟨L, hm⟩ := hex
    refine ⟨L + 1, ?_⟩
    intro K hK
    have hmK : m ∈ smoothComponentVertices q K :=
      smoothComponentVertices_mono q L K (by omega) hm
    have hamK : a * m ∈ smoothComponentVertices q K :=
      smoothComponentVertices_mono q (L + 1) K hK
        (smoothComponentVertices_mul_succ q L a m ha hm)
    exact ⟨fun _ => hamK, fun _ => hmK⟩
  · refine ⟨0, ?_⟩
    intro K _hK
    constructor
    · intro hm
      exact False.elim (hex ⟨K, hm⟩)
    · intro ham
      exact False.elim (hex ⟨K,
        smoothComponentVertices_of_mul_mem q K a m hq hc ha ham⟩)

/-- A single large level simultaneously closes every edge in a finite packet;
the same is then true at every larger level. No coefficient bound is required. -/
theorem smoothComponent_finite_edges_eventually_closed {ι : Type*}
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (s : Finset ι) (a m : ι → ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3) :
    ∃ L : ℕ, ∀ K : ℕ, L ≤ K → ∀ i ∈ s,
      (m i ∈ smoothComponentVertices q K ↔ a i * m i ∈ smoothComponentVertices q K) := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty =>
      intro _ha
      refine ⟨0, ?_⟩
      intro K hK i hi
      simp at hi
  | @insert i s his ih =>
      intro ha
      have haS : ∀ j ∈ s, a j = 2 ∨ a j = 3 := by
        intro j hj
        exact ha j (Finset.mem_insert_of_mem hj)
      obtain ⟨L, hL⟩ := ih haS
      have hai : a i ∣ 6 := by
        rcases ha i (Finset.mem_insert_self i s) with h | h <;> simp [h]
      obtain ⟨M, hM⟩ := smoothComponent_edge_eventually_closed q (a i) (m i) hq hc hai
      refine ⟨max L M, ?_⟩
      intro K hK j hj
      rcases Finset.mem_insert.mp hj with he | hs
      · subst j
        exact hM K (le_trans (le_max_right L M) hK)
      · exact hL K (le_trans (le_max_left L M) hK) j hs

/-- Exact component head profiles for actual finite legal packets, with the
geometric closure condition supplied automatically by exhaustion. -/
theorem seed_component_exact_head_eventually {ι : Type*}
    (q N : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3) (hm : ∀ i ∈ s, 0 < m i)
    (hhead : ∀ j, 0 < j → j ≤ N → seedCombination s a m c j = 1) :
    ∃ L : ℕ, ∀ K : ℕ, L ≤ K → ∀ k : ℕ, k ≤ N →
      finiteSmoothComponent q K
        (fun d => mobiusDifference (q * d) (seedCombination s a m c) /
          ((q * d : ℕ) : ℝ)) k =
        (ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q k := by
  obtain ⟨L, hL⟩ := smoothComponent_finite_edges_eventually_closed q hq hc s a m ha
  refine ⟨L, ?_⟩
  intro K hK k hk
  exact seed_component_exact_head q K N k hq hc s a m c ha hm
    (hL K hK) hhead hk

end
end RiemannResearch.RH.Pareto
