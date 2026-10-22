import RiemannResearch.RH.FiniteSeedComponentCharge
import RiemannResearch.RH.ArithmeticChargeEscape
import RiemannResearch.RH.RoughComponentNormDivergence

/-!
# The actual rough-component projection and its necessary norm divergence

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
section 7. The algebraic component is identified on every actual generator;
the pointwise limit is then computed by finite Möbius inversion.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators Topology
open Filter OneBoundaryRepair PositiveSeedCone FiniteSeedComponentCharge TwoSeedThreshold
noncomputable section
attribute [local instance] Classical.propDecidable

def InRoughComponent (q d : ℕ) : Prop := ∃ L, d ∈ smoothComponentVertices q L

theorem inRoughComponent_mul_iff (q a m : ℕ) (hq : 0 < q)
    (hc : Nat.Coprime q 6) (ha : a ∣ 6) :
    InRoughComponent q (a * m) ↔ InRoughComponent q m := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, smoothComponentVertices_of_mul_mem q L a m hq hc ha hL⟩
  · rintro ⟨L, hL⟩
    exact ⟨L + 1, smoothComponentVertices_mul_succ q L a m ha hL⟩

def roughComponentProjection (q : ℕ) (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 n, if InRoughComponent q d then
    mobiusDifference d F * floorBlock d n else 0

private theorem floor_delta_sum (n m : ℕ) (hm : 0 < m) (x : ℝ) :
    (∑ d ∈ Finset.Icc 1 n, if d = m then x * floorBlock d n else 0) =
      x * floorBlock m n := by
  by_cases hmn : m ≤ n
  · simp [Finset.mem_Icc, show 1 ≤ m by omega, hmn]
  · have hnm : n < m := by omega
    simp [Finset.mem_Icc, hmn, floorBlock, Nat.div_eq_of_lt hnm]

/-- Projection selects whole actual seed generators, without splitting their
positive and negative endpoints or discarding any covariance. -/
theorem roughComponentProjection_generator (q a m n : ℕ) (hq : 0 < q)
    (hc : Nat.Coprime q 6) (ha : a = 2 ∨ a = 3) (hm : 0 < m) :
    roughComponentProjection q (certificateGenerator a m) n =
      if InRoughComponent q m then certificateGenerator a m n else 0 := by
  have ha0 : 0 < a := by rcases ha with h | h <;> omega
  have had : a ∣ 6 := by rcases ha with h | h <;> simp [h]
  have hcomp := inRoughComponent_mul_iff q a m hq hc had
  have hi (d : ℕ) (hd : d ∈ Finset.Icc 1 n) :
      (if InRoughComponent q d then
        mobiusDifference d (certificateGenerator a m) * floorBlock d n else 0) =
      (if d = m then (if InRoughComponent q m then (m : ℝ) else 0) *
        floorBlock d n else 0) -
      (if d = a * m then (if InRoughComponent q (a * m) then
        ((a * m : ℕ) : ℝ) else 0) * floorBlock d n else 0) := by
    rw [mobiusDifference_generator d a m (by have := (Finset.mem_Icc.mp hd).1; omega)]
    split_ifs <;> simp_all <;> ring
  unfold roughComponentProjection
  rw [Finset.sum_congr rfl hi, Finset.sum_sub_distrib,
    floor_delta_sum n m hm, floor_delta_sum n (a * m) (Nat.mul_pos ha0 hm)]
  rw [hcomp]
  split_ifs with h
  · have h1 := floorBlock_mul m n
    have h2 := floorBlock_mul (a * m) n
    change _ = residue (a * m) n - residue m n
    linarith
  · ring

theorem roughComponentProjection_seedCombination {ι : Type*}
    (q n : ℕ) (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) :
    roughComponentProjection q (seedCombination s a m c) n =
      ∑ i ∈ s, c i * roughComponentProjection q (certificateGenerator (a i) (m i)) n := by
  have hlin (d : ℕ) : mobiusDifference d (seedCombination s a m c) =
      ∑ i ∈ s, c i * mobiusDifference d (certificateGenerator (a i) (m i)) := by
    unfold mobiusDifference seedCombination
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro e he
    ring
  unfold roughComponentProjection
  have ht (d : ℕ) :
      (if InRoughComponent q d then mobiusDifference d (seedCombination s a m c) *
        floorBlock d n else 0) =
      ∑ i ∈ s, c i * (if InRoughComponent q d then
        mobiusDifference d (certificateGenerator (a i) (m i)) * floorBlock d n else 0) := by
    split_ifs
    · rw [hlin, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

/-- The finite algebraic projection is itself a signed legal packet. -/
theorem roughComponentProjection_seedCombination_eq {ι : Type*}
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3) (hm : ∀ i ∈ s, 0 < m i) :
    roughComponentProjection q (seedCombination s a m c) =
      seedCombination s a m (fun i => if InRoughComponent q (m i) then c i else 0) := by
  funext n
  rw [roughComponentProjection_seedCombination]
  apply Finset.sum_congr rfl
  intro i hi
  rw [roughComponentProjection_generator q (a i) (m i) n hq hc (ha i hi) (hm i hi)]
  by_cases h : InRoughComponent q (m i) <;> simp [h]

private theorem roughComponent_finite_stabilizes (q : ℕ) (s : Finset ℕ) :
    ∃ K : ℕ, ∀ L, K ≤ L → ∀ d ∈ s,
      (d ∈ smoothComponentVertices q L ↔ InRoughComponent q d) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert d s hd ih =>
    obtain ⟨K, hK⟩ := ih
    by_cases hx : InRoughComponent q d
    · obtain ⟨J, hJ⟩ := hx
      refine ⟨max K J, ?_⟩
      intro L hL e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact ⟨fun h => ⟨L, h⟩, fun _ =>
          smoothComponentVertices_mono q J L ((le_max_right _ _).trans hL) hJ⟩
      · exact hK L ((le_max_left _ _).trans hL) e he
    · refine ⟨K, ?_⟩
      intro L hL e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact ⟨fun h => False.elim (hx ⟨L, h⟩), fun h => False.elim (hx h)⟩
      · exact hK L hL e he

/-- The target's local component is exactly the four-floor rough profile. -/
theorem roughComponentProjection_one (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (n : ℕ) :
    roughComponentProjection q (fun k => if k = 0 then 0 else 1) n =
      (ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q n := by
  classical
  obtain ⟨K, hK⟩ := roughComponent_finite_stabilizes q (Finset.Icc 1 n)
  have hpos (d : ℕ) (hd : d ∈ smoothComponentVertices q K) : 0 < d := by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mul_pos hq (Nat.pos_of_mem_divisors he)
  have htrunc : (∑ d ∈ smoothComponentVertices q K,
      (ArithmeticFunction.moebius d : ℝ) * floorBlock d n) =
      ∑ d ∈ Finset.Icc 1 n, if d ∈ smoothComponentVertices q K then
        (ArithmeticFunction.moebius d : ℝ) * floorBlock d n else 0 := by
    calc
      _ = ∑ d ∈ smoothComponentVertices q K ∩ Finset.Icc 1 n,
          (ArithmeticFunction.moebius d : ℝ) * floorBlock d n := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro d hd hnot
        have hdn : n < d := by
          have hp := hpos d hd
          simp only [Finset.mem_inter, hd, true_and, Finset.mem_Icc] at hnot
          omega
        simp [floorBlock, Nat.div_eq_of_lt hdn]
      _ = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ∈ smoothComponentVertices q K),
          (ArithmeticFunction.moebius d : ℝ) * floorBlock d n := by
        congr 1
        ext d
        simp [and_comm]
      _ = _ := Finset.sum_filter _ _
  calc
    _ = ∑ d ∈ Finset.Icc 1 n, if d ∈ smoothComponentVertices q K then
        (ArithmeticFunction.moebius d : ℝ) * floorBlock d n else 0 := by
      unfold roughComponentProjection
      apply Finset.sum_congr rfl
      intro d hd
      rw [mobiusDifference_one d (by have := (Finset.mem_Icc.mp hd).1; omega),
        ← hK K le_rfl d hd]
      by_cases h : d ∈ smoothComponentVertices q K <;> simp [h]
    _ = ∑ d ∈ smoothComponentVertices q K,
        (ArithmeticFunction.moebius d : ℝ) * floorBlock d n := htrunc.symm
    _ = _ := by
      unfold smoothComponentVertices
      rw [Finset.sum_image]
      · exact smooth_mobius_floor_profile q K n hc
      · intro d hd e he hde
        exact Nat.eq_of_mul_eq_mul_left hq hde

/-- Norm approximants, and even pointwise approximants, force the same
pointwise rough-component limit. No exact interpolation is assumed. -/
theorem roughComponentProjection_tendsto_profile
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6) (F : ℕ → ℕ → ℝ)
    (hzero : ∀ j, F j 0 = 0)
    (hp : ∀ n, 0 < n → Tendsto (fun j => F j n) atTop (𝓝 1))
    (n : ℕ) :
    Tendsto (fun j => roughComponentProjection q (F j) n) atTop
      (𝓝 ((ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q n)) := by
  have hpoint (k : ℕ) : Tendsto (fun j => F j k) atTop
      (𝓝 (if k = 0 then 0 else 1)) := by
    by_cases hk : k = 0
    · subst k
      simpa [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [if_neg hk] using hp k (Nat.pos_of_ne_zero hk)
  rw [← roughComponentProjection_one q hq hc n]
  unfold roughComponentProjection
  apply tendsto_finsetSum
  intro d hd
  by_cases hcomp : InRoughComponent q d
  · simp only [if_pos hcomp]
    exact (mobiusDifference_tendsto d hpoint).mul_const _
  · simp only [if_neg hcomp]
    exact tendsto_const_nhds

/-- The actual component projection of each finite legal packet has summable
Pareto square norm, because it is another finite signed legal packet. -/
theorem roughComponentProjection_seed_square_summable {ι : Type*}
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3) (hm : ∀ i ∈ s, 0 < m i) :
    Summable (fun n : ℕ => positiveWeight (n + 1) *
      roughComponentProjection q (seedCombination s a m c) (n + 1) ^ 2) := by
  rw [roughComponentProjection_seedCombination_eq q hq hc s a m c ha hm]
  let c' : ι → ℝ := fun i => if InRoughComponent q (m i) then c i else 0
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  have hbound (n : ℕ) : |seedCombination s a m c' n ^ 2| ≤
      coefficientBound s a m c' ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := seedCombination_abs_le s a m c' ha0 hm n
    have hs := mul_self_le_mul_self (abs_nonneg _) h
    simpa only [← pow_two, sq_abs] using hs
  exact (summable_nat_add_iff 1).2 (weighted_summable_of_bounded hbound)

/-- Every nonzero arithmetic component of any successful legal approximation
has full square norm tending to infinity. Thus bounded full packets require
unbounded cancellation between their arithmetic components. -/
theorem twoSeed_roughComponent_energy_tendsto_atTop {ι : Type*}
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (hmu : ArithmeticFunction.moebius q ≠ 0)
    (s : ℕ → Finset ι) (a m : ℕ → ι → ℕ) (c : ℕ → ι → ℝ)
    (ha : ∀ j i, i ∈ s j → a j i = 2 ∨ a j i = 3)
    (hm : ∀ j i, i ∈ s j → 0 < m j i)
    (hp : ∀ n, 0 < n → Tendsto
      (fun j => seedCombination (s j) (a j) (m j) (c j) n) atTop (𝓝 1)) :
    Tendsto (fun j => ∑' n : ℕ, positiveWeight (n + 1) *
      roughComponentProjection q (seedCombination (s j) (a j) (m j) (c j))
        (n + 1) ^ 2) atTop atTop := by
  apply roughMobiusProfile_pointwise_forces_energy_divergence q hq hmu
    (fun j => roughComponentProjection q (seedCombination (s j) (a j) (m j) (c j)))
  · intro j
    exact roughComponentProjection_seed_square_summable q hq hc
      (s j) (a j) (m j) (c j) (ha j) (hm j)
  · intro n hn
    apply roughComponentProjection_tendsto_profile q hq hc
      (fun j => seedCombination (s j) (a j) (m j) (c j))
    · intro j
      simp [seedCombination, certificateGenerator]
    · exact hp

end
end RiemannResearch.RH.Pareto
