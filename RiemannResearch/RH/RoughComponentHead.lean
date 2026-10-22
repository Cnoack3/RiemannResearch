import RiemannResearch.RH.FiniteSeedComponentCharge
import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.RH.OneBoundaryRepairObstruction

/-!
# Exact rough-component profiles on an interpolated head

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 8, equation (39). The high component charges are arbitrary and
are retained through exact balance before their floor terms vanish on
the head. The final profile uses the actual Möbius function.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open OneBoundaryRepair FiniteSeedComponentCharge PositiveSeedCone

noncomputable section

/-- The integer version of C(k/q), with every floor term included. -/
def roughHeadProfile (q k : ℕ) : ℝ :=
  floorBlock q k - floorBlock (2 * q) k - floorBlock (3 * q) k +
    floorBlock (6 * q) k

private theorem smooth_divisor_moebius_zero (L d : ℕ)
    (hd : d ∈ (6 ^ (L + 1)).divisors) (hnot : ¬ d ∣ 6) :
    ArithmeticFunction.moebius d = 0 := by
  by_contra hn
  have hs := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hn
  exact hnot ((hs.dvd_pow_iff_dvd (by omega : L + 1 ≠ 0)).mp
    (Nat.dvd_of_mem_divisors hd))

/-- All smooth Möbius-floor sums reduce exactly to the four squarefree terms. -/
theorem smooth_mobius_floor_profile (q L k : ℕ) (hc : Nat.Coprime q 6) :
    (∑ d ∈ (6 ^ (L + 1)).divisors,
      (ArithmeticFunction.moebius (q * d) : ℝ) * floorBlock (q * d) k) =
        (ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q k := by
  have hcop : Nat.Coprime q (6 ^ (L + 1)) := by
    simpa using (Nat.Coprime.pow 1 (L + 1) hc)
  have hmult (d : ℕ) (hd : d ∈ (6 ^ (L + 1)).divisors) :
      (ArithmeticFunction.moebius (q * d) : ℝ) =
        (ArithmeticFunction.moebius q : ℝ) * (ArithmeticFunction.moebius d : ℝ) := by
    have hqd : Nat.Coprime q d :=
      Nat.Coprime.of_dvd_right (Nat.dvd_of_mem_divisors hd) hcop
    exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqd
  have hsum : (∑ d ∈ (6 ^ (L + 1)).divisors,
      (ArithmeticFunction.moebius (q * d) : ℝ) * floorBlock (q * d) k) =
      (ArithmeticFunction.moebius q : ℝ) *
        ∑ d ∈ (6 ^ (L + 1)).divisors,
          (ArithmeticFunction.moebius d : ℝ) * floorBlock (q * d) k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hmult d hd]
    ring
  have hsix : 6 ∣ 6 ^ (L + 1) := by
    refine ⟨6 ^ L, ?_⟩
    rw [pow_succ]
    ring
  have hsub : (6 : ℕ).divisors ⊆ (6 ^ (L + 1)).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans hsix, by positivity⟩
  have hreduce : (∑ d ∈ (6 ^ (L + 1)).divisors,
      (ArithmeticFunction.moebius d : ℝ) * floorBlock (q * d) k) =
      ∑ d ∈ (6 : ℕ).divisors,
        (ArithmeticFunction.moebius d : ℝ) * floorBlock (q * d) k := by
    symm
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hn : ¬ d ∣ 6 := by
      intro h
      exact hnot (Nat.mem_divisors.mpr ⟨h, by omega⟩)
    rw [smooth_divisor_moebius_zero L d hd hn]
    simp
  rw [hsum, hreduce]
  congr 1
  have hdiv : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
  have hm2 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2)
  have hm3 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)
  have hm6 : ArithmeticFunction.moebius 6 = 1 := by
    have he := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 2 3)
    norm_num [hm2, hm3] at he
    exact he
  rw [hdiv]
  norm_num [roughHeadProfile, Nat.mul_comm q, hm2, hm3, hm6] <;> ring

/-- A finite smooth component represented by its balanced residue charges. -/
def finiteSmoothComponent (q L : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  -(∑ d ∈ (6 ^ (L + 1)).divisors, c d * residue (q * d) k)

/-- Every charge, including high corrections, is included in the exact floor identity. -/
theorem finiteSmoothComponent_floor (q L k : ℕ) (c : ℕ → ℝ)
    (hbalance : ∑ d ∈ (6 ^ (L + 1)).divisors, c d = 0) :
    finiteSmoothComponent q L c k =
      ∑ d ∈ (6 ^ (L + 1)).divisors,
        ((q * d : ℕ) : ℝ) * c d * floorBlock (q * d) k := by
  have hterm (d : ℕ) :
      ((q * d : ℕ) : ℝ) * c d * floorBlock (q * d) k =
        (k : ℝ) * c d - c d * residue (q * d) k := by
    have he := floorBlock_mul (q * d) k
    nlinarith [congrArg (fun x : ℝ => c d * x) he]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hbalance]
  simp [finiteSmoothComponent]

/-- Balanced components with the forced head charges have the exact rough profile. -/
theorem finiteSmoothComponent_exact_head (q L N k : ℕ) (hq : 0 < q)
    (hc : Nat.Coprime q 6) (c : ℕ → ℝ)
    (hbalance : ∑ d ∈ (6 ^ (L + 1)).divisors, c d = 0)
    (hcharge : ∀ d ∈ (6 ^ (L + 1)).divisors, q * d ≤ N →
      c d = (ArithmeticFunction.moebius (q * d) : ℝ) / ((q * d : ℕ) : ℝ))
    (hk : k ≤ N) :
    finiteSmoothComponent q L c k =
      (ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q k := by
  rw [finiteSmoothComponent_floor q L k c hbalance]
  rw [← smooth_mobius_floor_profile q L k hc]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hsmall : q * d ≤ N
  · rw [hcharge d hd hsmall]
    have hqd : ((q * d : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hq (Nat.pos_of_mem_divisors hd)))
    field_simp
  · have hlarge : k < q * d := by omega
    simp [floorBlock, Nat.div_eq_of_lt hlarge]

/-- The coefficient hypothesis in the preceding lemma is supplied by actual jump inversion. -/
theorem mobius_component_exact_head (q L N k : ℕ) (hq : 0 < q)
    (hc : Nat.Coprime q 6) (F : ℕ → ℝ) (hzero : F 0 = 0)
    (hhead : ∀ j, 0 < j → j ≤ N → F j = 1)
    (hbalance : (∑ d ∈ (6 ^ (L + 1)).divisors,
      mobiusDifference (q * d) F / ((q * d : ℕ) : ℝ)) = 0)
    (hk : k ≤ N) :
    finiteSmoothComponent q L
      (fun d => mobiusDifference (q * d) F / ((q * d : ℕ) : ℝ)) k =
        (ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q k := by
  apply finiteSmoothComponent_exact_head q L N k hq hc _ hbalance _ hk
  intro d hd hqdN
  rw [exact_head_mobiusDifference hzero hhead
    (Nat.mul_pos hq (Nat.pos_of_mem_divisors hd)) hqdN]

/-- A finite rough component containing both or neither endpoint of every edge.
The condition is geometric closure of a chosen finite component, not an
arithmetic cancellation or energy hypothesis. -/
def smoothComponentVertices (q L : ℕ) : Finset ℕ :=
  (6 ^ (L + 1)).divisors.image (fun d => q * d)

/-- Equation (39) for actual signed legal packets, with zero component charge
derived from the actual finite edge presentation. -/
theorem seed_component_exact_head {ι : Type*} (q L N k : ℕ) (hq : 0 < q)
    (hc : Nat.Coprime q 6) (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3) (hm : ∀ i ∈ s, 0 < m i)
    (hclosed : ∀ i ∈ s, m i ∈ smoothComponentVertices q L ↔
      a i * m i ∈ smoothComponentVertices q L)
    (hhead : ∀ j, 0 < j → j ≤ N → seedCombination s a m c j = 1)
    (hk : k ≤ N) :
    finiteSmoothComponent q L
      (fun d => mobiusDifference (q * d) (seedCombination s a m c) /
        ((q * d : ℕ) : ℝ)) k =
          (ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q k := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with he | he <;> omega
  have hverts : ∀ n ∈ smoothComponentVertices q L, 0 < n := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact Nat.mul_pos hq (Nat.pos_of_mem_divisors hd)
  have hbal := seedCombination_componentCharge_eq_zero
    (smoothComponentVertices q L) s a m c hverts ha0 hm hclosed
  have hbalance : (∑ d ∈ (6 ^ (L + 1)).divisors,
      mobiusDifference (q * d) (seedCombination s a m c) / ((q * d : ℕ) : ℝ)) = 0 := by
    unfold componentCharge smoothComponentVertices at hbal
    rw [Finset.sum_image] at hbal
    · exact hbal
    · intro d hd e he hde
      exact Nat.eq_of_mul_eq_mul_left hq hde
  apply mobius_component_exact_head q L N k hq hc (seedCombination s a m c)
    _ hhead hbalance hk
  simp [seedCombination, TwoSeedThreshold.certificateGenerator]

end
end RiemannResearch.RH.Pareto
