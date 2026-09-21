import RiemannResearch.RH.ParetoEulerProduct
import RiemannResearch.RH.ParetoTailCapacityDuality
import Mathlib.Data.Nat.Prime.Basic

/-!
# Concrete two-point certificates for finite Pareto tail capacities

Source: user-provided argument in
`RH_Pareto_Capacity_Exact_Bounds_and_Critical_Shape_2026-09-21.md`,
the finite prime/rough-integer certificate construction.
The vector has its complete norm in the existing infinite Pareto Hilbert space.
No uniform bound over growing dictionaries or RH conclusion is asserted.
The related omitted-prime scalar obstruction is in `OmittedPrimeResidueBarrier`;
here the representer is a concrete two-point Hilbert vector and is used to
bound the actual inverse-Gram capacity, including composite rough integers.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

/-- The positive integer represented here is `p = k+2`.
In physical coordinates this is `p(p+1)e_p - p(p-1)e_(p-1)`. -/
def differenceCertificate (k : ℕ) : ThresholdHilbert :=
  (paretoWeight (k + 1))⁻¹ • paretoPointHilbert (k + 1) -
    (paretoWeight k)⁻¹ • paretoPointHilbert k

theorem differenceCertificate_inner (k : ℕ) (f : ThresholdHilbert) :
    inner ℝ (differenceCertificate k) f =
      hilbertGibbsPhysical f (k + 1) - hilbertGibbsPhysical f k := by
  have h1 : inner ℝ (paretoPointHilbert (k + 1)) f =
      paretoWeight (k + 1) * hilbertGibbsPhysical f (k + 1) := by
    rw [real_inner_comm, inner_paretoPoint]
  have h0 : inner ℝ (paretoPointHilbert k) f =
      paretoWeight k * hilbertGibbsPhysical f k := by
    rw [real_inner_comm, inner_paretoPoint]
  rw [differenceCertificate, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, h1, h0]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (paretoWeight_pos (k + 1))),
    one_mul, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (paretoWeight_pos k)), one_mul]

private theorem point_inner (i j : ℕ) :
    inner ℝ (paretoPointHilbert i) (paretoPointHilbert j) =
      if i = j then paretoWeight j else 0 := by
  rw [inner_paretoPoint, hilbertGibbsPhysical_paretoPoint]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem differenceCertificate_norm_sq (k : ℕ) :
    ‖differenceCertificate k‖ ^ 2 = 2 * ((k : ℝ) + 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [differenceCertificate, inner_sub_left, inner_sub_right,
    real_inner_smul_left, inner_smul_right, point_inner]
  simp only [show k + 1 ≠ k by omega, show k ≠ k + 1 by omega,
    if_false, if_true, mul_zero, sub_zero, zero_sub]
  unfold paretoWeight
  push_cast
  simp only [one_div, inv_inv]
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (k : ℝ) + 1 + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact arithmetic first difference, including its signed divisibility term. -/
theorem differenceCertificate_inner_residue (k d : ℕ) (hd : 0 < d) :
    inner ℝ (differenceCertificate k) (normalizedResidueHilbert d hd) =
      1 / (d : ℝ) - divisorIndicator d (k + 2) := by
  rw [differenceCertificate_inner, hilbertGibbsPhysical_eq,
    hilbertGibbsPhysical_eq, normalizedResidueHilbert_sequence]
  have h := cumulative_succ (balancedDivisor d) (k + 1)
  rw [cumulative_balancedDivisor d (k + 1 + 1) hd,
    cumulative_balancedDivisor d (k + 1) hd] at h
  simp only [balancedDivisor] at h
  simpa only [Nat.add_assoc] using
    (show residueFraction d (k + 1 + 1) - residueFraction d (k + 1) =
      1 / (d : ℝ) - divisorIndicator d (k + 1 + 1) by linarith)

theorem differenceCertificate_inner_firstPoint (k : ℕ) (hk : 0 < k) :
    inner ℝ (differenceCertificate k) (paretoPointHilbert 0) = 0 := by
  rw [differenceCertificate_inner]
  simp [hilbertGibbsPhysical_paretoPoint, show k ≠ 0 by omega]

/-- Any integer avoiding all moduli in the finite dictionary supplies a genuine
finite feasible vector for its full-tail minimum problem. -/
theorem differenceCertificate_observation (n k : ℕ) (hk : 0 < k)
    (hrough : ∀ i : Fin n, ¬ (i.val + 2) ∣ (k + 2)) (i : Fin n) :
    inner ℝ (tailAtom i.val) (differenceCertificate k) = reciprocalSource n i := by
  rw [real_inner_comm]
  change inner ℝ (differenceCertificate k)
    (residueAtom i.val -
      (anchoredEvaluationCLM 1 (residueAtom i.val)) • paretoPointHilbert 0) = _
  rw [inner_sub_right, inner_smul_right, differenceCertificate_inner_firstPoint k hk,
    mul_zero, sub_zero]
  change inner ℝ (differenceCertificate k)
    (normalizedResidueHilbert (i.val + 2) _) = _
  rw [differenceCertificate_inner_residue]
  simp [divisorIndicator, hrough i, reciprocalSource]

/-- The actual full infinite tail capacity, bounded using a concrete rough integer.
The bound depends on the dictionary and is not a uniform-in-`n` assertion. -/
theorem tailCapacity_le_rough_certificate (n k : ℕ) (hk : 0 < k)
    (hrough : ∀ i : Fin n, ¬ (i.val + 2) ∣ (k + 2)) :
    tailCapacity n ≤ 2 * ((k : ℝ) + 2) ^ 2 := by
  calc
    tailCapacity n ≤ ‖differenceCertificate k‖ ^ 2 :=
      finiteTailCertificate_capacity_le n (differenceCertificate k)
        (differenceCertificate_observation n k hk hrough)
    _ = 2 * ((k : ℝ) + 2) ^ 2 := differenceCertificate_norm_sq k

/-- A prime beyond the last dictionary modulus is a rough integer as required. -/
theorem tailCapacity_le_prime_certificate (n k : ℕ) (hk : 0 < k)
    (hp : Nat.Prime (k + 2)) (hn : n + 1 < k + 2) :
    tailCapacity n ≤ 2 * ((k : ℝ) + 2) ^ 2 := by
  apply tailCapacity_le_rough_certificate n k hk
  intro i hdiv
  rcases hp.eq_one_or_self_of_dvd (i.val + 2) hdiv with h | h
  · omega
  · have hi := i.isLt
    omega


theorem differenceCertificate_orthogonal (k l : ℕ)
    (hsep : k + 1 < l ∨ l + 1 < k) :
    inner ℝ (differenceCertificate k) (differenceCertificate l) = 0 := by
  have h00 : k ≠ l := by omega
  have h01 : k ≠ l + 1 := by omega
  have h10 : k + 1 ≠ l := by omega
  have h11 : k + 1 ≠ l + 1 := by omega
  simp only [differenceCertificate, inner_sub_left, inner_sub_right,
    real_inner_smul_left, inner_smul_right, point_inner,
    if_neg h00, if_neg h01, if_neg h10, if_neg h11,
    mul_zero, sub_zero]

theorem differenceCertificate_sum_norm_sq (s : Finset ℕ) (a : ℕ → ℝ)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k)) :
    ‖∑ k ∈ s, a k • differenceCertificate k‖ ^ 2 =
      ∑ k ∈ s, (a k) ^ 2 * (2 * ((k : ℝ) + 2) ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  simp only [real_inner_smul_left, inner_smul_right]
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq, differenceCertificate_norm_sq]
    ring
  · intro j hj hji
    rw [differenceCertificate_orthogonal i j (hsep hi hj (Ne.symm hji))]
    simp
  · intro hnot
    exact (hnot hi).elim

def roughCertificateMass (s : Finset ℕ) : ℝ :=
  ∑ k ∈ s, 1 / (2 * ((k : ℝ) + 2) ^ 2)

theorem roughCertificateMass_pos (s : Finset ℕ) (hs : s.Nonempty) :
    0 < roughCertificateMass s := by
  apply Finset.sum_pos'
  · intro k hk
    positivity
  · obtain ⟨k, hk⟩ := hs
    exact ⟨k, hk, by positivity⟩

def averagedRoughCertificate (s : Finset ℕ) : ThresholdHilbert :=
  (roughCertificateMass s)⁻¹ •
    ∑ k ∈ s, (1 / (2 * ((k : ℝ) + 2) ^ 2)) • differenceCertificate k

theorem averagedRoughCertificate_norm_sq (s : Finset ℕ)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k))
    (hs : s.Nonempty) :
    ‖averagedRoughCertificate s‖ ^ 2 = 1 / roughCertificateMass s := by
  have hb : roughCertificateMass s ≠ 0 := ne_of_gt (roughCertificateMass_pos s hs)
  have hsum : (∑ k ∈ s,
      (1 / (2 * ((k : ℝ) + 2) ^ 2)) ^ 2 * (2 * ((k : ℝ) + 2) ^ 2)) =
      roughCertificateMass s := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : 2 * ((k : ℝ) + 2) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [averagedRoughCertificate, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    differenceCertificate_sum_norm_sq s _ hsep, hsum]
  field_simp

theorem averagedRoughCertificate_observation (n : ℕ) (s : Finset ℕ)
    (hs : s.Nonempty) (hk : ∀ k ∈ s, 0 < k)
    (hrough : ∀ k ∈ s, ∀ i : Fin n, ¬ (i.val + 2) ∣ (k + 2))
    (i : Fin n) :
    inner ℝ (tailAtom i.val) (averagedRoughCertificate s) = reciprocalSource n i := by
  have hb : roughCertificateMass s ≠ 0 := ne_of_gt (roughCertificateMass_pos s hs)
  rw [averagedRoughCertificate, inner_smul_right, inner_sum]
  simp only [inner_smul_right]
  have he : (∑ k ∈ s, 1 / (2 * ((k : ℝ) + 2) ^ 2) *
      inner ℝ (tailAtom i.val) (differenceCertificate k)) =
      roughCertificateMass s * reciprocalSource n i := by
    rw [roughCertificateMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hks
    rw [differenceCertificate_observation n k (hk k hks) (hrough k hks) i]
  rw [he, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]

/-- A finite version of the note's rough-integer reciprocal-square bound. -/
theorem tailCapacity_le_averaged_rough_certificate (n : ℕ) (s : Finset ℕ)
    (hs : s.Nonempty) (hk : ∀ k ∈ s, 0 < k)
    (hrough : ∀ k ∈ s, ∀ i : Fin n, ¬ (i.val + 2) ∣ (k + 2))
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k)) :
    tailCapacity n ≤ 1 / roughCertificateMass s := by
  calc
    tailCapacity n ≤ ‖averagedRoughCertificate s‖ ^ 2 :=
      finiteTailCertificate_capacity_le n (averagedRoughCertificate s)
        (averagedRoughCertificate_observation n s hs hk hrough)
    _ = 1 / roughCertificateMass s := averagedRoughCertificate_norm_sq s hsep hs


theorem tailCapacity_mul_roughCertificateMass_le (n : ℕ) (s : Finset ℕ)
    (hk : ∀ k ∈ s, 0 < k)
    (hrough : ∀ k ∈ s, ∀ i : Fin n, ¬ (i.val + 2) ∣ (k + 2))
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k)) :
    tailCapacity n * roughCertificateMass s ≤ 1 := by
  by_cases hs : s.Nonempty
  · exact (le_div_iff₀ (roughCertificateMass_pos s hs)).mp
      (tailCapacity_le_averaged_rough_certificate n s hs hk hrough hsep)
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he, roughCertificateMass]

theorem tailCapacity_mul_coprimeMass_le (n P : ℕ)
    (hP : ∀ i : Fin n, i.val + 2 ∣ P) :
    tailCapacity n * ((∑' p, coprimePairMass P p) / 2) ≤ 1 := by
  classical
  let s : ℕ → Finset ℕ := fun M =>
    (Finset.range M).filter (fun k => coprimePairIndex P (k + 2))
  have hfinite (M : ℕ) : tailCapacity n * roughCertificateMass (s M) ≤ 1 := by
    apply tailCapacity_mul_roughCertificateMass_le
    · intro k hk
      have hmin := (Finset.mem_filter.mp hk).2.1
      omega
    · intro k hk i hdiv
      have hcop := (Finset.mem_filter.mp hk).2.2.2
      have hdone : i.val + 2 ∣ 1 := by
        simpa only [show Nat.gcd (k + 2) P = 1 from hcop] using
          Nat.dvd_gcd hdiv (hP i)
      have he := Nat.dvd_one.mp hdone
      omega
    · intro k hk l hl hne
      have hko := (Finset.mem_filter.mp hk).2.2.1
      have hlo := (Finset.mem_filter.mp hl).2.2.1
      omega
  have hmass (M : ℕ) : roughCertificateMass (s M) =
      (∑ k ∈ Finset.range M, coprimePairMass P (k + 2)) / 2 := by
    rw [roughCertificateMass, Finset.sum_filter, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    unfold coprimePairMass
    have hk0 : (k : ℝ) + 2 ≠ 0 := by positivity
    split_ifs <;> push_cast <;> field_simp [hk0] <;> ring
  have hshift : HasSum (fun k => coprimePairMass P (k + 2))
      (∑' p, coprimePairMass P p) := by
    apply (hasSum_nat_add_iff 2).mpr
    have hz : (∑ k ∈ Finset.range 2, coprimePairMass P k) = 0 := by
      norm_num [Finset.sum_range_succ, coprimePairMass, coprimePairIndex]
    rw [hz, add_zero]
    exact (coprimePairMass_summable P).hasSum
  have hlim : Filter.Tendsto (fun M => tailCapacity n * roughCertificateMass (s M))
      Filter.atTop (nhds (tailCapacity n * ((∑' p, coprimePairMass P p) / 2))) := by
    simp_rw [hmass]
    exact tendsto_const_nhds.mul
      (hshift.tendsto_sum_nat.div_const 2)
  exact isClosed_Iic.mem_of_tendsto hlim (Filter.Eventually.of_forall hfinite)

theorem coprimePairMass_tsum_pos (P : ℕ) (hP : P ≠ 0) (h2 : 2 ∣ P) :
    0 < ∑' p, coprimePairMass P p := by
  have hPpos : 0 < P := Nat.pos_of_ne_zero hP
  have hP2 : 2 ≤ P := Nat.le_of_dvd hPpos h2
  have hc : Nat.Coprime (P + 1) P := by simp [Nat.coprime_self_add_left]
  have hodd : (P + 1) % 2 = 1 := by
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd h2]
  have hidx : coprimePairIndex P (P + 1) := ⟨by omega, hodd, hc⟩
  have hterm : 0 < coprimePairMass P (P + 1) := by
    simp only [coprimePairMass, if_pos hidx]
    positivity
  have hle : coprimePairMass P (P + 1) ≤ ∑' p, coprimePairMass P p :=
    (coprimePairMass_summable P).le_tsum (P + 1)
      (fun p hp => coprimePairMass_nonneg P p)
  exact lt_of_lt_of_le hterm hle

/-- Full reciprocal-square bound for every common support modulus. -/
theorem tailCapacity_le_coprimeMass (n P : ℕ) (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P) :
    tailCapacity n ≤ 2 / (coprimeReciprocalSquareMass P - 1) := by
  have hp := coprimePairMass_tsum_pos P hP h2
  have h := tailCapacity_mul_coprimeMass_le n P hmod
  rw [coprimeReciprocalSquareMass]
  simp only [add_sub_cancel_left]
  apply (le_div_iff₀ hp).mpr
  nlinarith

/-- The exact Euler-product expression from the Pareto note, for any nonzero
even common multiple of the dictionary moduli. -/
theorem tailCapacity_le_eulerProduct (n P : ℕ) (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P) :
    tailCapacity n ≤ 2 /
      ((Real.pi ^ 2 / 6) * ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2) - 1) := by
  rw [← coprimeReciprocalSquareMass_eulerProduct P hP h2]
  exact tailCapacity_le_coprimeMass n P hP h2 hmod

/-- Stage `n` uses moduli 2,...,n+1; their factorial is an explicit support modulus. -/
theorem tailCapacity_le_factorial_eulerProduct (n : ℕ) (hn : 0 < n) :
    tailCapacity n ≤ 2 /
      ((Real.pi ^ 2 / 6) * ∏ p ∈ (n + 1).factorial.primeFactors,
        (1 - 1 / (p : ℝ) ^ 2) - 1) := by
  apply tailCapacity_le_eulerProduct n ((n + 1).factorial)
    (Nat.factorial_ne_zero _)
  · apply Nat.dvd_factorial
    · omega
    · omega
  · intro i
    apply Nat.dvd_factorial
    · omega
    · omega

/-- Inverse-square weighting gives the same pairing with every certificate in
the chosen orthogonal family. -/
theorem averagedRoughCertificate_inner_member (s : Finset ℕ) (i : ℕ) (hi : i ∈ s)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k)) :
    inner ℝ (averagedRoughCertificate s) (differenceCertificate i) =
      1 / roughCertificateMass s := by
  rw [averagedRoughCertificate, real_inner_smul_left, sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq, differenceCertificate_norm_sq]
    have hd : 2 * ((i : ℝ) + 2) ^ 2 ≠ 0 := by positivity
    simp only [one_div, inv_mul_cancel₀ hd, mul_one]
  · intro j hj hji
    rw [differenceCertificate_orthogonal j i (hsep hj hi hji), mul_zero]
  · intro hnot
    exact (hnot hi).elim

/-- Every coefficient family of total mass one has the same inner product with
the normalized inverse-square certificate. -/
theorem averagedRoughCertificate_inner_affine (s : Finset ℕ) (a : ℕ → ℝ)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k))
    (ha : ∑ k ∈ s, a k = 1) :
    inner ℝ (averagedRoughCertificate s)
      (∑ k ∈ s, a k • differenceCertificate k) = 1 / roughCertificateMass s := by
  rw [inner_sum]
  simp only [inner_smul_right]
  calc
    (∑ k ∈ s, a k * inner ℝ (averagedRoughCertificate s) (differenceCertificate k)) =
        ∑ k ∈ s, a k * (1 / roughCertificateMass s) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [averagedRoughCertificate_inner_member s k hk hsep]
    _ = (∑ k ∈ s, a k) * (1 / roughCertificateMass s) := by
      rw [Finset.sum_mul]
    _ = 1 / roughCertificateMass s := by rw [ha, one_mul]

/-- Exact completion for every signed reweighting with total coefficient one.
The inverse-square certificate is the minimum-energy element of this affine
family; the complete excess energy is the Hilbert distance from that element. -/
theorem roughCertificate_affine_energy_completion (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s.Nonempty)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k))
    (ha : ∑ k ∈ s, a k = 1) :
    ‖∑ k ∈ s, a k • differenceCertificate k‖ ^ 2 =
      1 / roughCertificateMass s +
        ‖(∑ k ∈ s, a k • differenceCertificate k) - averagedRoughCertificate s‖ ^ 2 := by
  let f := ∑ k ∈ s, a k • differenceCertificate k
  have hright : inner ℝ (averagedRoughCertificate s) f =
      1 / roughCertificateMass s := averagedRoughCertificate_inner_affine s a hsep ha
  have hleft : inner ℝ f (averagedRoughCertificate s) =
      1 / roughCertificateMass s := by rw [real_inner_comm]; exact hright
  have hexact : ‖f - averagedRoughCertificate s‖ ^ 2 =
      ‖f‖ ^ 2 - 1 / roughCertificateMass s := by
    rw [← real_inner_self_eq_norm_sq]
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      hleft, hright, averagedRoughCertificate_norm_sq s hsep hs]
    ring
  change ‖f‖ ^ 2 = 1 / roughCertificateMass s + ‖f - averagedRoughCertificate s‖ ^ 2
  rw [hexact]
  ring

/-- No signed coefficient reweighting of this fixed orthogonal family improves
the reciprocal-mass certificate energy. -/
theorem roughCertificate_affine_energy_lower_bound (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s.Nonempty)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k))
    (ha : ∑ k ∈ s, a k = 1) :
    1 / roughCertificateMass s ≤ ‖∑ k ∈ s, a k • differenceCertificate k‖ ^ 2 := by
  rw [roughCertificate_affine_energy_completion s a hs hsep ha]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality of energy holds exactly at the inverse-square averaged vector. -/
theorem roughCertificate_affine_energy_eq_iff (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s.Nonempty)
    (hsep : (s : Set ℕ).Pairwise (fun k l => k + 1 < l ∨ l + 1 < k))
    (ha : ∑ k ∈ s, a k = 1) :
    ‖∑ k ∈ s, a k • differenceCertificate k‖ ^ 2 = 1 / roughCertificateMass s ↔
      (∑ k ∈ s, a k • differenceCertificate k) = averagedRoughCertificate s := by
  rw [roughCertificate_affine_energy_completion s a hs hsep ha]
  constructor
  · intro h
    have hz : ‖(∑ k ∈ s, a k • differenceCertificate k) -
        averagedRoughCertificate s‖ ^ 2 = 0 := by linarith
    have hn : ‖(∑ k ∈ s, a k • differenceCertificate k) -
        averagedRoughCertificate s‖ = 0 := sq_eq_zero_iff.mp hz
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · intro h
    rw [h, sub_self, norm_zero]
    ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
