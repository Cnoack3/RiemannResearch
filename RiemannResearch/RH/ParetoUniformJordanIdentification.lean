import RiemannResearch.RH.ParetoUniformJordanVariance
import RiemannResearch.RH.ParetoResidueUniformCovariance
import RiemannResearch.RH.ParetoReflectionVariance

/-!
# Actual uniform variance equals the signed Jordan divisor energy

Source: Christian Noack, September 11, 2026, reflection-pair total variance.
This is the bridge from the actual legal generator values to the arithmetic
diagonal; it assumes only positive seeds, positive scales, and a common period.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def divisorLegalPacket {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a m : ι → ℕ) (n : ℕ) : ℝ :=
  ∑ i ∈ s, c i * dilation (m i) (residue (a i)) n

/-- Real subtraction is intentional: the center has no truncated natural subtraction. -/
def divisorLegalPacketReflectionConstant {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a m : ι → ℕ) : ℝ :=
  ∑ i ∈ s, c i * (((a i * m i : ℕ) : ℝ) - (m i : ℝ))

theorem divisorLegalPacket_centered {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a m : ι → ℕ) (n : ℕ) :
    divisorLegalPacket s c a m n - divisorLegalPacketReflectionConstant s c a m / 2 =
      ∑ i ∈ s, c i * (dilation (m i) (residue (a i)) n -
        (((a i * m i : ℕ) : ℝ) - (m i : ℝ)) / 2) := by
  unfold divisorLegalPacket divisorLegalPacketReflectionConstant
  calc
    _ = (∑ i ∈ s, c i * dilation (m i) (residue (a i)) n) -
        ∑ i ∈ s, c i * ((((a i * m i : ℕ) : ℝ) - (m i : ℝ)) / 2) := by
      congr 1
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem dilation_residue_uniform_centered (a m n : ℕ) :
    dilation m (residue a) n - (((a * m : ℕ) : ℝ) - (m : ℝ)) / 2 =
      (residue (a * m) n - (((a * m : ℕ) : ℝ) - 1) / 2) -
        (residue m n - ((m : ℝ) - 1) / 2) := by
  rw [dilation_residue_incidence_coordinates]
  ring

/-- The uniform covariance of the actual legal generators has the four gcd terms. -/
theorem legal_seed_uniform_covariance_sum (a m b k Q : ℕ)
    (ha : 0 < a) (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    (ham : a * m ∣ Q) (hmQ : m ∣ Q) (hbk : b * k ∣ Q) (hkQ : k ∣ Q) :
    (∑ n ∈ Finset.range Q,
      (dilation m (residue a) n - (((a * m : ℕ) : ℝ) - (m : ℝ)) / 2) *
      (dilation k (residue b) n - (((b * k : ℕ) : ℝ) - (k : ℝ)) / 2)) =
        (Q : ℝ) * seedGcdCovariance a m b k := by
  let R : ℕ → ℕ → ℝ := fun L n => residue L n - ((L : ℝ) - 1) / 2
  have hpoint (n : ℕ) :
      (dilation m (residue a) n - (((a * m : ℕ) : ℝ) - (m : ℝ)) / 2) *
      (dilation k (residue b) n - (((b * k : ℕ) : ℝ) - (k : ℝ)) / 2) =
        R (a * m) n * R (b * k) n - R (a * m) n * R k n -
          R m n * R (b * k) n + R m n * R k n := by
    rw [dilation_residue_uniform_centered, dilation_residue_uniform_centered]
    dsimp [R]
    ring
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  dsimp [R]
  rw [residue_uniform_covariance_sum (a * m) (b * k) Q
      (Nat.mul_pos ha hm) (Nat.mul_pos hb hk) ham hbk,
    residue_uniform_covariance_sum (a * m) k Q (Nat.mul_pos ha hm) hk ham hkQ,
    residue_uniform_covariance_sum m (b * k) Q hm (Nat.mul_pos hb hk) hmQ hbk,
    residue_uniform_covariance_sum m k Q hm hk hmQ hkQ]
  unfold seedGcdCovariance
  ring

/-- Actual uniform full-period variance, expressed in the signed divisor coordinates. -/
theorem uniformReflectionVariance_divisorLegalPacket {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (a m : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ Q)
    (hscale : ∀ i ∈ s, m i ∣ Q) :
    uniformReflectionVariance Q (divisorLegalPacket s c a m)
      (divisorLegalPacketReflectionConstant s c a m) =
        (∑ d ∈ Q.divisors,
          jordanTwo d * legalPacketDivisorCoordinate s c a m d ^ 2) / 12 := by
  classical
  let e : ι → ℕ → ℝ := fun i n => dilation (m i) (residue (a i)) n -
    (((a i * m i : ℕ) : ℝ) - (m i : ℝ)) / 2
  have hs : (∑ n ∈ Finset.range Q, (∑ i ∈ s, c i * e i n) ^ 2) =
      (Q : ℝ) * (∑ i ∈ s, ∑ j ∈ s,
        c i * c j * seedGcdCovariance (a i) (m i) (a j) (m j)) := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, c i * c j *
          (∑ n ∈ Finset.range Q, e i n * e j n) := by
        simpa only [one_mul] using
          (finite_gram_diagonal s (Finset.range Q) c (fun _ => 1) e).symm
      _ = ∑ i ∈ s, ∑ j ∈ s, c i * c j *
          ((Q : ℝ) * seedGcdCovariance (a i) (m i) (a j) (m j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (∑ n ∈ Finset.range Q, e i n * e j n) =
            (Q : ℝ) * seedGcdCovariance (a i) (m i) (a j) (m j) from
          legal_seed_uniform_covariance_sum _ _ _ _ Q (ha i hi) (hm i hi)
            (ha j hj) (hm j hj) (hperiod i hi) (hscale i hi)
            (hperiod j hj) (hscale j hj)]
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  unfold uniformReflectionVariance
  simp_rw [divisorLegalPacket_centered]
  change (∑ r : Fin Q, (∑ i ∈ s, c i * e i r.val) ^ 2) / (Q : ℝ) = _
  rw [Fin.sum_univ_eq_sum_range (fun n => (∑ i ∈ s, c i * e i n) ^ 2) Q]
  change (∑ n ∈ Finset.range Q, (∑ i ∈ s, c i * e i n) ^ 2) / (Q : ℝ) = _
  rw [hs]
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hQ0]
  exact legalPacket_gcd_energy_eq_jordan s c a m Q hQ hperiod hscale

/-!
## Centered raw residue combinations and the actual Mobius cutoff

Source: user-provided RH_Centered_Far_Tail_and_Subpower_Obstruction_2026-09-24(1).md,
Part I, Sections 2--3, for the centered Mobius variance identity.
The proof extends the legal-packet identification above to arbitrary centered
residue combinations, removes the constant Jordan coordinate, and proves that
the actual Mobius coordinates vanish beyond the arithmetic cutoff. It uses the
existing CRT and Mobius-inversion proofs, not a uniform-to-Pareto substitution.
No arithmetic cancellation, large-sieve estimate, or RH hypothesis is assumed.
-/


theorem gcd_square_sub_one_eq_jordan_incidence (Q L K : ℕ) (hQ : 0 < Q)
    (hL : L ∣ Q) (hK : K ∣ Q) :
    (Nat.gcd L K : ℝ)^2 - 1 =
      ∑ d ∈ Q.divisors.erase 1,
        jordanTwo d * divisorIncidence L d * divisorIncidence K d := by
  have h1 : 1 ∈ Q.divisors := Nat.mem_divisors.mpr ⟨one_dvd Q, hQ.ne'⟩
  have he := Finset.sum_erase_add Q.divisors
    (fun d => jordanTwo d * divisorIncidence L d * divisorIncidence K d) h1
  rw [← gcd_square_eq_jordan_incidence Q L K hQ hL hK] at he
  simp only [jordanTwo_one, divisorIncidence, one_dvd, if_true, mul_one] at he ⊢
  linarith

theorem centeredResidue_uniform_variance_eq_jordan {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ)
    (Q : ℕ) (hQ : 0 < Q) (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, m i ∣ Q) :
    (∑ n ∈ Finset.range Q,
      (∑ i ∈ s, c i * (residue (m i) n - ((m i : ℝ)-1)/2))^2) / (Q : ℝ) =
    (∑ d ∈ Q.divisors.erase 1,
      jordanTwo d * (∑ i ∈ s, c i * divisorIncidence (m i) d)^2) / 12 := by
  classical
  let h : ι → ℕ → ℝ := fun i n => residue (m i) n - ((m i : ℝ)-1)/2
  have hsum :
      (∑ n ∈ Finset.range Q, (∑ i ∈ s, c i * h i n)^2) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (∑ n ∈ Finset.range Q, h i n * h j n) := by
    simpa only [one_mul] using
      (finite_gram_diagonal s (Finset.range Q) c (fun _ => 1) h).symm
  have hc (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      (∑ n ∈ Finset.range Q, h i n * h j n) =
      (Q : ℝ) * (∑ d ∈ Q.divisors.erase 1,
        jordanTwo d * divisorIncidence (m i) d * divisorIncidence (m j) d) / 12 := by
    dsimp [h]
    rw [residue_uniform_covariance_sum (m i) (m j) Q
      (hm i hi) (hm j hj) (hperiod i hi) (hperiod j hj),
      gcd_square_sub_one_eq_jordan_incidence Q (m i) (m j) hQ
        (hperiod i hi) (hperiod j hj)]
  change (∑ n ∈ Finset.range Q, (∑ i ∈ s, c i * h i n)^2) / (Q : ℝ) = _
  rw [hsum]
  have he :
      (∑ i ∈ s, ∑ j ∈ s, c i * c j * (∑ n ∈ Finset.range Q, h i n * h j n)) =
      (Q : ℝ)/12 * (∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (∑ d ∈ Q.divisors.erase 1,
          jordanTwo d * divisorIncidence (m i) d * divisorIncidence (m j) d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hc i hi j hj]
    ring
  rw [he, finite_gram_diagonal]
  have hQR : (Q : ℝ) ≠ 0 := by positivity
  field_simp

theorem centeredMobius_uniform_variance_eq_jordan
    (N Q : ℕ) (hQ : 0 < Q)
    (hperiod : ∀ d ∈ Finset.Icc 1 N, d ∣ Q) :
    (∑ n ∈ Finset.range Q,
      (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) *
        (residue d n - ((d : ℝ)-1)/2))^2) / (Q : ℝ) =
    (∑ q ∈ Q.divisors.erase 1, jordanTwo q *
      (∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) * divisorIncidence d q)^2) / 12 :=
  centeredResidue_uniform_variance_eq_jordan (Finset.Icc 1 N)
    (fun d => (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) id Q hQ
    (fun _d hd => (Finset.mem_Icc.mp hd).1) hperiod


/-- The Jordan coordinates outside the original arithmetic cutoff vanish exactly. -/
theorem centeredMobius_uniform_variance_finite_cutoff
    (N Q : ℕ) (hQ : 0 < Q)
    (hperiod : ∀ d ∈ Finset.Icc 1 N, d ∣ Q) :
    (∑ n ∈ Finset.range Q,
      (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) *
        (residue d n - ((d : ℝ)-1)/2))^2) / (Q : ℝ) =
    (∑ q ∈ Finset.Icc 2 N, jordanTwo q *
      (∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) * divisorIncidence d q)^2) / 12 := by
  rw [centeredMobius_uniform_variance_eq_jordan N Q hQ hperiod]
  congr 1
  symm
  apply Finset.sum_subset
  · intro q hq
    have hq' := Finset.mem_Icc.mp hq
    exact Finset.mem_erase.mpr ⟨by omega,
      Nat.mem_divisors.mpr ⟨hperiod q (Finset.mem_Icc.mpr ⟨by omega, hq'.2⟩), hQ.ne'⟩⟩
  · intro q hq hnot
    have hq1 : q ≠ 1 := (Finset.mem_erase.mp hq).1
    have hq0 : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hq).2
    have hNq : N < q := by
      have : ¬ (2 ≤ q ∧ q ≤ N) := by simpa only [Finset.mem_Icc] using hnot
      omega
    have hz : (∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) * divisorIncidence d q) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hd' := Finset.mem_Icc.mp hd
      have hnd : ¬ q ∣ d := by
        intro hqd
        have := Nat.le_of_dvd (by omega : 0 < d) hqd
        omega
      simp [divisorIncidence, hnd]
    rw [hz]
    ring

/-- A completely unconditional common-period formula for the actual Mobius coefficients. -/
theorem centeredMobius_factorial_variance_eq_jordan (N : ℕ) :
    (∑ n ∈ Finset.range N.factorial,
      (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) *
        (residue d n - ((d : ℝ)-1)/2))^2) / (N.factorial : ℝ) =
    (∑ q ∈ Finset.Icc 2 N, jordanTwo q *
      (∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) * divisorIncidence d q)^2) / 12 := by
  apply centeredMobius_uniform_variance_finite_cutoff N N.factorial (Nat.factorial_pos N)
  intro d hd
  exact Nat.dvd_factorial (by have := (Finset.mem_Icc.mp hd).1; omega)
    (Finset.mem_Icc.mp hd).2

/-!
## Moving divisor coordinates in the top half of the cutoff

Source: direct divisibility calculation for the user's directed RH attempt,
September 24, 2026. If q<=N<2q, the sole multiple of q in 1,...,N is q.
The actual coefficient is therefore mu(q)/q, with no cancellation hypothesis.
The variance lower bound concerns the uniform period only; it is not a
lower or upper estimate for the weighted Pareto middle window.
-/

theorem divisorCoordinate_eq_single_of_top_half
    (c : ℕ → ℝ) (N q : ℕ) (hq : 0 < q) (hqN : q ≤ N)
    (hhalf : N < 2 * q) :
    (∑ d ∈ Finset.Icc 1 N, c d * divisorIncidence d q) = c q := by
  classical
  rw [Finset.sum_eq_single q]
  · simp [divisorIncidence]
  · intro d hd hdq
    have hnot : ¬ q ∣ d := by
      intro hqd
      rcases hqd with ⟨k, rfl⟩
      have hk : 2 ≤ k := by
        by_contra h
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl <;> simp_all
      have hdN := (Finset.mem_Icc.mp hd).2
      have hmul : q * 2 ≤ q * k := Nat.mul_le_mul_left q hk
      omega
    simp [divisorIncidence, hnot]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨hq, hqN⟩)).elim

theorem centeredMobius_divisorCoordinate_eq_top_half
    (N q : ℕ) (hq : 0 < q) (hqN : q ≤ N) (hhalf : N < 2 * q) :
    (∑ d ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) * divisorIncidence d q) =
        (ArithmeticFunction.moebius q : ℝ)/(q : ℝ) :=
  divisorCoordinate_eq_single_of_top_half
    (fun d => (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) N q hq hqN hhalf

theorem centeredMobius_factorial_variance_ge_top_half
    (N : ℕ) (hN : 2 ≤ N) :
    (∑ q ∈ Finset.Icc (N / 2 + 1) N,
      jordanTwo q * ((ArithmeticFunction.moebius q : ℝ)/(q : ℝ))^2) / 12 ≤
    (∑ n ∈ Finset.range N.factorial,
      (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) *
        (residue d n - ((d : ℝ)-1)/2))^2) / (N.factorial : ℝ) := by
  rw [centeredMobius_factorial_variance_eq_jordan]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12)
  calc
    _ = ∑ q ∈ Finset.Icc (N / 2 + 1) N, jordanTwo q *
        (∑ d ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) * divisorIncidence d q)^2 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq' := Finset.mem_Icc.mp hq
      rw [centeredMobius_divisorCoordinate_eq_top_half N q
        (by omega) hq'.2 (by omega)]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have hq' := Finset.mem_Icc.mp hq
        exact Finset.mem_Icc.mpr ⟨by omega, hq'.2⟩
      · intro q hq _
        exact mul_nonneg (jordanTwo_pos q
          (by have := (Finset.mem_Icc.mp hq).1; omega)).le (sq_nonneg _)

end
end RiemannResearch.RH.Pareto
