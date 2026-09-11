import RiemannResearch.RH.ParetoPrimePackets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Exact Jordan coordinates of the uniform residue gcd Gram form

Source: Christian Noack, September 11, 2026, reflection-pair law of total
variance discussion. The signed incidence coordinates are taken from the
actual residue differences `dilation m (residue a)`.

This module proves the finite arithmetic diagonalization. The identification
of the gcd Gram form with actual uniform residue covariance is separate.
No approximation, all-scale bound, or RH is assumed or proved here.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The second Jordan totient, defined by its genuine Möbius formula. -/
def jordanTwo (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) * (d : ℝ) ^ 2

theorem sum_divisors_jordanTwo (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, jordanTwo d) = (n : ℝ) ^ 2 := by
  exact (mobius_inversion jordanTwo (fun n => (n : ℝ) ^ 2)).mpr
    (by intro d hd; rfl) n hn

@[simp] theorem jordanTwo_one : jordanTwo 1 = 1 := by
  simp [jordanTwo]

/-- The exact Euler-factor recurrence, including a repeated prime. -/
theorem jordanTwo_prime_mul (p q : ℕ) (hp : p.Prime) (hq : 0 < q) :
    jordanTwo (p * q) =
      if p ∣ q then (p : ℝ) ^ 2 * jordanTwo q
      else ((p : ℝ) ^ 2 - 1) * jordanTwo q := by
  rw [jordanTwo, prime_divisor_transform p q hp hq]
  have hs : (∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius (q / d) : ℝ) * ((p * d : ℕ) : ℝ) ^ 2) =
      (p : ℝ) ^ 2 * jordanTwo q := by
    rw [jordanTwo, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    push_cast
    ring
  rw [hs]
  change (p : ℝ) ^ 2 * jordanTwo q - (if p ∣ q then 0 else jordanTwo q) = _
  split_ifs <;> ring

/-- All the arithmetic penalties in the Jordan diagonal are strictly positive. -/
theorem jordanTwo_pos (n : ℕ) (hn : 0 < n) : 0 < jordanTwo n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      simp
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
    have hq : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
    have hqn : n / p < n := Nat.div_lt_self hn hp.one_lt
    have hprev : 0 < jordanTwo (n / p) := ih (n / p) hqn hq
    have he : p * (n / p) = n := Nat.mul_div_cancel' hpn
    have hrec := jordanTwo_prime_mul p (n / p) hp hq
    rw [he] at hrec
    rw [hrec]
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    split_ifs
    · exact mul_pos (sq_pos_of_pos (lt_trans zero_lt_one hpR)) hprev
    · exact mul_pos hp2 hprev

/-- Incidence of a divisor in a modulus, with values in the real numbers. -/
def divisorIncidence (m d : ℕ) : ℝ := if d ∣ m then 1 else 0

/-- Signed incidence of the legal difference `R_(am) - R_m`. -/
def seedDivisorIncidence (a m d : ℕ) : ℝ :=
  divisorIncidence (a * m) d - divisorIncidence m d

theorem dilation_residue_incidence_coordinates (a m n : ℕ) :
    dilation m (residue a) n = residue (a * m) n - residue m n := by
  simpa [Nat.mul_comm] using residue_mul_floor m a n

/-- The divisor sum of Jordan weights evaluates the exact gcd-square kernel. -/
theorem gcd_square_eq_jordan_incidence (Q L K : ℕ) (hQ : 0 < Q)
    (hL : L ∣ Q) (hK : K ∣ Q) :
    (Nat.gcd L K : ℝ) ^ 2 =
      ∑ d ∈ Q.divisors,
        jordanTwo d * divisorIncidence L d * divisorIncidence K d := by
  have hL0 : L ≠ 0 := by
    intro h
    subst L
    exact (ne_of_gt hQ) (by simpa using hL)
  have hg0 : Nat.gcd L K ≠ 0 := by
    intro h
    have hd := Nat.gcd_dvd_left L K
    rw [h, zero_dvd_iff] at hd
    exact hL0 hd
  have hset : Q.divisors.filter (fun d => d ∣ L ∧ d ∣ K) =
      (Nat.gcd L K).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdQ, hQ0⟩, hdL, hdK⟩
      exact ⟨⟨hdL, hdK⟩, hg0⟩
    · rintro ⟨⟨hdL, hdK⟩, hg⟩
      exact ⟨⟨dvd_trans hdL hL, ne_of_gt hQ⟩, hdL, hdK⟩
  calc
    _ = ∑ d ∈ (Nat.gcd L K).divisors, jordanTwo d :=
      (sum_divisors_jordanTwo _ (Nat.pos_of_ne_zero hg0)).symm
    _ = ∑ d ∈ Q.divisors.filter (fun d => d ∣ L ∧ d ∣ K), jordanTwo d := by
      rw [hset]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [divisorIncidence]
      by_cases hdl : d ∣ L <;> by_cases hdk : d ∣ K <;> simp [hdl, hdk]

/-- The actual four signed gcd terms for two legal residue differences. -/
def seedGcdCovariance (a m b n : ℕ) : ℝ :=
  ((Nat.gcd (a * m) (b * n) : ℝ) ^ 2 -
    (Nat.gcd (a * m) n : ℝ) ^ 2 -
    (Nat.gcd m (b * n) : ℝ) ^ 2 +
    (Nat.gcd m n : ℝ) ^ 2) / 12

theorem seedGcdCovariance_eq_jordan (Q a m b n : ℕ) (hQ : 0 < Q)
    (ham : a * m ∣ Q) (hm : m ∣ Q) (hbn : b * n ∣ Q) (hn : n ∣ Q) :
    seedGcdCovariance a m b n =
      (∑ d ∈ Q.divisors,
        jordanTwo d * seedDivisorIncidence a m d *
          seedDivisorIncidence b n d) / 12 := by
  unfold seedGcdCovariance
  rw [gcd_square_eq_jordan_incidence Q (a * m) (b * n) hQ ham hbn,
    gcd_square_eq_jordan_incidence Q (a * m) n hQ ham hn,
    gcd_square_eq_jordan_incidence Q m (b * n) hQ hm hbn,
    gcd_square_eq_jordan_incidence Q m n hQ hm hn]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  unfold seedDivisorIncidence
  ring

/-- Exchange every finite signed mixed term before taking the final squares. -/
theorem finite_gram_diagonal {ι κ : Type*} (s : Finset ι) (D : Finset κ)
    (c : ι → ℝ) (w : κ → ℝ) (h : ι → κ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j *
      (∑ d ∈ D, w d * h i d * h j d)) =
      ∑ d ∈ D, w d * (∑ i ∈ s, c i * h i d) ^ 2 := by
  classical
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ d ∈ D,
        w d * (c i * h i d) * (c j * h j d) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∑ i ∈ s, ∑ d ∈ D, ∑ j ∈ s,
        w d * (c i * h i d) * (c j * h j d) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, ∑ i ∈ s, ∑ j ∈ s,
        w d * (c i * h i d) * (c j * h j d) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The legal packet's signed divisibility coordinate `H_d`. -/
def legalPacketDivisorCoordinate {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a m : ι → ℕ) (d : ℕ) : ℝ :=
  ∑ i ∈ s, c i * seedDivisorIncidence (a i) (m i) d

/-- Exact Jordan diagonalization, with all signed cross terms retained. -/
theorem legalPacket_gcd_energy_eq_jordan {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a m : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hperiod : ∀ i ∈ s, a i * m i ∣ Q)
    (hscale : ∀ i ∈ s, m i ∣ Q) :
    (∑ i ∈ s, ∑ j ∈ s,
      c i * c j * seedGcdCovariance (a i) (m i) (a j) (m j)) =
      (∑ d ∈ Q.divisors,
        jordanTwo d * legalPacketDivisorCoordinate s c a m d ^ 2) / 12 := by
  classical
  calc
    _ = (∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (∑ d ∈ Q.divisors, jordanTwo d *
          seedDivisorIncidence (a i) (m i) d *
          seedDivisorIncidence (a j) (m j) d)) / 12 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [seedGcdCovariance_eq_jordan Q _ _ _ _ hQ
        (hperiod i hi) (hscale i hi) (hperiod j hj) (hscale j hj)]
      ring
    _ = _ := by
      rw [finite_gram_diagonal]
      rfl

/-- Positivity follows only after the signed mixed terms have been regrouped. -/
theorem legalPacket_gcd_energy_nonneg {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a m : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hperiod : ∀ i ∈ s, a i * m i ∣ Q)
    (hscale : ∀ i ∈ s, m i ∣ Q) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      c i * c j * seedGcdCovariance (a i) (m i) (a j) (m j) := by
  rw [legalPacket_gcd_energy_eq_jordan s c a m Q hQ hperiod hscale]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (jordanTwo_pos d (Nat.pos_of_mem_divisors hd)).le (sq_nonneg _)
  · norm_num

end
end RiemannResearch.RH.Pareto
