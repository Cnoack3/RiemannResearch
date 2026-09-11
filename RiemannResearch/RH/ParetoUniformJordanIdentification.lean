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

end
end RiemannResearch.RH.Pareto
