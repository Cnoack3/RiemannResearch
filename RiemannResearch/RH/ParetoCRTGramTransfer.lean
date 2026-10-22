import RiemannResearch.RH.ParetoExactHeadCRT
import RiemannResearch.RH.ParetoResidueUniformCovariance
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.ParetoLegalStructure

/-!
# Exact Pareto transfer and uniform packet-tail control

Source: user-provided CLT/Gram and Pareto/Green program, 23 September 2026.
The results below are constructive finite/infinite-sum identities and bounds.
They do not replace the actual Pareto residue weights by uniform weights.

The first theorem transfers the uniform CRT covariance to the genuine Pareto
inner product with an exact signed correction. The second group gives a
coefficient-explicit Green-tail bound, uniform even when the finite support,
conductors, and coefficients vary with the cutoff.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The residue coordinate centered for the uniform law on one period. -/
def centeredResidue (q k : ℕ) : ℝ :=
  residue q k - ((q : ℝ) - 1) / 2

theorem centeredResidue_abs_le (q k : ℕ) (hq : 0 < q) :
    |centeredResidue q k| ≤ (q : ℝ) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr0 : 0 ≤ residue q k := by
    unfold residue
    positivity
  have hrq : residue q k ≤ (q : ℝ) := by
    simpa only [abs_of_nonneg hr0] using residue_abs_le q k hq
  rw [abs_le]
  constructor <;> dsimp [centeredResidue] <;> linarith

theorem centeredResidue_period_of_dvd {q Q : ℕ} (hQ : q ∣ Q) (k : ℕ) :
    centeredResidue q (k + Q) = centeredResidue q k := by
  unfold centeredResidue
  rw [residue_period_of_dvd hQ]

private theorem sum_fin_positive (Q : ℕ) (f : ℕ → ℝ) :
    (∑ r : Fin Q, f (r.val + 1)) = ∑ k ∈ Finset.Ico 1 (Q + 1), f k := by
  classical
  refine Finset.sum_bij (fun r _ => r.val + 1) ?_ ?_ ?_ ?_
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
    refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega
  · intro r _
    rfl

/-- The positive representatives 1,...,Q have the same uniform centered
covariance as the representatives 0,...,Q-1. -/
theorem centeredResidue_uniform_covariance_positive
    (L K Q : ℕ) (hL : 0 < L) (hK : 0 < K) (hQ : 0 < Q)
    (hLQ : L ∣ Q) (hKQ : K ∣ Q) :
    (1 / (Q : ℝ)) *
        (∑ r : Fin Q,
          centeredResidue L (r.val + 1) * centeredResidue K (r.val + 1)) =
      ((Nat.gcd L K : ℝ) ^ 2 - 1) / 12 := by
  let f : ℕ → ℝ := fun n => centeredResidue L n * centeredResidue K n
  have hfQ : f Q = f 0 := by
    dsimp [f]
    rw [show Q = 0 + Q by omega,
      centeredResidue_period_of_dvd hLQ 0,
      centeredResidue_period_of_dvd hKQ 0]
  have hshift :
      (∑ r : Fin Q, f (r.val + 1)) = ∑ n ∈ Finset.range Q, f n := by
    rw [sum_fin_positive, Finset.sum_Ico_eq_sub _ (by omega),
      Finset.sum_range_succ, Finset.sum_range_one, hfQ]
    ring
  have hcov := residue_uniform_covariance L K Q hL hK hQ hLQ hKQ
  rw [show (∑ r : Fin Q,
      centeredResidue L (r.val + 1) * centeredResidue K (r.val + 1)) =
      ∑ r : Fin Q, f (r.val + 1) by rfl, hshift]
  simpa [f, centeredResidue, div_eq_mul_inv, mul_comm] using hcov

/-- Exact transfer of the uniform CRT covariance to the genuine Pareto Gram
entry. The second finite sum is the complete, signed nonuniformity correction. -/
theorem centeredResidue_paretoInner_eq_uniform_add_defect
    (L K Q : ℕ) (hL : 0 < L) (hK : 0 < K) (hQ : 0 < Q)
    (hLQ : L ∣ Q) (hKQ : K ∣ Q) :
    paretoInner (centeredResidue L) (centeredResidue K) =
      ((Nat.gcd L K : ℝ) ^ 2 - 1) / 12 +
        ∑ r : Fin Q, ExactHeadCRT.uniformDefect Q (r.val + 1) *
          (centeredResidue L (r.val + 1) *
            centeredResidue K (r.val + 1)) := by
  calc
    _ = (1 / (Q : ℝ)) *
          (∑ r : Fin Q,
            centeredResidue L (r.val + 1) * centeredResidue K (r.val + 1)) +
        ∑ r : Fin Q, ExactHeadCRT.uniformDefect Q (r.val + 1) *
          (centeredResidue L (r.val + 1) *
            centeredResidue K (r.val + 1)) := by
      exact ExactHeadCRT.mixed_uniform_defect Q hQ _ _
        (centeredResidue_abs_le L · hL)
        (centeredResidue_abs_le K · hK)
        (centeredResidue_period_of_dvd hLQ)
        (centeredResidue_period_of_dvd hKQ)
    _ = _ := by
      rw [centeredResidue_uniform_covariance_positive L K Q hL hK hQ hLQ hKQ]

/-- Total variation scale of the genuine Pareto residue weights relative to
the uniform law. -/
def uniformDefectL1 (Q : ℕ) : ℝ :=
  ∑ r : Fin Q, |ExactHeadCRT.uniformDefect Q (r.val + 1)|

/-- Quantitative form of the exact CRT-to-Pareto transfer. No claim is made
that this defect tends to zero as the modulus grows. -/
theorem centeredResidue_paretoInner_error_abs_le
    (L K Q : ℕ) (hL : 0 < L) (hK : 0 < K) (hQ : 0 < Q)
    (hLQ : L ∣ Q) (hKQ : K ∣ Q) :
    |paretoInner (centeredResidue L) (centeredResidue K) -
        ((Nat.gcd L K : ℝ) ^ 2 - 1) / 12| ≤
      uniformDefectL1 Q * ((L : ℝ) * (K : ℝ)) := by
  rw [centeredResidue_paretoInner_eq_uniform_add_defect
    L K Q hL hK hQ hLQ hKQ]
  have hsum :
      |∑ r : Fin Q, ExactHeadCRT.uniformDefect Q (r.val + 1) *
          (centeredResidue L (r.val + 1) * centeredResidue K (r.val + 1))| ≤
        ∑ r : Fin Q, |ExactHeadCRT.uniformDefect Q (r.val + 1)| *
          ((L : ℝ) * (K : ℝ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro r hr
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (bounded_product (centeredResidue_abs_le L · hL)
        (centeredResidue_abs_le K · hK) (r.val + 1))
      (abs_nonneg _)
  simpa only [add_sub_cancel_left, uniformDefectL1, Finset.sum_mul] using hsum

/-- The complete Pareto tail after the finite head through N. -/
def paretoInnerTail (N : ℕ) (F G : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, positiveWeight (k + (N + 1)) *
    (F (k + (N + 1)) * G (k + (N + 1)))

/-- An explicit tail estimate with no fixed-function hypothesis hidden in the
constant. -/
theorem paretoInnerTail_abs_le (N : ℕ) {F G : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D) :
    |paretoInnerTail N F G| ≤ C * D / ((N : ℝ) + 1) := by
  have hs : Summable (fun k : ℕ => positiveWeight (k + (N + 1)) *
      (F (k + (N + 1)) * G (k + (N + 1)))) :=
    (summable_nat_add_iff (N + 1)).mpr
      (weighted_summable_of_bounded (bounded_product hF hG))
  have hw : Summable (fun k : ℕ => positiveWeight (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr positiveWeight_summable
  have hb (k : ℕ) :
      |positiveWeight (k + (N + 1)) *
          (F (k + (N + 1)) * G (k + (N + 1)))| ≤
        positiveWeight (k + (N + 1)) * (C * D) := by
    rw [abs_mul, abs_of_nonneg (positiveWeight_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (bounded_product hF hG (k + (N + 1))) (positiveWeight_nonneg _)
  unfold paretoInnerTail
  calc
    _ ≤ ∑' k : ℕ, |positiveWeight (k + (N + 1)) *
        (F (k + (N + 1)) * G (k + (N + 1)))| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, positiveWeight (k + (N + 1)) * (C * D) :=
      hs.abs.tsum_le_tsum hb (hw.mul_right _)
    _ = _ := by
      rw [hw.tsum_mul_right, positiveWeight_tail_tsum (N + 1) (by omega)]
      push_cast
      ring

/-- The visible coefficient envelope controlling a finite packet combination. -/
def packetCoefficientEnvelope (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ q ∈ s, |a q| *
    (∑ d ∈ q.divisors,
      |(ArithmeticFunction.moebius (q / d) : ℝ)| * (d : ℝ))

theorem packetCombination_abs_le_envelope
    (s : Finset ℕ) (a : ℕ → ℝ) (k : ℕ) :
    |∑ q ∈ s, a q * ramanujanPacket q k| ≤
      packetCoefficientEnvelope s a := by
  unfold packetCoefficientEnvelope
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro q hq
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (ramanujanPacket_abs_le q k) (abs_nonneg _)

/-- Coefficient-explicit control for arbitrary growing packet families. -/
theorem packetCombination_tail_abs_le
    (s t : Finset ℕ) (a b : ℕ → ℝ) (N : ℕ) :
    |paretoInnerTail N
        (fun k => ∑ q ∈ s, a q * ramanujanPacket q k)
        (fun k => ∑ q ∈ t, b q * ramanujanPacket q k)| ≤
      packetCoefficientEnvelope s a * packetCoefficientEnvelope t b /
        ((N : ℝ) + 1) := by
  exact paretoInnerTail_abs_le N
    (packetCombination_abs_le_envelope s a)
    (packetCombination_abs_le_envelope t b)

/-- The finite anchored-Green Gram approximates the genuine Pareto Gram with
the same explicit error, uniformly in support size and conductor size. -/
theorem packetCombination_green_gram_error_le
    (s t : Finset ℕ) (a b : ℕ → ℝ) (N : ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) :
    |paretoInner (fun k => ∑ q ∈ s, a q * ramanujanPacket q k)
        (fun k => ∑ q ∈ t, b q * ramanujanPacket q k) -
      (∑ m ∈ Finset.Ico 1 (N + 1), ∑ n ∈ Finset.Ico 1 (N + 1),
        (∑ q ∈ s, a q * ramanujanSum q m) *
          (∑ q ∈ t, b q * ramanujanSum q n) * anchoredGreen N m n)| ≤
      packetCoefficientEnvelope s a * packetCoefficientEnvelope t b /
        ((N : ℝ) + 1) := by
  rw [packetCombination_green_gram_with_tail s t a b N hs ht,
    add_sub_cancel_left]
  exact packetCombination_tail_abs_le s t a b N

/-- A single constructive hypothesis controls changing dimensions,
conductors, and coefficients: the product envelope must be little-o of the
cutoff. -/
theorem packetCombination_tail_tendsto_zero
    (s t : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (hEnvelope : Tendsto
      (fun N => packetCoefficientEnvelope (s N) (a N) *
        packetCoefficientEnvelope (t N) (b N) / ((N : ℝ) + 1))
      atTop (𝓝 0)) :
    Tendsto
      (fun N => paretoInnerTail N
        (fun k => ∑ q ∈ s N, a N q * ramanujanPacket q k)
        (fun k => ∑ q ∈ t N, b N q * ramanujanPacket q k))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm _ hEnvelope
  intro N
  rw [Real.norm_eq_abs]
  exact packetCombination_tail_abs_le (s N) (t N) (a N) (b N) N

end
end RiemannResearch.RH.Pareto
