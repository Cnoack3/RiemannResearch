import RiemannResearch.RH.ParetoNewPacketCovariance
import RiemannResearch.RH.ParetoConductorHilbert
import RiemannResearch.LinearAlgebra.ConditionalSchurDecomposition

/-!
# Actual Pareto conductor innovation covariance is positive definite

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`, §3.
The conditional means here use the genuine full periodized Pareto weights
and the concrete quotient map on positive representatives.  No Fourier support
or conditional-orthogonality hypothesis is assumed.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
open RiemannResearch.LinearAlgebra.ConditionalSchur
noncomputable section

/-- The exact finite quotient average, extended to an old-periodic sequence.
Positive coordinates use their representative in `1,...,N`. -/
def conductorMeanSequence (N b : ℕ) (hN : 0 < N) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  conductorQuotientMean N b hN f ⟨(k + (N - 1)) % N, Nat.mod_lt _ hN⟩

theorem conductorMeanSequence_periodic (N b : ℕ) (hN : 0 < N)
    (f : ℕ → ℝ) (k : ℕ) :
    conductorMeanSequence N b hN f (k + N) = conductorMeanSequence N b hN f k := by
  unfold conductorMeanSequence
  congr 1
  apply Fin.ext
  dsimp
  rw [show k + N + (N - 1) = (k + (N - 1)) + N by omega]
  simp [Nat.add_mod]

/-- At every fine positive representative this is exactly the finite
conditional average, not an independently specified coarse function. -/
theorem conductorMeanSequence_sample (N b : ℕ) (hN : 0 < N)
    (f : ℕ → ℝ) (i : Fin (N * b)) :
    conductorMeanSequence N b hN f (i.val + 1) =
      conductorQuotientMean N b hN f (conductorQuotient N b hN i) := by
  unfold conductorMeanSequence
  congr 1
  apply Fin.ext
  dsimp [conductorQuotient]
  rw [show i.val + 1 + (N - 1) = i.val + N by omega]
  simp [Nat.add_mod]

theorem conductorMeanSequence_abs_le (N b : ℕ) (hN : 0 < N)
    (f : ℕ → ℝ) (k : ℕ) :
    |conductorMeanSequence N b hN f k| ≤
      ∑ r : Fin N, |conductorQuotientMean N b hN f r| := by
  unfold conductorMeanSequence
  exact Finset.single_le_sum (fun r _ => abs_nonneg (conductorQuotientMean N b hN f r))
    (Finset.mem_univ (⟨(k + (N - 1)) % N, Nat.mod_lt _ hN⟩ : Fin N))

/-- The sequence innovation is exactly the Hilbert fluctuation against the
entire coarse periodic space. -/
theorem conductorHilbert_innovation (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (f : ℕ → ℝ) :
    fluctuation (coarseSpace (conductorQuotient N b hN) (conductorFineWeight N b))
      (conductorHilbert N b f) =
    conductorHilbert N b (fun k => f k - conductorMeanSequence N b hN f k) := by
  unfold fluctuation
  rw [← conductorHilbert_mean_eq_projection N b hN hb f]
  unfold conductorHilbert
  rw [← map_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply, conductorSample, Function.comp_apply,
    conductorMeanSequence_sample]

/-- Full infinite Pareto Gram entries of the actual conditional innovations.
All off-diagonal entries are retained. -/
def conductorInnovationCovariance (N b : ℕ) (hN : 0 < N) (q r : ℕ) : ℝ :=
  paretoInner
    (fun k => ramanujanPacket q k - conductorMeanSequence N b hN (ramanujanPacket q) k)
    (fun k => ramanujanPacket r k - conductorMeanSequence N b hN (ramanujanPacket r) k)

/-- Every full arithmetic covariance entry equals its actual finite Hilbert
fluctuation Gram entry, retaining both the tail and every mixed entry. -/
theorem conductorInnovationCovariance_eq_fluctuation_inner (N b : ℕ)
    (hN : 0 < N) (hb : 0 < b) (q r : ℕ) (hq : q ∣ N * b) (hr : r ∣ N * b) :
    inner ℝ
      (fluctuation (coarseSpace (conductorQuotient N b hN) (conductorFineWeight N b))
        (conductorHilbert N b (ramanujanPacket q)))
      (fluctuation (coarseSpace (conductorQuotient N b hN) (conductorFineWeight N b))
        (conductorHilbert N b (ramanujanPacket r))) =
      conductorInnovationCovariance N b hN q r := by
  rw [conductorHilbert_innovation N b hN hb, conductorHilbert_innovation N b hN hb]
  apply conductorHilbert_inner N b hN hb
  · exact bounded_sub (ramanujanPacket_abs_le q)
      (conductorMeanSequence_abs_le N b hN (ramanujanPacket q))
  · exact bounded_sub (ramanujanPacket_abs_le r)
      (conductorMeanSequence_abs_le N b hN (ramanujanPacket r))
  · intro k
    rw [ramanujanPacket_period_of_dvd q (N * b) hq k,
      periodic_add_mul N (conductorMeanSequence N b hN (ramanujanPacket q))
        (conductorMeanSequence_periodic N b hN (ramanujanPacket q)) k b]
  · intro k
    rw [ramanujanPacket_period_of_dvd r (N * b) hr k,
      periodic_add_mul N (conductorMeanSequence N b hN (ramanujanPacket r))
        (conductorMeanSequence_periodic N b hN (ramanujanPacket r)) k b]

/-- Strict positive definiteness of the actual new-packet covariance for
`Q → pQ`, including repeated primes.  This is a pointwise-in-conductor result,
not a uniform coercivity estimate. -/
theorem conductorInnovationCovariance_pos (p Q : ℕ) (hp : p.Prime) (hQ : 0 < Q)
    (s : Finset ℕ) (b : ℕ → ℝ)
    (hs : ∀ q ∈ s, q ∣ p * Q ∧ ¬ q ∣ Q) (hb : ∃ q ∈ s, b q ≠ 0) :
    0 < ∑ q ∈ s, ∑ r ∈ s, b q * b r * conductorInnovationCovariance Q p hQ q r := by
  exact new_packet_periodic_mean_covariance_pos p Q hp hQ s b hs hb
    (fun q => conductorMeanSequence Q p hQ (ramanujanPacket q))
    (fun q => ∑ r : Fin Q, |conductorQuotientMean Q p hQ (ramanujanPacket q) r|)
    (fun q k => conductorMeanSequence_abs_le Q p hQ (ramanujanPacket q) k)
    (fun q k => conductorMeanSequence_periodic Q p hQ (ramanujanPacket q) k)

end
end RiemannResearch.RH.Pareto
