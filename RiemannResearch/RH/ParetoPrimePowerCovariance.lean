import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ThresholdRiemannHypothesis
import RiemannResearch.RH.PrimePowerRamanujanSchur
import RiemannResearch.RH.ScreenedParityPhysicalBounds
import RiemannResearch.RH.MixedConductorCovariance
import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Pareto projection and a single prime-power test

For the Pareto weights `1 / (n * (n + 1))` on the positive integers, write
`V = closedSpace` for the closed real span of the residues and `M = mixedClosure`
for the closed span of packets with at least two distinct prime divisors.
The constant target is `hilbertOne`. The screened parity vector is
`u = (J₂ - P_M J₂) / log 2`.

The residue mean and Möbius inversion give `⟪J_q, 1⟫ = Λ(q)` in
`ParetoResidueMean`. The arithmetic rigidity theorem in `MixedConductorRankOne`
gives `(I - P_M) J_q = Λ(q) • u`. Thus the screened prime powers span the
line through `u` in `V`, and `⟪u, 1⟫ = 1`. The distinction between `u` and the
ambient constant is measured below by the covariance with a single packet.

Bagchi, *On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation
of the Riemann hypothesis*, Theorem 1, https://arxiv.org/abs/math/0607733,
gives the discrete closure criterion. Báez-Duarte's natural-dilation theorem
is at https://arxiv.org/abs/math/0202141. For the additive rigidity input see
Kátai, *On additive functions*, equations (1.1) and (1.2),
https://doi.org/10.5486/PMD.1978.25.3-4.10.

Acknowledgment. I thank Michael Kruskal for his help with the Lean formalization.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization
open Filter
open scoped Topology

private theorem inner_centered_of_mean_one {x : ThresholdHilbert}
    (hx : inner ℝ x hilbertOne = 1) :
    inner ℝ x (x - hilbertOne) = ‖x - hilbertOne‖ ^ 2 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real, hx, hilbertOne_norm_sq]
  ring

/-- On the legal space, pairing with the centered screened vector is the
mean multiplied by the full squared distance from the constant. -/
theorem legal_pairing_screenedTwo_sub_one {v : ThresholdHilbert} (hv : v ∈ closedSpace) :
    inner ℝ v (normalizedScreenedTwo - hilbertOne) =
      inner ℝ v hilbertOne * ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  have hd : normalizedScreenedTwo - hilbertOne ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.sub_mem hu.2 one_mem_mixedClosure_orthogonal
  calc
    _ = inner ℝ (fullScreening v) (normalizedScreenedTwo - hilbertOne) :=
      (fullScreening_inner_right_of_orthogonal v _ hd).symm
    _ = _ := by rw [fullScreening_eq_mean_smul hv, real_inner_smul_left,
      inner_centered_of_mean_one normalizedScreenedTwo_mean]

/-- The covariance for every conductor, including all powers of each prime.
For a mixed conductor the factor on the right vanishes. -/
theorem packet_pairing_screenedTwo_sub_one (q : ℕ) (hq : 1 < q) :
    inner ℝ (ramanujanPacketHilbert q) (normalizedScreenedTwo - hilbertOne) =
      ArithmeticFunction.vonMangoldt q * ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  rw [legal_pairing_screenedTwo_sub_one (packet_mem_closedSpace q hq), hilbert_inner_one,
    hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket]

/-- At a single prime power the covariance is nonpositive exactly when the
ambient constant belongs to the closed residue span. -/
theorem one_mem_iff_primePower_pairing_nonpos (q : ℕ) (hq : 1 < q) (hp : IsPrimePow q) :
    hilbertOne ∈ closedSpace ↔
      inner ℝ (ramanujanPacketHilbert q) (normalizedScreenedTwo - hilbertOne) ≤ 0 := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo, packet_pairing_screenedTwo_sub_one q hq]
  constructor
  · intro hu
    simp [hu]
  · intro h
    have hΛ : 0 < ArithmeticFunction.vonMangoldt q :=
      ArithmeticFunction.vonMangoldt_pos_iff.mpr hp
    by_contra hne
    exact (not_lt_of_ge h) (mul_pos hΛ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))))

/-- The single open parity inequality suffices for the Riemann hypothesis.
Here the raw packet at two is the indicator of odd sites. -/
theorem riemannHypothesis_of_parity_pairing_nonpos
    (h : inner ℝ (ramanujanPacketHilbert 2) (normalizedScreenedTwo - hilbertOne) ≤ 0) :
    RiemannHypothesis := by
  have hmem : hilbertOne ∈ closedSpace :=
    (one_mem_iff_primePower_pairing_nonpos 2 (by decide) Nat.prime_two.isPrimePow).mpr h
  exact riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn) (closedSpace_le_legalClosure hmem)

/-! ## Appendix. Testing the inequality at finite mixed cutoffs -/

/-- At each finite cutoff the parity pairing is exactly the squared approximation
error multiplied by the odd-site mass. -/
theorem finite_parity_pairing_eq_variance (N : ℕ) :
    inner ℝ (ramanujanPacketHilbert 2) (fixedTwoTrial N - hilbertOne) =
      Real.log 2 * ‖fixedTwoTrial N - hilbertOne‖ ^ 2 := by
  let K := mixedSpace (Finset.Icc 2 N)
  let z := ramanujanPacketHilbert 2
  let u := fixedTwoTrial N
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hmean : inner ℝ u hilbertOne = 1 := by
    change inner ℝ ((Real.log 2)⁻¹ • screenedPacket (Finset.Icc 2 N) 2) hilbertOne = 1
    rw [real_inner_smul_left, screenedPacket_inner_one,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact inv_mul_cancel₀ hlog
  have horth : u - hilbertOne ∈ Kᗮ :=
    K.orthogonal.sub_mem
      (K.orthogonal.smul_mem _ (K.sub_starProjection_mem_orthogonal z))
      (one_mem_mixed_orthogonal _)
  have hsplit : z = K.starProjection z + (Real.log 2) • u := by
    change z = K.starProjection z + (Real.log 2) • ((Real.log 2)⁻¹ • (z - K.starProjection z))
    rw [smul_smul, mul_inv_cancel₀ hlog, one_smul]
    abel
  change inner ℝ z (u - hilbertOne) = Real.log 2 * ‖u - hilbertOne‖ ^ 2
  calc
    _ = inner ℝ (K.starProjection z + (Real.log 2) • u) (u - hilbertOne) :=
      congrArg (fun x => inner ℝ x (u - hilbertOne)) hsplit
    _ = _ := by
      rw [inner_add_left, horth _ (K.starProjection_apply_mem z), zero_add,
        real_inner_smul_left, inner_centered_of_mean_one hmean]

/-- The signed error is strictly positive at every finite cutoff. All trial
packets vanish at a common positive multiple of their conductors. -/
theorem finite_parity_pairing_pos (N : ℕ) :
    0 < inner ℝ (ramanujanPacketHilbert 2) (fixedTwoTrial N - hilbertOne) := by
  have hne : fixedTwoTrial N ≠ hilbertOne := by
    intro he
    have hz := fixedTwoTrial_at_common_factorial N
    rw [he, hilbertOne_sequence] at hz
    have hpos : 0 < 2 * (N + 1).factorial := Nat.mul_pos (by decide) (Nat.factorial_pos _)
    simp [zeroAnchor, hpos.ne'] at hz
  rw [finite_parity_pairing_eq_variance]
  exact mul_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))

/-- An equivalent statement of the open sign using only finite projections. -/
theorem one_mem_iff_finite_parity_pairing_tendsto_zero :
    hilbertOne ∈ closedSpace ↔
      Tendsto (fun N => inner ℝ (ramanujanPacketHilbert 2) (fixedTwoTrial N - hilbertOne))
        atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun N => inner ℝ (ramanujanPacketHilbert 2) (fixedTwoTrial N - hilbertOne)) atTop
      (𝓝 (inner ℝ (ramanujanPacketHilbert 2) (normalizedScreenedTwo - hilbertOne))) :=
    tendsto_const_nhds.inner (fixedTwoTrial_tendsto.sub_const hilbertOne)
  constructor
  · intro hmem
    simpa [one_mem_closedSpace_iff_normalizedScreenedTwo.mp hmem] using hlim
  · intro hzero
    exact (one_mem_iff_primePower_pairing_nonpos 2 (by decide) Nat.prime_two.isPrimePow).mpr
      (tendsto_nhds_unique hlim hzero).le

end RiemannResearch.RH.Pareto.PrimePowerSchur
