import RiemannResearch.RH.ArithmeticPacketCore
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.ThresholdHilbertDifference
import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.ResidueClosureDensity
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Periodic reflection along one prime-power dilation tower

Source: the supplied CRT packet character decomposition, equations (1) and
(2). Reflection about zero at positive sites equals the totient constant
minus the bounded backward shift. Repeated powers of a prime already in the
conductor give exact dilation energies throughout the complete Pareto space.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PacketReflectionTower
open CoefficientStabilization

/-- The physical Hilbert vector of the periodically reflected packet;
coordinate zero uses the Hilbert space's zero anchor. -/
def reflectedPacket (q : ℕ) : ThresholdHilbert :=
  (q.totient : ℝ) • hilbertOne - hilbertBackwardShift (ramanujanPacketHilbert q)

theorem reflectedPacket_at (q k : ℕ) (hq : 1 < q) :
    hilbertSequence (reflectedPacket q) (k+1) =
      ramanujanPacket q (q - 1 - (k % q)) := by
  have hmod : ramanujanPacket q (k % q) = ramanujanPacket q k := by
    unfold ramanujanPacket
    apply Finset.sum_congr rfl
    intro d hd
    simp only [residue, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mem_divisors hd)]
  have h := packet_reflection_totient q q (k % q) hq (dvd_refl _) (Nat.mod_lt _ (by omega))
  rw [hmod] at h
  simp only [reflectedPacket, hilbertSequence_sub, hilbertSequence_smul, hilbertOne_sequence,
    hilbertBackwardShift_sequence, hilbertSequence_ramanujanPacketHilbert, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, PrimitiveEnergy.backwardShift, Nat.add_sub_cancel, zeroAnchor]
  simpa using (show (q.totient : ℝ) - ramanujanPacket q k = _ by linarith only [h])

private theorem prime_step {p m : ℕ} (hp : p.Prime) (hm : 1 < m) (hd : p ∣ m) :
    ramanujanPacketHilbert (p*m) = hilbertDilation p hp.pos (ramanujanPacketHilbert m) := by
  apply hilbertSequence_injective
  funext n
  simp only [hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert]
  exact ramanujanPacket_mul_prime_of_dvd p m n hp hm hd

/-- Increasing the exponent of an existing prime dilates the entire packet. -/
theorem packet_prime_tower (p q k : ℕ) (hp : p.Prime) (hq : 1 < q) (hd : p ∣ q) :
    ramanujanPacketHilbert (p^k*q) =
      hilbertDilation (p^k) (pow_pos hp.pos _) (ramanujanPacketHilbert q) := by
  induction k with
  | zero => simp [hilbertDilation_one]
  | succ k ih =>
    have hm : 1 < p^k*q := lt_of_lt_of_le hq (Nat.le_mul_of_pos_left _ (pow_pos hp.pos _))
    have hs := prime_step hp hm (dvd_mul_of_dvd_right hd (p^k))
    have hc := hilbertDilation_comp p (p^k) hp.pos (pow_pos hp.pos k) (ramanujanPacketHilbert q)
    simpa only [pow_succ' p k, Nat.mul_assoc] using
      hs.trans ((congrArg (hilbertDilation p hp.pos) ih).trans hc)

private theorem totient_tower (p q k : ℕ) (hp : p.Prime) (hd : p ∣ q) :
    (p^k*q).totient = p^k*q.totient := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Nat.mul_assoc, Nat.totient_mul_of_prime_of_dvd hp
      (dvd_mul_of_dvd_right hd _), ih, Nat.mul_assoc]

def scaledPacket (p q k : ℕ) : ThresholdHilbert :=
  (p : ℝ)⁻¹ ^ k • ramanujanPacketHilbert (p^k*q)

def scaledReflection (p q k : ℕ) : ThresholdHilbert :=
  (p : ℝ)⁻¹ ^ k • reflectedPacket (p^k*q)

theorem scaledPacket_norm_sq (p q k : ℕ) (hp : p.Prime) (hq : 1 < q) (hd : p ∣ q) :
    ‖scaledPacket p q k‖^2 = (p : ℝ)⁻¹ ^ k * ‖ramanujanPacketHilbert q‖^2 := by
  have hn : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [scaledPacket, packet_prime_tower p q k hp hq hd, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, hilbertDilation_norm_sq, Nat.cast_pow, inv_pow]
  field_simp

theorem scaledReflection_eq (p q k : ℕ) (hp : p.Prime) (hd : p ∣ q) :
    scaledReflection p q k =
      (q.totient : ℝ) • hilbertOne - hilbertBackwardShiftContinuous (scaledPacket p q k) := by
  have hn : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  simp only [scaledReflection, reflectedPacket, smul_sub, totient_tower p q k hp hd,
    Nat.cast_mul, Nat.cast_pow, smul_smul, scaledPacket, map_smul,
    hilbertBackwardShiftContinuous_apply, inv_pow, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Exact energy identity including the positive mass lost under the backward shift. -/
theorem reflected_tower_energy (p q k : ℕ) (hp : p.Prime) (hq : 1 < q) (hd : p ∣ q) :
    ‖scaledReflection p q k - (q.totient : ℝ) • hilbertOne‖^2 +
      PrimitiveEnergy.shiftDefect (hilbertSequence (scaledPacket p q k)) =
        (p : ℝ)⁻¹ ^ k * ‖ramanujanPacketHilbert q‖^2 := by
  rw [scaledReflection_eq p q k hp hd, sub_sub_cancel_left, norm_neg,
    hilbertBackwardShiftContinuous_apply, ← hilbert_norm_sub_backwardShift,
    ← scaledPacket_norm_sq p q k hp hq hd]
  ring

theorem scaledPacket_tendsto_zero (p q : ℕ) (hp : p.Prime) (hq : 1 < q) (hd : p ∣ q) :
    Tendsto (scaledPacket p q) atTop (𝓝 0) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr (le_trans zero_le_one hpR.le)) (inv_lt_one_of_one_lt₀ hpR)
  have hs : Tendsto (fun k => ‖scaledPacket p q k‖^2) atTop (𝓝 0) := by
    simpa only [scaledPacket_norm_sq p q _ hp hq hd, zero_mul] using
      hpow.mul_const (‖ramanujanPacketHilbert q‖^2)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hs)

theorem scaledReflection_tendsto (p q : ℕ) (hp : p.Prime) (hq : 1 < q) (hd : p ∣ q) :
    Tendsto (scaledReflection p q) atTop (𝓝 ((q.totient : ℝ) • hilbertOne)) := by
  have hs := hilbertBackwardShiftContinuous.continuous.continuousAt.tendsto.comp
    (scaledPacket_tendsto_zero p q hp hq hd)
  simpa only [Function.comp_def, ← scaledReflection_eq p q _ hp hd, map_zero, sub_zero] using
    (tendsto_const_nhds (x := (q.totient : ℝ) • hilbertOne)).sub hs

/-- RH is equivalent to cofinal exact legal membership of the reflected
packets on any one such tower. Under RH the entire Pareto legal space is dense. -/
theorem rh_iff_frequently_mem_reflected_tower (p q : ℕ) (hp : p.Prime) (hq : 1 < q)
    (hd : p ∣ q) :
    RiemannHypothesis ↔ ∃ᶠ k in atTop, scaledReflection p q k ∈ closedSpace := by
  have hx := PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.trans
    BaezDuarte.naturalApproximation_iff_one_mem
  constructor
  · intro h
    have ht := closedSpace_eq_top_iff_one_mem.mpr (hx.mp h)
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro k
    rw [ht]
    exact Submodule.mem_top
  · intro h
    have hc : IsClosed (closedSpace : Set ThresholdHilbert) := isClosed_closure
    have hh := hc.mem_of_frequently_of_tendsto h (scaledReflection_tendsto p q hp hq hd)
    apply hx.mpr
    have hn : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q)).ne'
    simpa [smul_smul, hn] using closedSpace.smul_mem (q.totient : ℝ)⁻¹ hh

end RiemannResearch.RH.Pareto.PacketReflectionTower
