import RiemannResearch.RH.ArithmeticConductorCommonZeros
import RiemannResearch.RH.FiniteSeedMellinObstruction
import RiemannResearch.RH.NymanConductorContinuation
import RiemannResearch.RH.ParetoResidueMellinContinuation
import RiemannResearch.RH.PrimePowerRamanujanSchur
import RiemannResearch.RH.IntegratedRamanujanBasis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# A one-prime restriction on mixed corrections leaves a positive error floor

The existing single-seed Mellin separation and conductor resonance apply to
every packet divisible by the seed prime. In particular, a conductor-2 trial
needs mixed directions beyond the even conductors if its error is to vanish.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticConductorCommonZeros

theorem ramanujanPacketHilbert_mem_singleSeed_of_dvd (p q : ℕ) (hp : p.Prime)
    (hq : 0 < q) (hd : p ∣ q) :
    ramanujanPacketHilbert q ∈ singleSeedDilationClosure (ramanujanPacketHilbert p) := by
  let K := singleSeedDilationClosure (ramanujanPacketHilbert p)
  have hspan : legalSeedSpan ({p} : Set ℕ) ≤ K.map hilbertSequenceLinear := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, m, hm, rfl⟩
    have he : a = p := Set.mem_singleton_iff.mp ha
    subst a
    refine ⟨hilbertDilation m hm (ramanujanPacketHilbert p), ?_, ?_⟩
    · exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨m, hm, rfl⟩)
    · change hilbertSequence (hilbertDilation m hm (ramanujanPacketHilbert p)) = _
      rw [hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert,
        ramanujanPacket_prime_eq_residue p hp]
  obtain ⟨m, rfl⟩ := hd
  have hm : 0 < m := by
    by_contra! h
    have he : m = 0 := by omega
    simp [he] at hq
  have hx : hilbertSequenceLinear (ramanujanPacketHilbert (p * m)) ∈ K.map hilbertSequenceLinear :=
    hspan (by
      change hilbertSequence (ramanujanPacketHilbert (p * m)) ∈ legalSeedSpan ({p} : Set ℕ)
      rw [hilbertSequence_ramanujanPacketHilbert]
      exact ramanujanPacket_seed_multiple_mem _ p hp (by simp) m hm)
  obtain ⟨v, hv, he⟩ := hx
  have he' : v = ramanujanPacketHilbert (p * m) := hilbertSequence_injective he
  exact he' ▸ hv

/-- An explicit Mellin bound for every mixed correction whose conductors are
all divisible by the same prime as the input packet. -/
theorem restricted_mixed_seed_error_floor (p : ℕ) (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q ∧ p ∣ q) {c : ThresholdHilbert}
    (hc : c ∈ PrimePowerSchur.mixedSpace s) :
    let z : ℂ := 1 + (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) / (Real.log p : ℂ)
    0 < 1 / ‖z‖ ^ 2 ∧ 1 / ‖z‖ ^ 2 ≤
      ‖hilbertOne - (Real.log p)⁻¹ • (ramanujanPacketHilbert p - c)‖ ^ 2 := by
  intro z
  let K := singleSeedDilationClosure (ramanujanPacketHilbert p)
  have hle : PrimePowerSchur.mixedSpace s ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    have hq := hs q.val (Finset.mem_filter.mp q.property).1
    exact ramanujanPacketHilbert_mem_singleSeed_of_dvd p q.val hp (by omega) hq.2
  have hx : (Real.log p)⁻¹ • (ramanujanPacketHilbert p - c) ∈ K :=
    K.smul_mem _ (K.sub_mem
      (ramanujanPacketHilbert_mem_singleSeed_of_dvd p p hp hp.pos dvd_rfl) (hle hc))
  have hzero : conductorSymbol p z = 0 := conductorSymbol_explicit_zero p hp.one_lt 1
  have hz : z ≠ 1 := conductorSymbol_extra_zero_ne_one p hp.one_lt 1 (by decide)
  have hre : z.re = 1 := conductorSymbol_zero_re p hp.one_lt z hzero
  have hhalf : (1 / 2 : ℝ) < z.re := by rw [hre]; norm_num
  have hpos : 0 < z.re := by rw [hre]; norm_num
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : (p : ℂ) ^ (1 - z) = 1 := by
    rw [RiemannResearch.RH.conductorSymbol_eq_cpow p hp.pos] at hzero
    rw [sub_eq_zero] at hzero
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hpC, Complex.cpow_one, ← hzero]
    field_simp
  have hv : ramanujanPacketHilbert p = digitHilbert p 1 hp.pos (by omega) := by
    apply hilbertSequence_injective
    rw [hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_prime_eq_residue p hp,
      hilbertSequence_digitHilbert]
    funext k
    simp [digitSequence, residue]
  have hnull : paretoMellin (ramanujanPacketHilbert p) z = 0 := by
    rw [hv, paretoMellin_residue_zeta p hp.pos z hpos hz, hpow, sub_self, mul_zero]
  have hz0 : z ≠ 0 := by intro hz0; simp [hz0] at hre
  refine ⟨one_div_pos.mpr (pow_pos (norm_pos_iff.mpr hz0) _), ?_⟩
  have hb := singleSeedClosure_distance_sq_lower_bound (ramanujanPacketHilbert p) z hhalf hnull hx
  simpa only [hre, mul_one, show (2 : ℝ) - 1 = 1 by norm_num] using hb

end RiemannResearch.RH.Pareto
