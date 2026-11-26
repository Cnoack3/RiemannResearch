import RiemannResearch.RH.PhysicalHeadFiniteMinimum
import RiemannResearch.RH.MixedCanonicalCarryCapture
import RiemannResearch.RH.FiniteAtomCarryCRT
import RiemannResearch.RH.ParetoLCMRamanujanCertificate

/-!
# Least full Pareto norm in a finite mixed window

Source: the proposed Nyman–Beurling parity construction. Impose the physical head
of 1 - J₂ / log 2, then project away the zero-head directions in the chosen window.
The CRT coefficient involution preserves the synthesized correction at a common period.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadParityMinimum

open CoefficientStabilization TwoSeedExactHeadEnergy PhysicalHeadFiniteMinimum
open RiemannResearch.CategoryTheory.AtomCarryPresentation

/-- The mean-one parity seed used in the finite sections: J₂ / log 2. -/
abbrev paritySeed : ThresholdHilbert := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2

theorem paritySeed_mem_mean : paritySeed ∈ closedSpace ∧ inner ℝ paritySeed hilbertOne = 1 := by
  constructor
  · exact closedSpace.smul_mem _ (packet_mem_closedSpace 2 (by decide))
  · rw [paritySeed, real_inner_smul_left, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      Nat.cast_ofNat, inv_mul_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

/-- The explicit window supplied by mixed interpolation at physical depth N. -/
abbrev quadraticWindow (N : ℕ) : ℕ := 2 * (N + 1)^2

/-- Exact head required of the mixed correction to the parity seed. -/
def parityCorrectionHead (N : ℕ) : Fin N → ℝ :=
  (fun _ => 1) - headRestriction N paritySeed

/-- Characterization of the full-norm minimizing correction by the exact excess of
every feasible competitor in the same window. -/
def WindowMinimum (N B : ℕ) (g : ThresholdHilbert) (a : Fin N → ℝ) (z : ThresholdHilbert) : Prop :=
  z ∈ mixedSpace (Finset.Icc 2 B) ∧ headRestriction N z = a ∧
    ∀ w ∈ mixedSpace (Finset.Icc 2 B), headRestriction N w = a →
      ‖g+w‖^2 = ‖g+z‖^2 + ‖w-z‖^2

theorem existsUnique_windowMinimum (N B : ℕ) (g : ThresholdHilbert) (a : Fin N → ℝ)
    (hfeas : ∃ m ∈ mixedSpace (Finset.Icc 2 B), headRestriction N m = a) :
    ∃! z, WindowMinimum N B g a z := by
  let W := mixedSpace (Finset.Icc 2 B)
  let E := headRestriction N
  let K := W ⊓ E.ker
  let : FiniteDimensional ℝ K := FiniteDimensional.of_injective
    (Submodule.inclusion (inf_le_left : K ≤ W)) (Submodule.inclusion_injective _)
  obtain ⟨m, hm, he⟩ := hfeas
  let p := K.starProjection (g+m)
  have hp : p ∈ K := K.starProjection_apply_mem _
  have hpW : p ∈ W := hp.1
  have hp0 : E p = 0 := hp.2
  let z := m-p
  have hz : z ∈ W := W.sub_mem hm hpW
  have hze : E z = a := by
    change E (m-p) = a
    rw [map_sub, hp0, sub_zero]
    exact he
  have hzo : g+z ∈ Kᗮ := by
    rw [show g+z = (g+m) - K.starProjection (g+m) by dsimp only [z, p]; abel]
    exact K.sub_starProjection_mem_orthogonal _
  have hpy (w : ThresholdHilbert) (hw : w ∈ W) (hwe : E w = a) :
      ‖g+w‖^2 = ‖g+z‖^2 + ‖w-z‖^2 := by
    have hk : w-z ∈ K := by
      refine ⟨W.sub_mem hw hz, ?_⟩
      change E (w-z) = 0
      rw [map_sub, hwe, hze, sub_self]
    have ho := (Submodule.mem_orthogonal' _ _).mp hzo (w-z) hk
    calc
      ‖g+w‖^2 = ‖(g+z)+(w-z)‖^2 :=
        congrArg (fun y : ThresholdHilbert => ‖y‖^2) (by abel)
      _ = ‖g+z‖^2 + ‖w-z‖^2 := by rw [norm_add_sq_real, ho]; ring
  refine ⟨z, ⟨hz, hze, hpy⟩, ?_⟩
  rintro w ⟨hw, hwe, hwp⟩
  have h₁ := hpy w hw hwe
  have h₂ := hwp z hz hze
  rw [norm_sub_rev z w] at h₂
  have hzero : ‖w-z‖^2 = 0 := by linarith only [h₁, h₂]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

private theorem parityMinimum_existsUnique (N : ℕ) :
    ∃! z, WindowMinimum N (quadraticWindow N) paritySeed (parityCorrectionHead N) z :=
  existsUnique_windowMinimum N _ _ _ (quadratic_window_mixed_head N (parityCorrectionHead N))

/-- The unique mixed correction minimizing the full norm in the quadratic conductor window. -/
def optimalParityCorrection (N : ℕ) : ThresholdHilbert := (parityMinimum_existsUnique N).choose

theorem optimalParityCorrection_spec (N : ℕ) :
    WindowMinimum N (quadraticWindow N) paritySeed (parityCorrectionHead N)
      (optimalParityCorrection N) := (parityMinimum_existsUnique N).choose_spec.1

/-- The optimum has the same squared excess formula in the corrected CRT carry span. -/
theorem optimalParityCorrection_carry_cost (N : ℕ) :
    optimalParityCorrection N ∈ correctedCarrySpace (quadraticWindow N) ∧
    ∀ w ∈ correctedCarrySpace (quadraticWindow N), headRestriction N w = parityCorrectionHead N →
      ‖paritySeed+w‖^2 =
        ‖paritySeed+optimalParityCorrection N‖^2 + ‖w-optimalParityCorrection N‖^2 := by
  rw [correctedCarrySpace_eq_mixedSpace]
  exact ⟨(optimalParityCorrection_spec N).1, (optimalParityCorrection_spec N).2.2⟩

theorem optimalParityCorrection_unit_head (N : ℕ) (i : ℕ) (hi : i < N) :
    physicalEvaluationCLM i (paritySeed + optimalParityCorrection N) = 1 := by
  have h := congrFun (optimalParityCorrection_spec N).2.1 ⟨i, hi⟩
  simp only [parityCorrectionHead, Pi.sub_apply, headRestriction_apply] at h
  rw [map_add, physicalEvaluationCLM_apply, physicalEvaluationCLM_apply, h]
  ring

/-- Coefficients of every packet in a window belong to a common divisor stage. -/
private theorem window_sequence_mem_atomSpan (B : ℕ) {m : ThresholdHilbert}
    (hm : m ∈ mixedSpace (Finset.Icc 2 B)) :
    hilbertSequence m ∈ RiemannResearch.RH.FiniteAtomCarryCRT.atomSpan B.factorial := by
  let L := B.factorial
  have htrial : mixedSpace (Finset.Icc 2 B) ≤ ResidueMellin.trialSpace L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    have hq : q.val ∈ Finset.Icc 2 B := (Finset.mem_filter.mp q.property).1
    obtain ⟨hq2, hqB⟩ := Finset.mem_Icc.mp hq
    exact ResidueMellin.packet_mem_trial L _ (ResidueMellin.mem_packetIndex.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (by omega) hqB, (Nat.factorial_pos _).ne'⟩,
        by omega⟩)
  have hmap : ResidueMellin.trialSpace L ≤
      (RiemannResearch.RH.FiniteAtomCarryCRT.atomSpan L).comap hilbertSequenceLinear := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    have hd := Nat.pos_of_mem_divisors d.property
    change hilbertSequence (normalizedResidueHilbert d.val hd) ∈
      RiemannResearch.RH.FiniteAtomCarryCRT.atomSpan L
    rw [normalizedResidueHilbert_sequence]
    by_cases h1 : d.val = 1
    · have hz : ArithmeticCumulative.residueFraction d.val = 0 := by
        funext n
        simp [ArithmeticCumulative.residueFraction, h1, Nat.mod_one]
      rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨d.val, d.property, by omega, rfl⟩
  exact hmap (htrial hm)

/-- One coefficient array represents the same physical correction in the atom and carry
presentations. The second array is the explicit CRT involution of the first. -/
theorem window_crt_coordinates (B : ℕ) {m : ThresholdHilbert}
    (hm : m ∈ mixedSpace (Finset.Icc 2 B)) :
    let L := B.factorial
    let p := Fintype.linearCombination ℝ (FiniteAtomCarryCRT.primeAtom L)
    let q := Fintype.linearCombination ℝ (FiniteAtomCarryCRT.mixedAtom L)
    let c := Fintype.linearCombination ℝ (FiniteAtomCarryCRT.carryVector L)
    let U := coefficientSynthesis (FiniteAtomCarryCRT.rowCoefficients L)
    ∃ x, (p.coprod q) x = hilbertSequence m ∧ (p.coprod c) (crtEquiv U x) = hilbertSequence m := by
  classical
  let L := B.factorial
  let p := Fintype.linearCombination ℝ (FiniteAtomCarryCRT.primeAtom L)
  let q := Fintype.linearCombination ℝ (FiniteAtomCarryCRT.mixedAtom L)
  let c := Fintype.linearCombination ℝ (FiniteAtomCarryCRT.carryVector L)
  let U := coefficientSynthesis (FiniteAtomCarryCRT.rowCoefficients L)
  have hrep : hilbertSequence m ∈ LinearMap.range (p.coprod q) := by
    simpa only [p, q, LinearMap.range_coprod, Fintype.range_linearCombination,
      ← FiniteAtomCarryCRT.atomSpan_eq_partition] using window_sequence_mem_atomSpan B hm
  obtain ⟨x, hx⟩ := hrep
  have hrow : (fun j => (Fintype.linearCombination ℝ (FiniteAtomCarryCRT.primeAtom L))
      (FiniteAtomCarryCRT.rowCoefficients L j) -
      FiniteAtomCarryCRT.mixedAtom L j) = FiniteAtomCarryCRT.carryVector L := by
    funext j
    exact (FiniteAtomCarryCRT.carry_eq_row_sub_atom L j).symm
  have hcarry : carrySynthesis p q U = c := by
    have hr := family_carrySynthesis (FiniteAtomCarryCRT.primeAtom L)
      (FiniteAtomCarryCRT.mixedAtom L) (FiniteAtomCarryCRT.rowCoefficients L)
    rw [hrow] at hr
    exact hr
  refine ⟨x, hx, ?_⟩
  have hchange := DFunLike.congr_fun (crt_synthesis p q U) (crtEquiv U x)
  change (p.coprod q) (crtEquiv U (crtEquiv U x)) =
    (p.coprod (carrySynthesis p q U)) (crtEquiv U x) at hchange
  rw [crtEquiv_involutive, hcarry] at hchange
  exact hchange.symm.trans hx

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadParityMinimum
