import RiemannResearch.RH.CenteredMeanUnitNorm
import RiemannResearch.RH.ParetoLaguerreMellinTail
import RiemannResearch.RH.PrimeSupportLaguerreInterpolation
import RiemannResearch.RH.ParetoMobiusHeadInterpolation
import RiemannResearch.RH.MixedConductorResonanceProduct
import RiemannResearch.RH.ResidualEnergyHistoricalTargets
import RiemannResearch.RH.RamanujanMultipleCapacityLimits
import RiemannResearch.RH.ThresholdRiemannHypothesis
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Exact cost of matching finite Laguerre prefixes at a right zero -/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open CoefficientStabilization

private theorem one_readout_zero : laguerreReadout 0 hilbertOne = 1 := by
  have hb (k : ℕ) : |hilbertSequence hilbertOne k| ≤ 1 := by
    rw [hilbertOne_sequence]
    by_cases hk : k = 0 <;> simp [zeroAnchor, hk]
  rw [readout_coeff, coefficient_zero_of_bounded hb, ← hilbert_inner_one,
    real_inner_self_eq_norm_sq, hilbertOne_norm_sq]

private theorem one_readout_pos {j : ℕ} (hj : 0 < j) : laguerreReadout j hilbertOne = 0 := by
  have hs := hasSum_readout_sq hilbertOne
  have h := hs.summable.sum_le_tsum ({0,j} : Finset ℕ)
    (fun k _ => sq_nonneg (laguerreReadout k hilbertOne))
  rw [hs.tsum_eq, hilbertOne_norm_sq] at h
  simp only [Finset.sum_insert (by simpa using hj.ne : (0 : ℕ) ∉ ({j} : Finset ℕ)),
    Finset.sum_singleton, one_readout_zero, one_pow] at h
  exact sq_eq_zero_iff.mp (le_antisymm (by linarith only [h]) (sq_nonneg _))

private theorem cayley_radius {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    0 < ‖1 - 1 / s‖ ∧ ‖1 - 1 / s‖ < 1 ∧
      1 - ‖1 - 1 / s‖ ^ 2 = (2*s.re-1)/‖s‖^2 ∧
      ‖1 - 1 / s‖ = ‖s-1‖/‖s‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hsn := norm_pos_iff.mpr hs0
  have hh : 1 - 1/s = (s-1)/s := by field_simp [hs0] <;> ring
  have hr : ‖1-1/s‖ = ‖s-1‖/‖s‖ := by rw [hh, norm_div]
  have hn : ‖s-1‖^2 = ‖s‖^2-(2*s.re-1) := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    <;> ring
  have he : 1-‖1-1/s‖^2 = (2*s.re-1)/‖s‖^2 := by
    rw [hr, div_pow, hn]
    field_simp [hsn.ne'] <;> ring
  have hpos : 0 < (2*s.re-1)/‖s‖^2 := div_pos (by linarith) (sq_pos_of_pos hsn)
  exact ⟨hr.symm ▸ div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hs1)) hsn,
    by nlinarith [he, hpos, norm_nonneg (1 - 1 / s)], he, hr⟩

/-- A Mellin annihilator forces exponential error for every vector matching the
ambient constant at the first N readouts. -/
theorem mellin_zero_prefix_floor {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    {f : ThresholdHilbert} (hzero : paretoMellin f s = 0) (N : ℕ)
    (hmatch : ∀ j < N, laguerreReadout j f = laguerreReadout j hilbertOne) :
    (1-‖1-1/s‖^2)/‖1-1/s‖^(2*N) ≤ ‖f-hilbertOne‖^2 := by
  have heval : paretoMellin (hilbertOne - f) s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs, hzero, sub_zero]
  have hinit (j : ℕ) (hj : j < N) : laguerreReadout j (hilbertOne-f) = 0 := by
    rw [map_sub, hmatch j hj, sub_self]
  obtain ⟨hr, _, hrid, hratio⟩ := cayley_radius hs hs1
  have H := paretoMellin_norm_sq_le_of_laguerre_matching (hilbertOne-f) s hs N hinit
  rw [heval, norm_div, norm_one, div_pow, one_pow, norm_sub_rev hilbertOne f, ← hratio] at H
  rw [hrid]
  apply (div_le_iff₀ (pow_pos hr _)).mpr
  have hden : 0 < 2*s.re-1 := by linarith
  have H' : 1/‖s‖^2 ≤ (‖f-hilbertOne‖^2 * ‖1-1/s‖^(2*N))/(2*s.re-1) := by
    apply H.trans_eq
    ring
  have H'' := (le_div_iff₀ hden).mp H'
  simpa only [div_eq_mul_inv, one_mul, mul_comm (‖s‖^2)⁻¹] using H''

/-- The same exponential cost floor applies to every member of the closed legal
space at a hypothetical right zero. -/
theorem closed_legal_laguerre_prefix_zero_floor {s : ℂ}
    (hz : riemannZeta s = 0) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    {f : ThresholdHilbert} (hf : f ∈ closedSpace) (N : ℕ)
    (hmatch : ∀ j < N, laguerreReadout j f = laguerreReadout j hilbertOne) :
    (1-‖1-1/s‖^2)/‖1-1/s‖^(2*N) ≤ ‖f-hilbertOne‖^2 :=
  mellin_zero_prefix_floor hs hs1
    (paretoMellin_zero_on_legalClosure_of_zeta {a : ℕ | 0 < a}
      (fun _ ha => ha) s hs hs1 hz (closedSpace_le_legalClosure hf)) N hmatch

/-- The constant Laguerre readout represents the ambient Pareto mean on all of H. -/
private theorem scalar_readout_eq_mean (f : ThresholdHilbert) :
    laguerreReadout 0 f = inner ℝ hilbertOne f := by
  have hinner : inner ℝ (RiemannResearch.Analysis.laguerreVector 0)
      (laguerreRealization hilbertOne) = 1 := one_readout_zero
  have he := norm_sub_sq_real (RiemannResearch.Analysis.laguerreVector 0)
    (laguerreRealization hilbertOne)
  rw [RiemannResearch.Analysis.laguerreVector_orthonormal.1 0,
    laguerreRealization.norm_map, hilbertOne_norm_sq, hinner] at he
  have hvec : RiemannResearch.Analysis.laguerreVector 0 = laguerreRealization hilbertOne :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (by linarith only [he])))
  change inner ℝ (RiemannResearch.Analysis.laguerreVector 0) (laguerreRealization f) = _
  rw [hvec, laguerreRealization.inner_map_map]

/-- A common prime forces an explicit exponentially increasing complete squared norm
for attainable Laguerre prefixes, independently of the zeta zeros. -/
theorem fixedPrime_laguerre_prefix_exponential_floor (p : ℕ) (hp : p.Prime)
    {f : ThresholdHilbert} (hf : f ∈ singleSeedDilationClosure (ramanujanPacketHilbert p))
    (k : ℕ) (hmatch : ∀ j ≤ k, laguerreReadout j f = laguerreReadout j hilbertOne) :
    let r := ‖1 - 1 / primePacketResonance p 1‖
    0 < r ∧ r < 1 ∧ 1+(1-r^2)/r^(2*(k+1)) ≤ ‖f‖^2 := by
  let z := primePacketResonance p 1
  have hs : (1 / 2 : ℝ) < z.re := by
    rw [show z.re = 1 from primePacketResonance_re p hp.one_lt 1]
    norm_num
  have hs1 : z ≠ 1 :=
    RiemannResearch.RH.ArithmeticConductorCommonZeros.conductorSymbol_extra_zero_ne_one
      p hp.one_lt 1 (by norm_num)
  have hz : paretoMellin f z = 0 := by
    apply paretoMellin_zero_on_singleSeedClosure _ _ hs _ hf
    intro m hm
    rw [paretoMellin_dilation, primePacketResonance_mellin_zero p hp 1 (by norm_num), mul_zero]
  obtain ⟨hr0, hr1, _, _⟩ := cayley_radius hs hs1
  refine ⟨hr0,hr1,?_⟩
  have hl := mellin_zero_prefix_floor hs hs1 hz (k+1) (fun j hj => hmatch j (by omega))
  have hm : inner ℝ hilbertOne f = 1 := by
    rw [← scalar_readout_eq_mean, hmatch 0 (Nat.zero_le _), one_readout_zero]
  have he := norm_sub_sq_real f hilbertOne
  have hfm : inner ℝ f hilbertOne = 1 := (real_inner_comm ..).trans hm
  rw [hfm, hilbertOne_norm_sq] at he
  change 1+(1-‖1-1/z‖^2)/‖1-1/z‖^(2*(k+1)) ≤ ‖f‖^2
  linarith only [hl, he]

/-- The finite residue formulation of the historical variance target follows
by identifying its scalar and positive-index Laguerre observations. -/
theorem laguerreMatchingVariance : LaguerreMatchingVarianceTarget := by
  intro s hz hs hslt k f hf hmean hprefix
  obtain ⟨n, hn⟩ := hf
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hslt
  apply closed_legal_laguerre_prefix_zero_floor hz hs hs1
    (RamanujanMultipleCapacityLimits.finiteSpace_le_closedSpace n hn) (k+1)
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjp
  · rw [one_readout_zero, scalar_readout_eq_mean, hmean]
  · rw [one_readout_pos hjp, readout_coeff, hprefix j (by omega) (by omega)]

/-- The finite conductor and the matched finite legal vector may depend on both
the prescribed Laguerre depth and the exponential base. -/
def CofinalSubexponentialLaguerrePrefixes : Prop :=
  ∀ a : ℝ, 1 < a → ∃ C : ℝ, ∀ K : ℕ, ∃ k ≥ K, ∃ f : ThresholdHilbert,
    FiniteResidueLegal f ∧ inner ℝ hilbertOne f = 1 ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ k → coefficient (hilbertSequence f) j = 0) ∧
    ‖f‖^2 ≤ C*a^k

/-- Legal packets matching cofinal prefixes with subexponential complete squared norm
force the Riemann hypothesis. The finite conductor and the vector may depend on
both the prefix length and the permitted exponential base. -/
theorem riemannHypothesis_of_cofinal_subexponential_laguerre_prefix
    (h : CofinalSubexponentialLaguerrePrefixes) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hslt
  let r := ‖1-1/s‖
  obtain ⟨hr, hlt, _, _⟩ := cayley_radius hs hs1
  have hr0 : 0 < r := hr
  have hr1 : r < 1 := hlt
  have hn : 0 < 1-r^2 := by nlinarith [sq_nonneg (1-r), mul_pos (sub_pos.mpr hr1) (by linarith : 0 < 1+r)]
  have hbase : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
  obtain ⟨C,hC⟩ := h (r⁻¹) hbase
  have ht : Tendsto (fun k : ℕ => (C*r^2)*r^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C*r^2)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hn))
  obtain ⟨k, hk, f, hf, hm, hprefix, hcost⟩ := hC K
  have hfloor : 1-r^2 ≤ (C*r^2)*r^k := by
    have hl := laguerreMatchingVariance s hz hs hslt k f hf hm hprefix
    change (1-r^2)/r^(2*(k+1)) ≤ ‖f-hilbertOne‖^2 at hl
    have he : ‖f-hilbertOne‖^2 ≤ ‖f‖^2 := by
      have hfm : inner ℝ f hilbertOne = 1 := (real_inner_comm ..).trans hm
      rw [norm_sub_sq_real, hfm, hilbertOne_norm_sq]
      linarith
    have hle := (div_le_iff₀ (pow_pos hr0 _)).mp ((hl.trans he).trans hcost)
    calc
      _ ≤ _ := hle
      _ = (C*r^2)*r^k := by
        rw [show 2*(k+1) = k+(k+2) by omega, pow_add r k (k+2), pow_add r k 2, inv_pow]
        field_simp [(pow_ne_zero k hr0.ne')] <;> ring
  exact (not_lt_of_ge hfloor) (hK k hk)

/-- RH is equivalent to subexponential complete squared cost of actual finite
residue lifts at arbitrarily large Laguerre depths. -/
theorem riemannHypothesis_iff_cofinal_subexponential_laguerre_prefixes :
    RiemannHypothesis ↔ CofinalSubexponentialLaguerrePrefixes := by
  refine ⟨?_, riemannHypothesis_of_cofinal_subexponential_laguerre_prefix⟩
  intro hRH
  have href := bounded_finite_laguerre_prefixes_iff_riemannHypothesis.mpr hRH
  obtain ⟨C, hC⟩ := href
  obtain ⟨v₀, _, _, hv₀⟩ := hC 0
  have hC0 := (sq_nonneg ‖v₀‖).trans hv₀
  intro a ha
  refine ⟨C, fun k => ⟨k, le_rfl, ?_⟩⟩
  obtain ⟨v, hv, hpre, hvnorm⟩ := hC k
  change v ∈ Submodule.span ℝ (Set.range residueAtom) at hv
  rw [← RiemannResearch.Analysis.ExhaustiveWalk.iSup_walkSpan residueAtom id
    Function.surjective_id] at hv
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _
    (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id).directed_le).mp hv
  have hmean : inner ℝ hilbertOne v = 1 := by
    rw [← scalar_readout_eq_mean, hpre 0 (Nat.zero_le _), one_readout_zero]
  refine ⟨v, ⟨n,hn⟩, hmean, ?_, ?_⟩
  · intro j hj hjk
    rw [← readout_coeff, hpre j hjk, one_readout_pos (by omega)]
  · calc
      ‖v‖^2 ≤ C := hvnorm
      _ = C*1 := (mul_one C).symm
      _ ≤ C*a^k := mul_le_mul_of_nonneg_left (one_le_pow₀ ha.le) hC0

open PrimePowerSchur in
/-- Exact finite arithmetic interpolation detects both the categorical kernel lift
and the unit norm of the physical screened section at every mixed stage. -/
theorem stage_lift_and_unit_norm_iff_cofinal_prefixes
    (S : Submodule ℝ mixedClosure) :
    ((∃! k : (PrimePowerSchur.CenteredMeanSnake.Stage.middleVertical S).ker,
        PrimePowerSchur.CenteredMeanSnake.Stage.kernelMean S k = 1) ↔
      CofinalSubexponentialLaguerrePrefixes) ∧
    (‖normalizedScreenedTwo‖ ≤ 1 ↔ CofinalSubexponentialLaguerrePrefixes) := by
  have h := PrimePowerSchur.CenteredMeanSnake.stage_lift_unit_norm_tfae S
  exact ⟨(h.out 1 4).trans riemannHypothesis_iff_cofinal_subexponential_laguerre_prefixes,
    (h.out 2 4).trans riemannHypothesis_iff_cofinal_subexponential_laguerre_prefixes⟩

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.laguerreMatchingVariance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms laguerreMatchingVariance

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.fixedPrime_laguerre_prefix_exponential_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixedPrime_laguerre_prefix_exponential_floor

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.riemannHypothesis_iff_cofinal_subexponential_laguerre_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_cofinal_subexponential_laguerre_prefixes

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.stage_lift_and_unit_norm_iff_cofinal_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stage_lift_and_unit_norm_iff_cofinal_prefixes

end RiemannResearch.RH.Pareto.RamanujanLaguerre
