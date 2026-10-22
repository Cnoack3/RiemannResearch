import RiemannResearch.RH.ParetoMellinObstructionTargets
import RiemannResearch.RH.ArithmeticMellinIdentity
import RiemannResearch.RH.ParetoCompressedMellinNorm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace RiemannResearch.RH.Pareto.CompressedMellin
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def phaseMellinPoint (t : ℝ) : ℂ := 1 + (t : ℂ) * Complex.I

def phaseMellinForward (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t * Real.log t - t : ℝ) : ℂ))

theorem phaseMellinPoint_re (t : ℝ) : (phaseMellinPoint t).re = 1 := by
  simp [phaseMellinPoint]

def actualPhaseCenteredOperator (t : ℝ) : ThresholdHilbert →L[ℝ] ℂ :=
  phaseMellinForward t • paretoMellinContinuous (phaseMellinPoint t)
    (by rw [phaseMellinPoint_re]; norm_num)

theorem actualPhaseCenteredOperator_apply (t : ℝ) (f : ThresholdHilbert) :
    actualPhaseCenteredOperator t f = phaseMellinForward t * paretoMellin f (phaseMellinPoint t) := rfl

theorem phaseMellinForward_norm (t : ℝ) : ‖phaseMellinForward t‖ = 1 := by
  rw [phaseMellinForward, Complex.norm_exp]
  simp

private theorem star_exp_neg_I_mul (x : ℝ) :
    star (Complex.exp (-Complex.I * (x : ℂ))) = Complex.exp (Complex.I * (x : ℂ)) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp

private theorem star_exp_I_mul (x : ℝ) :
    star (Complex.exp (Complex.I * (x : ℂ))) = Complex.exp (-Complex.I * (x : ℂ)) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp

private def phaseCell (n : ℕ) : Set ℝ := Ico ((n : ℝ) + 1) ((n : ℝ) + 2)

private theorem phaseCell_floor (n : ℕ) {x : ℝ} (hx : x ∈ phaseCell n) :
    ⌊x⌋₊ = n + 1 := by
  apply Nat.floor_eq_on_Ico
  simpa only [phaseCell, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hx

private theorem phaseCell_disjoint : Pairwise (Function.onFun Disjoint phaseCell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (Nat.add_right_cancel ((phaseCell_floor i hi).symm.trans (phaseCell_floor j hj)))

private theorem phaseCell_union : (⋃ n, phaseCell n) = Ici (1 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    change (n : ℝ) + 1 ≤ x ∧ x < (n : ℝ) + 2 at hn
    exact le_trans (by linarith [Nat.cast_nonneg (α := ℝ) n]) hn.1
  · intro hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx
    have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx)
    let n := ⌊x⌋₊ - 1
    have hn : n + 1 = ⌊x⌋₊ := Nat.sub_add_cancel hf
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hlo := Nat.floor_le hx0
    have hhi := Nat.lt_floor_add_one x
    rw [← hn] at hlo hhi
    simpa only [phaseCell, Set.mem_Ico, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using And.intro hlo hhi

private theorem cpow_phase_antiderivative (t x : ℝ) (hx : 0 < x) :
    (x : ℂ)^(-phaseMellinPoint t) =
      Complex.exp (-Complex.I * ((t * Real.log x : ℝ) : ℂ)) / (x : ℂ) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [show -phaseMellinPoint t = (-Complex.I * (t : ℂ)) - 1 by
    unfold phaseMellinPoint; ring,
    Complex.cpow_sub _ _ hxC, Complex.cpow_one,
    Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le]
  congr 2
  push_cast
  ring

/-- Integral of the actual Mellin kernel over one physical unit cell. -/
theorem compressedMellinCell_integral (t : ℝ) (n : ℕ) :
    (∫ x in phaseCell n, (x : ℂ)^(-phaseMellinPoint t - 1)) =
      (paretoWeight n : ℂ) * star (compressedMellinCell t n) := by
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) + 2 := by positivity
  have haC : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast hb.ne'
  have hdC : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
  have hz : (0 : ℝ) ∉ uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    rw [uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hr : -phaseMellinPoint t - 1 ≠ (-1 : ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp [phaseMellinPoint] at hh
  unfold phaseCell
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_cpow (Or.inr ⟨hr, hz⟩)]
  rw [show -phaseMellinPoint t - 1 + 1 = -phaseMellinPoint t by ring,
    cpow_phase_antiderivative t _ hb, cpow_phase_antiderivative t _ ha]
  have hstarReal (x : ℝ) : star (x : ℂ) = (x : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hstarI : star Complex.I = -Complex.I := by rw [Complex.star_def]; simp
  unfold compressedMellinCell
  rw [star_div₀, star_sub, star_mul, star_mul, hstarReal, hstarReal,
    star_exp_I_mul, star_exp_I_mul]
  simp only [star_sub, star_one, star_mul, hstarI, hstarReal]
  unfold paretoWeight phaseMellinPoint
  push_cast
  field_simp [haC, hbC, hdC]
  <;> ring

/-- Complete unit-cell decomposition of the actual bounded Mellin functional. -/
theorem paretoMellin_eq_compressed_cells (t : ℝ) (f : ThresholdHilbert) :
    paretoMellin f (phaseMellinPoint t) =
      ∑' n, ((paretoWeight n * hilbertSequence f (n + 1) : ℝ) : ℂ) *
        star (compressedMellinCell t n) := by
  have hi : IntegrableOn (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) *
      (x : ℂ)^(-phaseMellinPoint t - 1)) (Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact paretoMellin_step_integrable f (phaseMellinPoint t)
      (by rw [phaseMellinPoint_re]; norm_num)
  rw [paretoMellin_eq_step_integral, ← integral_Ici_eq_integral_Ioi, ← phaseCell_union]
  rw [integral_iUnion (s := phaseCell) (fun _ => measurableSet_Ico) phaseCell_disjoint
    (by simpa only [phaseCell_union] using hi)]
  apply tsum_congr
  intro n
  calc
    _ = ∫ x in phaseCell n, (hilbertSequence f (n + 1) : ℂ) *
        (x : ℂ)^(-phaseMellinPoint t - 1) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      dsimp only
      rw [phaseCell_floor n hx]
    _ = _ := by
      rw [integral_const_mul, compressedMellinCell_integral]
      push_cast
      ring

/-- The selected operator has exactly the pairing recorded in the target. -/
theorem actualPhaseCenteredOperator_eq_pairing (t : ℝ) (f : ThresholdHilbert) :
    actualPhaseCenteredOperator t f = phaseCenteredPairing t f := by
  rw [actualPhaseCenteredOperator_apply, paretoMellin_eq_compressed_cells, ← tsum_mul_left]
  unfold phaseCenteredPairing
  apply tsum_congr
  intro n
  rw [phaseCenteredMellinCell, star_mul, star_exp_neg_I_mul]
  unfold phaseMellinForward
  ring

theorem actualPhaseCenteredOperator_one_norm (t : ℝ) :
    ‖actualPhaseCenteredOperator t hilbertOne‖ = 1 / Real.sqrt (1 + t^2) := by
  rw [actualPhaseCenteredOperator_apply, norm_mul, phaseMellinForward_norm, one_mul,
    paretoMellin_one (phaseMellinPoint t) (by rw [phaseMellinPoint_re]; norm_num),
    norm_div, norm_one]
  have hn : ‖phaseMellinPoint t‖^2 = 1 + t^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [phaseMellinPoint] <;> ring
  have hs := congrArg Real.sqrt hn
  rw [Real.sqrt_sq (norm_nonneg _)] at hs
  rw [hs]

/-- Vanishing of the actual conductor symbol extends to the closed physical
single-seed module by continuous linearity. -/
theorem paretoMellin_zero_on_singleSeedClosure_of_symbol
    (b : ℕ) (hb : 0 < b) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hpower : (b : ℂ)^(1-s) = 1)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure ({b} : Set ℕ)) :
    paretoMellin f s = 0 := by
  let L := paretoMellinContinuous s hs
  have hspan : legalSeedSpan ({b} : Set ℕ) ≤ L.ker.map hilbertSequenceLinear := by
    apply Submodule.span_le.2
    rintro g ⟨a, ha, m, hm, rfl⟩
    have haeq : a = b := Set.mem_singleton_iff.mp ha
    subst a
    refine ⟨hilbertDilation m hm (digitHilbert b 1 hb (by omega)), ?_, ?_⟩
    · change paretoMellin _ s = 0
      rw [paretoMellin_generator_zeta b m hb hm s hs hs1, hpower]
      simp
    · exact hilbertDilation_digit_one_sequence b m hb hm
  have hlegal : hilbertLegalSubspace ({b} : Set ℕ) ≤ L.ker := by
    intro g hg
    obtain ⟨v, hv, hvg⟩ := hspan hg
    have he : v = g := hilbertSequence_injective hvg
    exact he ▸ hv
  have hc := Submodule.topologicalClosure_mono hlegal
  rw [L.isClosed_ker.submodule_topologicalClosure_eq] at hc
  exact hc hf

def singleSeedResonance (b m : ℕ) : ℝ := 2 * Real.pi * (m : ℝ) / Real.log (b : ℝ)

theorem singleSeedResonance_pos (b m : ℕ) (hb : 2 ≤ b) (hm : 0 < m) :
    0 < singleSeedResonance b m := by
  have hlog : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  unfold singleSeedResonance
  positivity

theorem singleSeedResonance_symbol (b m : ℕ) (hb : 2 ≤ b) :
    (b : ℂ)^(1 - phaseMellinPoint (singleSeedResonance b m)) = 1 := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hlog : Real.log (b : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < b by omega))).ne'
  have hlogC0 : (Real.log (b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hbC]
  have hlogC : Complex.log (b : ℂ) = (Real.log (b : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hbpos.le).symm
  rw [hlogC]
  have he : (Real.log (b : ℝ) : ℂ) *
      (1 - phaseMellinPoint (singleSeedResonance b m)) =
      ((-(m : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold phaseMellinPoint singleSeedResonance
    push_cast
    rw [hlogC]
    field_simp [hlogC0]
    <;> ring
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I (-(m : ℤ))

/-- All positive arithmetic resonances annihilate the entire closed seed module. -/
theorem actualPhaseCenteredOperator_resonance
    (b : ℕ) (hb : 2 ≤ b) (m : ℕ) (hm : 0 < m)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure ({b} : Set ℕ)) :
    actualPhaseCenteredOperator (singleSeedResonance b m) f = 0 := by
  have ht := singleSeedResonance_pos b m hb hm
  have hs1 : phaseMellinPoint (singleSeedResonance b m) ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp [phaseMellinPoint] at hi
    linarith
  rw [actualPhaseCenteredOperator_apply,
    paretoMellin_zero_on_singleSeedClosure_of_symbol b (by omega) _
      (by rw [phaseMellinPoint_re]; norm_num) hs1
      (singleSeedResonance_symbol b m hb) hf, mul_zero]

end
end RiemannResearch.RH.Pareto.CompressedMellin
