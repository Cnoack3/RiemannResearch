import RiemannResearch.RH.DyadicTentFourierPackets
import RiemannResearch.RH.DyadicFourierAnalyticTargets

/-!
# Actual triadic Abel orbit and normalization comparison Fourier expansions

Source: continuation of the user-provided
`FourierTentContinuationVerification20260910(1).md`, September 11, 2026.
The geometric orbit is absolutely summable at every positive damping. Its
Fourier expansion follows from actual integer boundary samples, with the
binary-residue mean removed exactly. This proves the comparison component
of the signed Fourier bridge. The arithmetic zeta-ratio premise is discharged
in DyadicArithmeticFourierBridge; a bound uniform in vanishing damping remains open.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- The exponential triadic phase is the actual circle Fourier character. -/
theorem dyadicTriadicFourierPhase_eq_fourier (h : ℤ) :
    dyadicTriadicFourierPhase h =
      fourier h ((Real.log 3 / Real.log 2 : ℝ) : UnitAddCircle) := by
  rw [fourier_coe_apply]
  unfold dyadicTriadicFourierPhase dyadicLogFrequency
  push_cast
  congr 1
  ring

@[simp] theorem dyadicTriadicFourierPhase_zero :
    dyadicTriadicFourierPhase 0 = 1 := by
  simp [dyadicTriadicFourierPhase]

/-- All actual triadic phases lie on the unit circle. -/
theorem norm_dyadicTriadicFourierPhase (h : ℤ) :
    ‖dyadicTriadicFourierPhase h‖ = 1 := by
  rw [dyadicTriadicFourierPhase_eq_fourier]
  simp only [fourier_apply, Circle.norm_coe]

/-- The actual Abel denominator is nonzero at every positive damping. -/
theorem dyadicTriadicFourierPhase_abel_denominator_ne_zero
    {ε : ℝ} (hε : 0 < ε) (h : ℤ) :
    1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h ≠ 0 := by
  exact norm_pos_iff.mp (abel_denominator_norm_pos
    (triadicDampingRatio ε) (dyadicTriadicFourierPhase h)
    (triadicDampingRatio_pos ε).le (triadicDampingRatio_lt_one hε)
    (norm_dyadicTriadicFourierPhase h))

/-- Each physical integer `3^(j+1)` contributes its exact triadic phase power. -/
theorem fourier_log_triadic_pow (h : ℤ) (j : ℕ) :
    fourier h ((Real.log ((3 ^ (j + 1) : ℕ) : ℝ) / Real.log 2 : ℝ) :
      UnitAddCircle) = dyadicTriadicFourierPhase h ^ (j + 1) := by
  unfold dyadicTriadicFourierPhase
  rw [← Complex.exp_nat_mul, fourier_coe_apply]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  congr 1
  unfold dyadicLogFrequency
  push_cast
  ring

/-- Exact convergent geometric Fourier kernel for the genuine triadic orbit. -/
theorem triadicDamping_fourier_kernel_hasSum {ε : ℝ}
    (hε : 0 < ε) (h : ℤ) :
    HasSum (fun j : ℕ => (triadicDampingRatio ε ^ j : ℂ) *
      fourier h ((Real.log ((3 ^ (j + 1) : ℕ) : ℝ) / Real.log 2 : ℝ) :
        UnitAddCircle))
      (dyadicTriadicFourierPhase h /
        (1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h)) := by
  have hr : ‖(triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h‖ < 1 := by
    rw [norm_mul, norm_dyadicTriadicFourierPhase, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (triadicDampingRatio_pos ε)]
    exact triadicDampingRatio_lt_one hε
  have hs := (hasSum_geometric_of_norm_lt_one hr).mul_right
    (dyadicTriadicFourierPhase h)
  have hf : (fun j : ℕ => (triadicDampingRatio ε ^ j : ℂ) *
      fourier h ((Real.log ((3 ^ (j + 1) : ℕ) : ℝ) / Real.log 2 : ℝ) :
        UnitAddCircle)) =
      (fun j : ℕ => ((triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h) ^ j *
        dyadicTriadicFourierPhase h) := by
    funext j
    rw [fourier_log_triadic_pow]
    simp only [mul_pow, pow_succ]
    ring
  rw [hf]
  simpa only [div_eq_mul_inv, mul_comm] using hs

/-- Positive damping justifies the full Fourier expansion of the actual Abel step orbit. -/
theorem dyadicStepAbelOrbit_hasSum_fourier {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ((1 - (triadicDampingRatio ε : ℂ)) * dyadicTriadicFourierPhase h /
        (1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h)))
      (dyadicBoundaryCoordinate (dyadicStepAbelOrbit ε) i : ℂ) := by
  have hw : Summable (fun j : ℕ => |triadicDampingRatio ε ^ j|) := by
    simpa only [abs_of_nonneg (pow_nonneg (triadicDampingRatio_pos ε).le _)] using
      triadicDampingRatio_pow_summable hε
  have hs := dyadicBoundaryCoordinate_summable_dilation_packet_hasSum_fourier
    i (fun j : ℕ => 3 ^ (j + 1)) (fun _ => by positivity)
    (fun j => triadicDampingRatio ε ^ j) hw
  have hs' := hs.mul_left (1 - (triadicDampingRatio ε : ℂ))
  simp only [Complex.ofReal_pow] at hs'
  have hseries : (fun h : ℤ => (1 - (triadicDampingRatio ε : ℂ)) *
      (dyadicTentMellinCoefficient i h *
        ∑' j : ℕ, (triadicDampingRatio ε ^ j : ℂ) *
          fourier h ((Real.log ((3 ^ (j + 1) : ℕ) : ℝ) /
            Real.log 2 : ℝ) : UnitAddCircle))) =
      (fun h : ℤ => dyadicTentMellinCoefficient i h *
        ((1 - (triadicDampingRatio ε : ℂ)) * dyadicTriadicFourierPhase h /
          (1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h))) := by
    funext h
    rw [(triadicDamping_fourier_kernel_hasSum hε h).tsum_eq]
    ring
  rw [hseries] at hs'
  have hvalue : (1 - (triadicDampingRatio ε : ℂ)) *
      (∑' j : ℕ, (triadicDampingRatio ε ^ j : ℂ) *
        (dyadicBoundaryCoordinate
          (dyadicProjectedStep (3 ^ (j + 1)) (by positivity)) i : ℂ)) =
      (dyadicBoundaryCoordinate (dyadicStepAbelOrbit ε) i : ℂ) := by
    rw [dyadicStepAbelOrbit_boundaryCoordinate hε]
    push_cast
    rfl
  rwa [hvalue] at hs'

/-- Removing frequency zero retains the exact negative scalar mean. -/
theorem hasSum_dyadicTentMellinCoefficient_nonzero (i : ℕ) :
    HasSum (fun h : DyadicNonzeroFourierFrequency => dyadicTentMellinCoefficient i h.1)
      (-dyadicTentMellinCoefficient i 0) := by
  have hs := (({0} : Finset ℤ).hasSum_iff_compl).mp
    (hasSum_dyadicTentMellinCoefficient_zero i)
  let e : DyadicNonzeroFourierFrequency ≃
      {x : ℤ // x ∉ ({0} : Finset ℤ)} :=
    { toFun := fun h => ⟨h.1, by simpa only [Finset.mem_singleton] using h.2⟩
      invFun := fun h => ⟨h.1, by simpa only [Finset.mem_singleton] using h.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Function.comp_def, e] using e.hasSum_iff.mpr hs

/-- The normalized binary residue contributes exactly the zero Fourier mode. -/
theorem dyadicNormalizationComparison_boundaryCoordinate_fourier_mean
    (ε : ℝ) (i : ℕ) :
    (dyadicBoundaryCoordinate (dyadicNormalizationComparison ε) i : ℂ) =
      dyadicTentMellinCoefficient i 0 -
        (dyadicBoundaryCoordinate (dyadicStepAbelOrbit ε) i : ℂ) := by
  have hl : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [dyadicNormalizationComparison, dyadicBoundaryCoordinate_sub,
    dyadicBoundaryCoordinate_add, dyadicBoundaryCoordinate_smul,
    dyadicBoundaryCoordinate_projection, dyadicBoundaryCoordinate_projection,
    dyadicBoundaryCoordinate_one]
  push_cast
  rw [← log_two_mul_dyadicTentMellinCoefficient_zero]
  field_simp [hl]
  ring

/-- Unconditional provider of the actual comparison component `hk` of the
signed Fourier bridge. Only the arithmetic-family component remains to be supplied. -/
theorem dyadicNormalizationComparison_hasSum_fourier
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    HasSum (fun h : DyadicNonzeroFourierFrequency => dyadicTentMellinCoefficient i h.1 *
      ((1 - (triadicDampingRatio ε : ℂ)) * dyadicTriadicFourierPhase h.1 /
        (1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h.1)))
      (-(dyadicBoundaryCoordinate (dyadicNormalizationComparison ε) i : ℂ)) := by
  have hq : 1 - (triadicDampingRatio ε : ℂ) ≠ 0 := by
    simpa only [dyadicTriadicFourierPhase_zero, mul_one] using
      dyadicTriadicFourierPhase_abel_denominator_ne_zero hε 0
  have hs := (({0} : Finset ℤ).hasSum_iff_compl).mp
    (dyadicStepAbelOrbit_hasSum_fourier hε i)
  have hs' : HasSum
      (fun h : DyadicNonzeroFourierFrequency => dyadicTentMellinCoefficient i h.1 *
        ((1 - (triadicDampingRatio ε : ℂ)) * dyadicTriadicFourierPhase h.1 /
          (1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h.1)))
      ((dyadicBoundaryCoordinate (dyadicStepAbelOrbit ε) i : ℂ) -
        dyadicTentMellinCoefficient i 0) := by
    let e : DyadicNonzeroFourierFrequency ≃
        {x : ℤ // x ∉ ({0} : Finset ℤ)} :=
      { toFun := fun h => ⟨h.1, by simpa only [Finset.mem_singleton] using h.2⟩
        invFun := fun h => ⟨h.1, by simpa only [Finset.mem_singleton] using h.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa [Function.comp_def, e, hq] using e.hasSum_iff.mpr hs
  rw [dyadicNormalizationComparison_boundaryCoordinate_fourier_mean]
  convert hs' using 1
  ring

/-- Conditional research reduction to the sole remaining arithmetic-family
Fourier expansion. The actual phase, Abel denominator, scalar mean and
normalization comparison are supplied by proved provider declarations.
The hypothesis requires the actual zeta-ratio expansion and its convergence.
It is discharged by the downstream DyadicArithmeticFourierBridge module;
this assembly alone does not provide a uniform energy estimate. -/
theorem dyadicSignedFourierBridge_of_regularizedFamily_hasSum
    (hg : ∀ ε : ℝ, 0 < ε → ∀ i : ℕ,
      HasSum (fun h : DyadicNonzeroFourierFrequency =>
        dyadicTentMellinCoefficient i h.1 *
          (((dyadicRegularizationNormalization ε : ℂ) *
              riemannZeta (1 - Complex.I * (dyadicLogFrequency h.1 : ℂ)) /
              riemannZeta (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h.1 : ℂ))) *
            abelCancellationMultiplier (triadicDampingRatio ε)
              (dyadicTriadicFourierPhase h.1)))
        ((dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i : ℂ) -
          dyadicTentMellinCoefficient i 0)) :
    DyadicSignedFourierBridge := by
  intro ε hε i
  have hs := dyadicNormalizationBoundaryCoefficient_hasSum_fourier_of_components
    hε (fun i => dyadicTentMellinCoefficient i 0)
    (fun i (h : DyadicNonzeroFourierFrequency) => dyadicTentMellinCoefficient i h.1)
    (fun h => dyadicTriadicFourierPhase h.1)
    (fun h => (dyadicRegularizationNormalization ε : ℂ) *
      riemannZeta (1 - Complex.I * (dyadicLogFrequency h.1 : ℂ)) /
      riemannZeta (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h.1 : ℂ)))
    (fun h => dyadicTriadicFourierPhase_abel_denominator_ne_zero hε h.1)
    hasSum_dyadicTentMellinCoefficient_nonzero (hg ε hε)
    (dyadicNormalizationComparison_hasSum_fourier hε) i
  change HasSum (fun h => dyadicSignedFourierTerm ε i h) _
  simpa only [dyadicSignedFourierTerm, dyadicSignedFourierMultiplier,
    dyadicSignedZetaRatio, mul_assoc] using hs

end
end RiemannResearch.RH.Pareto
