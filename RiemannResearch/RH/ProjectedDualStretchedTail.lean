import RiemannResearch.RH.CanonicalMobiusStretchedCorrection
import RiemannResearch.RH.ResidueProjectionCorrectionTail
import RiemannResearch.RH.ParetoDyadicShellCriterion

/-!
# Quantitative moving projected-dual tails and the dyadic signed-gain criterion

Source: user-requested continuation of commit 37b70ace, 28 September 2026.
The arguments combine the repository's complete stretched canonical energy,
exact projected-dual pairing, inverse Gram identities, and dyadic telescope.
No external analytic theorem or novelty claim is introduced.

Established: an exact inverse-diagonal minus physical-head formula; a complete
tail bound by the squared l1 mass of the actual inverse Gram column divided
by n+1; its orthonormal Bessel representation; and a necessary stretched
tail-divergence obstruction for every nonzero limiting coefficient correction.

CONDITIONAL RESEARCH REDUCTIONS: at the arithmetic provider exponent a,
cofinal smallness of n*exp(-a*Phi(n))*projectedDualTailEnergy n d for each
fixed d>1 forces zero limiting residual and hence every cumulative signed
shell gain is zero. At any b<a, cofinal boundedness suffices. The cofinal
indices and constants may depend on d. Neither tail-rate provider, nor the
sufficient sub-stretched inverse-column mass bound, is proved here.
The existing qualitative dual-tail convergence and mode summability do
not supply a quantitative rate. RH remains open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis
open GramMobiusCorrection

/-- Exact cancellation needed beyond a bounded inverse diagonal: subtract the
complete physical head from the full projected-dual energy. -/
theorem projectedDualTailEnergy_eq_inverse_diagonal_sub_head (n : ℕ) (i : Fin n) :
    projectedDualTailEnergy n (i.val + 2) =
      residueInverseEntry n i i -
        ∑ k ∈ Finset.range n,
          (((finiteSpace n).starProjection (coefficientDual i.val)) k) ^ 2 := by
  rw [projectedDualTailEnergy, hilbertTailShift_norm_sq,
    residueInverseEntry_projection, real_inner_self_eq_norm_sq]
  rfl

/-- A nonzero fixed correction limit forces divergence at every strictly
smaller stretched exponent. This is a lower obstruction, not an upper rate. -/
theorem projectedDualTail_stretched_barrier_of_nonzero_correction
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (b : ℝ) (hba : b < a) (d : ℕ) (hd : 1 < d)
    (hne : mobiusDifferenceCLM d limitResidual ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
        projectedDualTailEnergy n d) atTop atTop := by
  let L := mobiusDifferenceCLM d limitResidual
  let φ : ℕ → ℝ := fun n => logProductPower (1 / 11) (6 + Real.log (n : ℝ))
  have hL : 0 < L ^ 2 := sq_pos_of_ne_zero hne
  have hcorr : ∀ᶠ n : ℕ in atTop, L ^ 2 / 2 < (correction n d) ^ 2 :=
    ((correction_tendsto_residual d (by omega)).pow 2).eventually_const_lt (by
      change L ^ 2 / 2 < L ^ 2
      linarith)
  have hφ : Tendsto φ atTop atTop :=
    (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp
      (tendsto_atTop_add_const_left atTop 6
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have heps : Tendsto (fun n => Real.exp (-(a - b) * φ n)) atTop (𝓝 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr
      (hφ.const_mul_atTop_of_neg (by linarith))
  have hsmall : Tendsto (fun n => C * Real.exp (-(a - b) * φ n)) atTop (𝓝 0) := by
    simpa using heps.const_mul C
  have htail : Tendsto (fun n => 8 * projectedDualTailEnergy n d) atTop (𝓝 0) := by
    simpa using (projectedDualTailEnergy_tendsto_zero d).const_mul 8
  apply tendsto_atTop_of_pos_le_add_mul_tendsto_zero
    (by linarith : 0 < L ^ 2 / 2) htail
    (Eventually.of_forall (fun n => mul_nonneg hC (Real.exp_pos _).le)) hsmall
  filter_upwards [henergy, hcorr, eventually_ge_atTop d] with n hen hcn hdn
  have hprod := correction_sq_le_tail_product n d hd hdn
  have hbound := mul_le_mul_of_nonneg_right hen
    (sq_nonneg ‖hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) n‖)
  have hexp : Real.exp (-b * φ n) * Real.exp (-(a - b) * φ n) =
      Real.exp (-a * φ n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    L ^ 2 / 2 ≤ (8 + C * (n : ℝ) * Real.exp (-a * φ n)) *
        projectedDualTailEnergy n d := hcn.le.trans (hprod.trans hbound)
    _ = 8 * projectedDualTailEnergy n d +
        ((n : ℝ) * Real.exp (-b * φ n) * projectedDualTailEnergy n d) *
          (C * Real.exp (-(a - b) * φ n)) := by
      rw [← hexp]
      ring

/-- Endpoint reduction: only arbitrarily small cofinal weighted dual tails
are required, not convergence of the entire weighted sequence. Provider Open. -/
theorem correction_limit_eq_zero_of_cofinally_small_stretched_dual_tail
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (d : ℕ) (hd : 1 < d)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
        projectedDualTailEnergy n d < ε) :
    mobiusDifferenceCLM d limitResidual = 0 := by
  by_contra hne
  let L := mobiusDifferenceCLM d limitResidual
  have hL : 0 < L ^ 2 := sq_pos_of_ne_zero hne
  have hden : 0 < 4 * (C + 1) := by linarith
  have hcorr : ∀ᶠ n : ℕ in atTop, L ^ 2 / 2 < (correction n d) ^ 2 :=
    ((correction_tendsto_residual d (by omega)).pow 2).eventually_const_lt (by
      change L ^ 2 / 2 < L ^ 2
      linarith)
  have htail : ∀ᶠ n : ℕ in atTop, projectedDualTailEnergy n d < L ^ 2 / 32 :=
    (projectedDualTailEnergy_tendsto_zero d).eventually_lt_const (by positivity)
  obtain ⟨n, hsn, hen, hcn, htn, hdn⟩ :=
    ((hsmall (L ^ 2 / (4 * (C + 1))) (div_pos hL hden)).and_eventually
      (henergy.and (hcorr.and (htail.and (eventually_ge_atTop d))))).exists
  let X := (n : ℝ) *
    Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
      projectedDualTailEnergy n d
  have hX : 0 ≤ X :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le) (sq_nonneg _)
  have hXs : X * (4 * (C + 1)) < L ^ 2 := (lt_div_iff₀ hden).mp hsn
  have hbound : (correction n d) ^ 2 ≤ 8 * projectedDualTailEnergy n d + C * X := by
    calc
      _ ≤ ‖tailError n‖ ^ 2 * projectedDualTailEnergy n d :=
        correction_sq_le_tail_product n d hd hdn
      _ ≤ (8 + C * (n : ℝ) *
          Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))) *
            projectedDualTailEnergy n d :=
        mul_le_mul_of_nonneg_right hen (sq_nonneg _)
      _ = _ := by dsimp [X]; ring
  nlinarith

/-- A strict margin in the stretched exponent weakens cofinal smallness to
cofinal boundedness. The bound remains an explicit open hypothesis. -/
theorem correction_limit_eq_zero_of_frequently_bounded_stretched_dual_tail
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (b : ℝ) (hba : b < a) (d : ℕ) (hd : 1 < d) (K : ℝ)
    (hbound : ∃ᶠ n : ℕ in atTop, (n : ℝ) *
      Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
        projectedDualTailEnergy n d ≤ K) :
    mobiusDifferenceCLM d limitResidual = 0 := by
  by_contra hne
  have ht := projectedDualTail_stretched_barrier_of_nonzero_correction
    hC henergy b hba d hd hne
  obtain ⟨n, hn, hn'⟩ := (hbound.and_eventually (ht.eventually_gt_atTop K)).exists
  linarith

private theorem limitResidual_eq_zero_of_correction_limit_zero
    (hzero : ∀ d : ℕ, 1 < d → mobiusDifferenceCLM d limitResidual = 0) :
    limitResidual = 0 := by
  apply limitResidual_zero_iff_energy_zero.mpr
  apply limitEnergy_zero_iff_mem.mpr
  apply projection_norm_tendsto_zero_iff_mem.mp
  apply correction_limits_iff_norm.mp
  intro d hd
  simpa only [hzero d hd] using correction_tendsto_residual d (by omega)

private theorem cumulative_signed_gain_eq_zero_of_residual_zero
    (hz : limitResidual = 0) (w : ℕ → ℝ) (N K : ℕ) :
    (∑ j ∈ Finset.range K, residualWeightedShellGain w (2 ^ j * N)) = 0 := by
  have ht (n : ℕ) : residualTailEnergy n = 0 := by
    have hs : hilbertTailShift limitResidual n = 0 := by
      ext i
      simp [hilbertTailShift, hz]
    simp [residualTailEnergy, hs]
  have he := residual_weighted_dyadic_telescope w N K
  simp only [ht, mul_zero, zero_sub] at he
  linarith

/-- The checked arithmetic exponent supports both quantitative projection
criteria. Either open provider forces the residual to vanish, connecting
to the exact cumulative signed gains for every weight and dyadic orbit.
There is no common-subsequence assumption across coefficient indices. -/
theorem exists_projectedDual_stretched_shell_bridge :
    ∃ a : ℝ, 0 < a ∧
      (((∀ d : ℕ, 1 < d → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
        (n : ℝ) * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
          projectedDualTailEnergy n d < ε) →
        limitResidual = 0 ∧ ∀ (w : ℕ → ℝ) (N K : ℕ),
          (∑ j ∈ Finset.range K, residualWeightedShellGain w (2 ^ j * N)) = 0) ∧
      (∀ b : ℝ, b < a →
        (∀ d : ℕ, 1 < d → ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
          (n : ℝ) * Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
            projectedDualTailEnergy n d ≤ K) →
        limitResidual = 0 ∧ ∀ (w : ℕ → ℝ) (N K : ℕ),
          (∑ j ∈ Finset.range K, residualWeightedShellGain w (2 ^ j * N)) = 0)) := by
  obtain ⟨a, ha, C, hC, he⟩ := canonicalMobiusResidual_eventual_stretched_energy
  have henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) := he
  refine ⟨a, ha, ?_, ?_⟩
  · intro hsmall
    have hz := limitResidual_eq_zero_of_correction_limit_zero (fun d hd =>
      correction_limit_eq_zero_of_cofinally_small_stretched_dual_tail
        hC henergy d hd (hsmall d hd))
    exact ⟨hz, cumulative_signed_gain_eq_zero_of_residual_zero hz⟩
  · intro b hba hbound
    have hz : limitResidual = 0 := by
      apply limitResidual_eq_zero_of_correction_limit_zero
      intro d hd
      obtain ⟨K, hK⟩ := hbound d hd
      exact correction_limit_eq_zero_of_frequently_bounded_stretched_dual_tail
        hC henergy b hba d hd K hK
    exact ⟨hz, cumulative_signed_gain_eq_zero_of_residual_zero hz⟩

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
/-- The complete physical tail of any finite legal combination, with its
actual coefficient mass. No boundedness of that mass is assumed. -/
theorem finite_residue_tail_energy_le_coefficient_mass (m n : ℕ) (a : Fin m → ℝ) :
    ‖hilbertTailShift (∑ i : Fin m, a i • residueAtom i.val) n‖ ^ 2 ≤
      (∑ i : Fin m, |a i|) ^ 2 / ((n : ℝ) + 1) := by
  let B : ℝ := ∑ i : Fin m, |a i|
  let R : ℝ := Real.sqrt (1 / ((n : ℝ) + 1))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 1 / ((n : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have ha (i : Fin m) : ‖hilbertTailShift (residueAtom i.val) n‖ ≤ R := by
    have h := residueAtom_tail_norm_sq_le i.val n
    nlinarith [norm_nonneg (hilbertTailShift (residueAtom i.val) n)]
  have he : hilbertTailShift (∑ i : Fin m, a i • residueAtom i.val) n =
      ∑ i : Fin m, a i • hilbertTailShift (residueAtom i.val) n := by
    change hilbertTailShiftLinear n (∑ i : Fin m, a i • residueAtom i.val) =
      ∑ i : Fin m, a i • hilbertTailShiftLinear n (residueAtom i.val)
    simp only [map_sum, map_smul]
  have hnorm : ‖hilbertTailShift (∑ i : Fin m, a i • residueAtom i.val) n‖ ≤ B * R := by
    rw [he]
    calc
      _ ≤ ∑ i : Fin m, ‖a i • hilbertTailShift (residueAtom i.val) n‖ := norm_sum_le _ _
      _ = ∑ i : Fin m, |a i| * ‖hilbertTailShift (residueAtom i.val) n‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin m, |a i| * R :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _))
      _ = B * R := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ (B * R) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB hR)).mpr hnorm
    _ = B ^ 2 / ((n : ℝ) + 1) := by rw [mul_pow, hR2]; ring

namespace CorrectionTail
/-- The total absolute coefficient mass of the actual projected Riesz dual. -/
def projectedDualCoefficientMass (n d : ℕ) : ℝ :=
  ∑ i : Fin n, |coefficientCLM (i.val + 2)
    ((finiteSpace n).starProjection (coefficientRiesz d))|

theorem projectedDualTailEnergy_le_coefficient_mass (n d : ℕ) :
    projectedDualTailEnergy n d ≤
      (projectedDualCoefficientMass n d) ^ 2 / ((n : ℝ) + 1) := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion n
    ((finiteSpace n).starProjection (coefficientRiesz d))
    ((finiteSpace n).starProjection_apply_mem _)
  have hc (i : Fin n) : coefficientCLM (i.val + 2)
      ((finiteSpace n).starProjection (coefficientRiesz d)) = a i := by
    rw [ha, coefficient_finite_sum]
  unfold projectedDualTailEnergy projectedDualCoefficientMass
  simp only [hc]
  rw [ha]
  exact finite_residue_tail_energy_le_coefficient_mass n n a
end CorrectionTail
end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
theorem projectedDualCoefficientMass_eq_inverse_column (n : ℕ) (i : Fin n) :
    projectedDualCoefficientMass n (i.val + 2) =
      ∑ k : Fin n, |residueInverseEntry n k i| := by
  unfold projectedDualCoefficientMass
  change (∑ k : Fin n, |coefficientCLM (k.val + 2)
    ((finiteSpace n).starProjection (coefficientDual i.val))|) = _
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [← GramMobiusCorrection.coefficientDual_inner]
  calc
    inner ℝ ((finiteSpace n).starProjection (coefficientDual i.val)) (coefficientDual k.val) =
        inner ℝ ((finiteSpace n).starProjection (coefficientDual i.val))
          ((finiteSpace n).starProjection (coefficientDual k.val)) := by
      symm
      rw [← (finiteSpace n).inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr ((finiteSpace n).starProjection_apply_mem _)]
    _ = residueInverseEntry n k i := by
      rw [residueInverseEntry_projection, real_inner_comm]
end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis
/-- The coefficient-mass estimate pays the complete moving physical tail.
It does not assert that the mass itself grows slowly. -/
theorem stretched_projectedDualTailEnergy_le_coefficient_mass (a : ℝ) (n d : ℕ) :
    (n : ℝ) * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
      projectedDualTailEnergy n d ≤
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
          (projectedDualCoefficientMass n d) ^ 2 := by
  let e := Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hr : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).mpr (by linarith)
  calc
    (n : ℝ) * e * projectedDualTailEnergy n d ≤
        (n : ℝ) * e * ((projectedDualCoefficientMass n d) ^ 2 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (projectedDualTailEnergy_le_coefficient_mass n d)
        (mul_nonneg (Nat.cast_nonneg n) he)
    _ = (e * (projectedDualCoefficientMass n d) ^ 2) * ((n : ℝ) / ((n : ℝ) + 1)) := by ring
    _ ≤ (e * (projectedDualCoefficientMass n d) ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg he (sq_nonneg _))
    _ = _ := mul_one _

/-- A concrete sufficient projection estimate: each fixed dual's coefficient
mass has cofinal stretched growth with a strict exponent margin. This provider
remains Open, and the cofinal indices may depend on the fixed dual. -/
theorem limitResidual_eq_zero_of_cofinal_stretched_coefficient_mass
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (b : ℝ) (hba : b < a)
    (hmass : ∀ d : ℕ, 1 < d → ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
      Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
        (projectedDualCoefficientMass n d) ^ 2 ≤ K) :
    limitResidual = 0 := by
  apply limitResidual_eq_zero_of_correction_limit_zero
  intro d hd
  obtain ⟨K, hK⟩ := hmass d hd
  apply correction_limit_eq_zero_of_frequently_bounded_stretched_dual_tail
    hC henergy b hba d hd K
  exact hK.mono (fun n hn => (stretched_projectedDualTailEnergy_le_coefficient_mass b n d).trans hn)
end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
/-- The inverse diagonal is exactly the finite Bessel sum of coefficient modes.
Together with the physical-head subtraction, this records the two distinct
coordinate systems; mode summability alone supplies no physical-tail rate. -/
theorem inverse_diagonal_eq_modeCoefficient_sq_sum (n : ℕ) (i : Fin n) :
    residueInverseEntry n i i =
      ∑ j : Fin n, (modeCoefficient (i.val + 2) j.val) ^ 2 := by
  have hn : Orthonormal ℝ (fun j : Fin n => residueMode j.val) :=
    residueMode_orthonormal.comp (fun j : Fin n => j.val) Fin.val_injective
  have he := RiemannResearch.Analysis.FiniteHilbertGram.projection_error_eq_orthonormal_sum
    hn (coefficientDual i.val)
  simp only [residueMode_finiteSpace] at he
  simp only [GramMobiusCorrection.coefficientDual_inner] at he
  unfold modeCoefficient
  have hd := residueInverseEntry_diagonal n i
  linarith

/-- The checked arithmetic provider makes the obstruction uniform in the
fixed coefficient index. It is a necessary-growth theorem conditional on
a nonzero correction limit, not a decay estimate. -/
theorem exists_projectedDual_stretched_barrier :
    ∃ a : ℝ, 0 < a ∧ ∀ b : ℝ, b < a → ∀ d : ℕ, 1 < d →
      mobiusDifferenceCLM d limitResidual ≠ 0 →
      Tendsto (fun n : ℕ => (n : ℝ) *
        Real.exp (-b * RiemannResearch.Analysis.logProductPower (1 / 11)
          (6 + Real.log (n : ℝ))) * projectedDualTailEnergy n d) atTop atTop := by
  obtain ⟨a, ha, C, hC, he⟩ := canonicalMobiusResidual_eventual_stretched_energy
  exact ⟨a, ha, fun b hb d hd hne =>
    projectedDualTail_stretched_barrier_of_nonzero_correction hC he b hb d hd hne⟩
end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis
open GramMobiusCorrection
/-- Unconditional full correction bound retaining the actual inverse-column
mass. An upper bound on that mass is not asserted. -/
theorem correction_eventual_stretched_coefficient_mass_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ d : ℕ, 1 < d → d ≤ n →
        (correction n d) ^ 2 ≤
          (8 / ((n : ℝ) + 1) + C *
            Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))) *
              (projectedDualCoefficientMass n d) ^ 2 := by
  obtain ⟨a, ha, C, hC, he⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, C, hC, ?_⟩
  filter_upwards [he] with n hn
  intro d hd hdn
  calc
    (correction n d) ^ 2 ≤ ‖tailError n‖ ^ 2 * projectedDualTailEnergy n d :=
      correction_sq_le_tail_product n d hd hdn
    _ ≤ (8 + C * (n : ℝ) *
          Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))) *
            projectedDualTailEnergy n d :=
      mul_le_mul_of_nonneg_right hn (sq_nonneg _)
    _ = 8 * projectedDualTailEnergy n d + C *
          ((n : ℝ) * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
            projectedDualTailEnergy n d) := by ring
    _ ≤ 8 * ((projectedDualCoefficientMass n d) ^ 2 / ((n : ℝ) + 1)) +
          C * (Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
            (projectedDualCoefficientMass n d) ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (projectedDualTailEnergy_le_coefficient_mass n d) (by norm_num))
        (mul_le_mul_of_nonneg_left
          (stretched_projectedDualTailEnergy_le_coefficient_mass a n d) hC)
    _ = _ := by ring
end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
