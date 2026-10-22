import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.ParetoUnscaledDilation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Floor dilations preserve the actual Q legal closure

Source: the user's prime Euler-product and convolution proposal, 13 October
2026. The bounded Q realization is transported through the already verified
equivalence with the full Pareto norm. The exact sequence and residue identities
are retained. The estimate proved here is 2/m on squared norms; it is sufficient
for summable prime operator series and does not assert an RH boundary estimate.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.QFloorDilation
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto

theorem hilbertSequence_q_square_summable (f : ThresholdHilbert) :
    Summable (fun k => positiveQWeight k * (hilbertSequence f k) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _)) _
    ((hilbertSequence_square_summable f).mul_left (2 / zetaTwo))
  intro k
  have hw : positiveQWeight k ≤ (2 / zetaTwo) * positiveWeight k := by
    suffices h : zetaTwo * positiveQWeight k ≤
        zetaTwo * ((2 / zetaTwo) * positiveWeight k) by
      by_contra hn
      exact (not_lt_of_ge h) (mul_lt_mul_of_pos_left (lt_of_not_ge hn) zetaTwo_pos)
    calc
      zetaTwo * positiveQWeight k ≤ 2 * positiveWeight k :=
        zetaTwo_mul_QWeight_le_two_mul_paretoWeight k
      _ = zetaTwo * ((2 / zetaTwo) * positiveWeight k) := by
        field_simp [ne_of_gt zetaTwo_pos]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right hw (sq_nonneg (hilbertSequence f k))

/-- The inverse complete-sequence reencoding from the Pareto Hilbert space. -/
def fromPareto (f : ThresholdHilbert) : QHilbert :=
  encodeQ (hilbertSequence f) (hilbertSequence_q_square_summable f)

@[simp] theorem fromPareto_sequence (f : ThresholdHilbert) :
    qSequence (fromPareto f) = hilbertSequence f :=
  qSequence_encodeQ _ _ (hilbertSequence_zero f)

@[simp] theorem toPareto_fromPareto (f : ThresholdHilbert) :
    toPareto (fromPareto f) = f := by
  apply hilbertSequence_injective
  simp only [toPareto_sequence, fromPareto_sequence]

@[simp] theorem fromPareto_toPareto (f : QHilbert) :
    fromPareto (toPareto f) = f := by
  apply qSequence_injective
  simp only [fromPareto_sequence, toPareto_sequence]

def fromParetoLinear : ThresholdHilbert →ₗ[ℝ] QHilbert where
  toFun := fromPareto
  map_add' f g := by
    apply qSequence_injective
    change qSequence (fromPareto (f + g)) =
      qSequenceLinear (fromPareto f + fromPareto g)
    rw [map_add]
    change qSequence (fromPareto (f + g)) =
      qSequence (fromPareto f) + qSequence (fromPareto g)
    simp only [fromPareto_sequence, hilbertSequence_add]
  map_smul' c f := by
    apply qSequence_injective
    change qSequence (fromPareto (c • f)) =
      qSequenceLinear (c • fromPareto f)
    rw [map_smul]
    change qSequence (fromPareto (c • f)) = c • qSequence (fromPareto f)
    simp only [fromPareto_sequence, hilbertSequence_smul]

theorem fromPareto_norm_sq_le (f : ThresholdHilbert) :
    ‖fromPareto f‖ ^ 2 ≤ (2 / zetaTwo) * ‖f‖ ^ 2 := by
  suffices h : zetaTwo * ‖fromPareto f‖ ^ 2 ≤
      zetaTwo * ((2 / zetaTwo) * ‖f‖ ^ 2) by
    by_contra hn
    exact (not_lt_of_ge h) (mul_lt_mul_of_pos_left (lt_of_not_ge hn) zetaTwo_pos)
  calc
    zetaTwo * ‖fromPareto f‖ ^ 2 ≤ 2 * ‖toPareto (fromPareto f)‖ ^ 2 :=
      zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq _
    _ = zetaTwo * ((2 / zetaTwo) * ‖f‖ ^ 2) := by
      rw [toPareto_fromPareto]
      field_simp [ne_of_gt zetaTwo_pos]

theorem fromPareto_norm_le (f : ThresholdHilbert) :
    ‖fromPareto f‖ ≤ Real.sqrt (2 / zetaTwo) * ‖f‖ := by
  have hZ := zetaTwo_pos
  have hs : ‖fromPareto f‖ ^ 2 ≤
      (Real.sqrt (2 / zetaTwo) * ‖f‖) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / zetaTwo)] using
      fromPareto_norm_sq_le f
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hs

def fromParetoCLM : ThresholdHilbert →L[ℝ] QHilbert :=
  fromParetoLinear.mkContinuous (Real.sqrt (2 / zetaTwo)) fromPareto_norm_le

@[simp] theorem fromParetoCLM_apply (f : ThresholdHilbert) :
    fromParetoCLM f = fromPareto f := rfl

/-- Actual unscaled floor dilation, (T_m f)(n) = f(floor(n/m)). -/
def floorDilation (m : ℕ) (hm : 0 < m) : QHilbert →L[ℝ] QHilbert :=
  (1 / (m : ℝ)) •
    (fromParetoCLM.comp ((hilbertDilationContinuous m hm).comp toParetoCLM))

@[simp] theorem floorDilation_sequence (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    qSequence (floorDilation m hm f) = fun n => qSequence f (n / m) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  change qSequenceLinear ((1 / (m : ℝ)) •
    fromPareto (hilbertDilation m hm (toPareto f))) = _
  rw [map_smul]
  change (1 / (m : ℝ)) •
    qSequence (fromPareto (hilbertDilation m hm (toPareto f))) = _
  rw [fromPareto_sequence, hilbertDilation_sequence, toPareto_sequence]
  funext n
  simp only [Pi.smul_apply, smul_eq_mul, dilation]
  field_simp [hm0]

theorem toPareto_floorDilation (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    toPareto (floorDilation m hm f) =
      (1 / (m : ℝ)) • hilbertDilation m hm (toPareto f) := by
  apply hilbertSequence_injective
  rw [toPareto_sequence, floorDilation_sequence, hilbertSequence_smul,
    hilbertDilation_sequence, toPareto_sequence]
  funext n
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  simp only [Pi.smul_apply, smul_eq_mul, dilation]
  field_simp [hm0]

/-- Complete Q norm control; the factor two is from equivalent full weights. -/
theorem floorDilation_norm_sq_le (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    ‖floorDilation m hm f‖ ^ 2 ≤ (2 / (m : ℝ)) * ‖f‖ ^ 2 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hp : ‖toPareto (floorDilation m hm f)‖ ^ 2 =
      (1 / (m : ℝ)) * ‖toPareto f‖ ^ 2 := by
    rw [toPareto_floorDilation, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)),
      mul_pow, hilbertDilation_norm_sq]
    field_simp [ne_of_gt hmR]
  suffices h : zetaTwo * ‖floorDilation m hm f‖ ^ 2 ≤
      zetaTwo * ((2 / (m : ℝ)) * ‖f‖ ^ 2) by
    by_contra hn
    exact (not_lt_of_ge h) (mul_lt_mul_of_pos_left (lt_of_not_ge hn) zetaTwo_pos)
  calc
    zetaTwo * ‖floorDilation m hm f‖ ^ 2 ≤
        2 * ‖toPareto (floorDilation m hm f)‖ ^ 2 :=
      zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq _
    _ = (2 / (m : ℝ)) * ‖toPareto f‖ ^ 2 := by rw [hp]; ring
    _ ≤ (2 / (m : ℝ)) * (zetaTwo * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (toPareto_norm_sq_le f) (by positivity)
    _ = zetaTwo * ((2 / (m : ℝ)) * ‖f‖ ^ 2) := by ring

theorem floorDilation_norm_le (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    ‖floorDilation m hm f‖ ≤ Real.sqrt (2 / (m : ℝ)) * ‖f‖ := by
  have hs : ‖floorDilation m hm f‖ ^ 2 ≤
      (Real.sqrt (2 / (m : ℝ)) * ‖f‖) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / (m : ℝ))]
      using floorDilation_norm_sq_le m hm f
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hs

theorem floorDilation_opNorm_le (m : ℕ) (hm : 0 < m) :
    ‖floorDilation m hm‖ ≤ Real.sqrt (2 / (m : ℝ)) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (floorDilation_norm_le m hm)

theorem floorDilation_comp (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (floorDilation m hm).comp (floorDilation n hn) =
      floorDilation (m * n) (Nat.mul_pos hm hn) := by
  apply ContinuousLinearMap.ext
  intro f
  apply qSequence_injective
  simp only [ContinuousLinearMap.comp_apply, floorDilation_sequence,
    Nat.div_div_eq_div_mul]

@[simp] theorem floorDilation_one :
    floorDilation 1 Nat.zero_lt_one = ContinuousLinearMap.id ℝ QHilbert := by
  apply ContinuousLinearMap.ext
  intro f
  apply qSequence_injective
  simp only [floorDilation_sequence, ContinuousLinearMap.id_apply, Nat.div_one]

/-- The arithmetic identity is exact, for every positive pair of conductors. -/
theorem floorDilation_qResidue (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    floorDilation m hm (qResidue d) =
      qResidue (m * d) - (1 / (d : ℝ)) • qResidue m := by
  apply qSequence_injective
  rw [floorDilation_sequence]
  change (fun n => qSequence (qResidue d) (n / m)) =
    qSequenceLinear (qResidue (m * d) - (1 / (d : ℝ)) • qResidue m)
  rw [map_sub, map_smul]
  change (fun n => qSequence (qResidue d) (n / m)) =
    qSequence (qResidue (m * d)) - (1 / (d : ℝ)) • qSequence (qResidue m)
  simp_rw [qSequence_qResidue]
  funext n
  have h := unscaledDilation_normalizedAtom m d n hm hd
  simpa only [unscaledDilation, normalizedAtom, Pareto.residue,
    ArithmeticCumulative.residueFraction, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using h

theorem qResidue_mem_legalSpan (d : ℕ) (hd : 0 < d) :
    qResidue d ∈ QFullResidueProjection.legalSpan := by
  by_cases h1 : d = 1
  · rw [h1, qResidue_one]
    exact Submodule.zero_mem _
  · apply Submodule.subset_span
    refine ⟨d - 2, ?_⟩
    have he : d - 2 + 2 = d := by omega
    change qResidue (d - 2 + 2) = qResidue d
    rw [he]

theorem floorDilation_mem_legalSpan (m : ℕ) (hm : 0 < m)
    (f : QHilbert) (hf : f ∈ QFullResidueProjection.legalSpan) :
    floorDilation m hm f ∈ QFullResidueProjection.legalSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      rw [floorDilation_qResidue m (i + 2) hm (by omega)]
      exact QFullResidueProjection.legalSpan.sub_mem
        (qResidue_mem_legalSpan _ (Nat.mul_pos hm (by omega)))
        (QFullResidueProjection.legalSpan.smul_mem _ (qResidue_mem_legalSpan m hm))
  | zero => simpa only [map_zero] using QFullResidueProjection.legalSpan.zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact QFullResidueProjection.legalSpan.add_mem ihx ihy
  | smul c x hx ihx =>
      rw [map_smul]
      exact QFullResidueProjection.legalSpan.smul_mem c ihx

theorem floorDilation_mem_legalClosure (m : ℕ) (hm : 0 < m)
    (f : QHilbert) (hf : f ∈ QFullResidueProjection.closure) :
    floorDilation m hm f ∈ QFullResidueProjection.closure := by
  let K := QFullResidueProjection.closure.comap (floorDilation m hm).toLinearMap
  have hs : QFullResidueProjection.legalSpan ≤ K := by
    intro x hx
    exact QFullResidueProjection.legalSpan.le_topologicalClosure
      (floorDilation_mem_legalSpan m hm x hx)
  have hclosed : IsClosed (K : Set QHilbert) :=
    (show IsClosed (QFullResidueProjection.closure : Set QHilbert) from
      isClosed_closure).preimage (floorDilation m hm).continuous
  exact (closure_minimal hs hclosed) hf

end RiemannResearch.RH.QFloorDilation
