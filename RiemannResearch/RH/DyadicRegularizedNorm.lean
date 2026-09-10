import Mathlib.Analysis.PSeries
import RiemannResearch.RH.ThresholdHilbertProjection
import RiemannResearch.RH.ParetoSequenceCertificates
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith

/-!
# Dyadic quotient geometry and the vanishing-damping norm assembly

Source: user-provided `norm_obligation_proved.md`, equations (N6), (N24),
(N30), and Section 7, September 10, 2026.

The dyadic quotient projection below is constructed in the actual weighted
Hilbert space. Its fixed-adjoint characterization and dilation norm estimate
are unconditional. The final assembly theorem is a **conditional research
reduction**: the exact arithmetic decomposition and its uniform Abel-orbit and
remainder estimates are explicit hypotheses. This file does not claim to
provide those analytic estimates. The arithmetic regularization and its finite
rectangular approximants are defined concretely below.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
noncomputable section

/-- Actual range of `I - T₂`; its orthogonal complement is the dyadic quotient. -/
def dyadicDifferenceRange : Submodule ℝ ThresholdHilbert :=
  (ContinuousLinearMap.id ℝ ThresholdHilbert -
    hilbertDilationContinuous 2 (by norm_num)).range

/-- The actual quotient, represented by minimum-norm orthogonal representatives. -/
def dyadicQuotientSubspace : Submodule ℝ ThresholdHilbert :=
  dyadicDifferenceRangeᗮ

instance dyadicQuotientSubspace_hasOrthogonalProjection :
    dyadicQuotientSubspace.HasOrthogonalProjection := by
  unfold dyadicQuotientSubspace
  infer_instance

/-- The genuine bounded orthogonal projection used by the regularization. -/
def dyadicQuotientProjection : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  dyadicQuotientSubspace.starProjection

private theorem residue_weighted_square_summable (a : ℕ) (ha : 0 < a) :
    Summable (fun k => positiveWeight k * residue a k ^ 2) := by
  have hb := bounded_product (fun k => residue_abs_le a k ha)
    (fun k => residue_abs_le a k ha)
  simpa only [pow_two] using weighted_summable_of_bounded hb

/-- An actual residue vector in the weighted complete Hilbert space. -/
def hilbertResidue (a : ℕ) (ha : 0 < a) : ThresholdHilbert :=
  sequenceHilbert (residue a) (residue_weighted_square_summable a ha)

@[simp] theorem hilbertResidue_sequence (a : ℕ) (ha : 0 < a) :
    hilbertSequence (hilbertResidue a ha) = residue a := by
  apply hilbertSequence_sequenceHilbert
  simp [residue]

/-- The real damping ratio `3^(-ε)`. -/
def triadicDampingRatio (ε : ℝ) : ℝ := (3 : ℝ) ^ (-ε)

/-- The real Dirichlet series for `ζ(1+ε)`, with index zero excluded.
As for every `tsum`, its intended series interpretation requires summability. -/
def regularizationZetaSeries (ε : ℝ) : ℝ :=
  ∑' n : ℕ, (n + 1 : ℝ) ^ (-(1 + ε))

def dyadicRegularizationNormalization (ε : ℝ) : ℝ :=
  regularizationZetaSeries ε * (1 - triadicDampingRatio ε) / Real.log 3

def dyadicRegularizationCoefficient (ε : ℝ) (m j : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (m + 1) : ℝ) /
    (m + 1 : ℝ) ^ (1 + ε) * triadicDampingRatio ε ^ j

/-- A single actual projected term of (N1), with physical Möbius index `m+1`. -/
def dyadicRegularizedTerm (ε : ℝ) (p : ℕ × ℕ) : ThresholdHilbert :=
  dyadicRegularizationCoefficient ε p.1 p.2 •
    dyadicQuotientProjection
      (hilbertDilation ((p.1 + 1) * 3 ^ p.2) (by positivity)
        (hilbertResidue 3 (by norm_num)))

/-- The concrete `G_{ε,1}` from (N1), defined by the projected product-index
series. It makes no assertion that an unprojected infinite sum lies in H. -/
def dyadicRegularizedFamily (ε : ℝ) : ThresholdHilbert :=
  dyadicRegularizationNormalization ε • ∑' p : ℕ × ℕ, dyadicRegularizedTerm ε p

/-- A genuine finite rectangular raw lift, before applying the quotient. -/
def dyadicRegularizedRawRectangle (ε : ℝ) (M J : ℕ) : ThresholdHilbert :=
  dyadicRegularizationNormalization ε •
    ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
      dyadicRegularizationCoefficient ε m j •
        hilbertDilation ((m + 1) * 3 ^ j) (by positivity)
          (hilbertResidue 3 (by norm_num))

def dyadicRegularizedRectangle (ε : ℝ) (M J : ℕ) : ThresholdHilbert :=
  dyadicQuotientProjection (dyadicRegularizedRawRectangle ε M J)

theorem dyadicRegularizedRectangle_eq_sum (ε : ℝ) (M J : ℕ) :
    dyadicRegularizedRectangle ε M J =
      dyadicRegularizationNormalization ε •
        ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J, dyadicRegularizedTerm ε (m, j) := by
  simp only [dyadicRegularizedRectangle, dyadicRegularizedRawRectangle,
    map_smul, map_sum, dyadicRegularizedTerm]

/-- The series obligations are separate from the uniform norm obligation.
In particular a default value of an unsummable `tsum` cannot count as proof
of the proposed arithmetic result. -/
def DyadicRegularizedSeriesSummable : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ (-(1 + ε))) ∧
    Summable (dyadicRegularizedTerm ε)

/-- The precise base norm obligation, stated for the concrete arithmetic
family. This is a proposition definition, not an axiom or a proved theorem. -/
def DyadicRegularizedNormBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    ‖dyadicRegularizedFamily ε‖ ^ 2 ≤ C

/-- The concrete step Abel orbit in (N24), defined entirely within QH. -/
def dyadicStepAbelOrbit (ε : ℝ) : ThresholdHilbert :=
  (1 - triadicDampingRatio ε) •
    ∑' j : ℕ, triadicDampingRatio ε ^ j •
      dyadicQuotientProjection
        (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne)

theorem mem_dyadicQuotientSubspace_iff (f : ThresholdHilbert) :
    f ∈ dyadicQuotientSubspace ↔
      hilbertDilationAdjoint 2 (by norm_num) f = f := by
  constructor
  · intro hf
    apply ext_inner_left ℝ
    intro x
    have hx : x - hilbertDilation 2 (by norm_num) x ∈ dyadicDifferenceRange :=
      ⟨x, rfl⟩
    have hz := (dyadicDifferenceRange.mem_orthogonal f).1 hf
      (x - hilbertDilation 2 (by norm_num) x) hx
    rw [inner_sub_left] at hz
    have ha := ContinuousLinearMap.adjoint_inner_right
      (hilbertDilationContinuous 2 (by norm_num)) x f
    change inner ℝ x (hilbertDilationAdjoint 2 (by norm_num) f) =
      inner ℝ (hilbertDilation 2 (by norm_num) x) f at ha
    exact ha.trans (sub_eq_zero.mp hz).symm
  · intro hf
    apply (dyadicDifferenceRange.mem_orthogonal f).2
    rintro u ⟨x, rfl⟩
    change inner ℝ (x - hilbertDilation 2 (by norm_num) x) f = 0
    rw [inner_sub_left]
    have ha := ContinuousLinearMap.adjoint_inner_right
      (hilbertDilationContinuous 2 (by norm_num)) x f
    change inner ℝ x (hilbertDilationAdjoint 2 (by norm_num) f) =
      inner ℝ (hilbertDilation 2 (by norm_num) x) f at ha
    rw [hf] at ha
    exact sub_eq_zero.mpr ha

theorem dyadicQuotientProjection_mem (f : ThresholdHilbert) :
    dyadicQuotientProjection f ∈ dyadicQuotientSubspace :=
  Submodule.starProjection_apply_mem _ _

theorem dyadicQuotientProjection_fixed (f : ThresholdHilbert) :
    hilbertDilationAdjoint 2 (by norm_num) (dyadicQuotientProjection f) =
      dyadicQuotientProjection f :=
  (mem_dyadicQuotientSubspace_iff _).mp (dyadicQuotientProjection_mem f)

theorem dyadicQuotientProjection_idempotent (f : ThresholdHilbert) :
    dyadicQuotientProjection (dyadicQuotientProjection f) =
      dyadicQuotientProjection f :=
  Submodule.starProjection_eq_self_iff.mpr (dyadicQuotientProjection_mem f)

theorem dyadicQuotientProjection_norm_le (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection f‖ ≤ ‖f‖ :=
  Submodule.norm_starProjection_apply_le _ _

/-- Exact quotient energy plus complementary energy; no mixed term is omitted. -/
theorem dyadicQuotientProjection_pythagoras (f : ThresholdHilbert) :
    ‖f‖ ^ 2 = ‖dyadicQuotientProjection f‖ ^ 2 +
      ‖f - dyadicQuotientProjection f‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection f dyadicQuotientSubspace
  rw [Submodule.starProjection_orthogonal_val] at h
  exact h

/-- Concrete scaled-dilation bound for the actual dyadic quotient. -/
theorem dyadicQuotientProjection_dilation_norm_sq_le
    (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection (hilbertDilation m hm f)‖ ^ 2 ≤
      (m : ℝ) * ‖f‖ ^ 2 := by
  have h := dyadicQuotientProjection_norm_le (hilbertDilation m hm f)
  have hsq : ‖dyadicQuotientProjection (hilbertDilation m hm f)‖ ^ 2 ≤
      ‖hilbertDilation m hm f‖ ^ 2 :=
    by simpa only [pow_two] using
      mul_le_mul h h (norm_nonneg _) (norm_nonneg _)
  simpa only [hilbertDilation_norm_sq] using hsq

/-- The tail transfer estimate requires only that the actual target projection
is contractive. It applies to every tail quotient once that projection and the
arithmetic transfer identity have been constructed. -/
theorem contractive_projection_dilation_norm_sq_le
    (P : ThresholdHilbert →L[ℝ] ThresholdHilbert)
    (hP : ∀ f, ‖P f‖ ≤ ‖f‖)
    (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖P (hilbertDilation m hm f)‖ ^ 2 ≤ (m : ℝ) * ‖f‖ ^ 2 := by
  have h := hP (hilbertDilation m hm f)
  have hsq : ‖P (hilbertDilation m hm f)‖ ^ 2 ≤
      ‖hilbertDilation m hm f‖ ^ 2 :=
    by simpa only [pow_two] using
      mul_le_mul h h (norm_nonneg _) (norm_nonneg _)
  simpa only [hilbertDilation_norm_sq] using hsq

/-- Conditional norm assembly for (N24). The hypotheses `hdecomp`, `hstep`,
and `herr` are the substantive analytic inputs; they have not been discharged
by the construction of the actual quotient projection above. -/
theorem uniform_norm_sq_of_exact_decomposition
    (G step err : ℝ → ThresholdHilbert) (u v : ThresholdHilbert)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdecomp : ∀ ε, 0 < ε → ε ≤ 1 / 2 →
      G ε = u + v - step ε + err ε)
    (hstep : ∀ ε, 0 < ε → ε ≤ 1 / 2 → ‖step ε‖ ≤ A)
    (herr : ∀ ε, 0 < ε → ε ≤ 1 / 2 → ‖err ε‖ ≤ R * Real.sqrt ε)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ‖G ε‖ ^ 2 ≤ (‖u‖ + ‖v‖ + A + R) ^ 2 := by
  have hsqrt : Real.sqrt ε ≤ 1 := by
    nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
  have he : ‖err ε‖ ≤ R :=
    (herr ε hε hεhalf).trans (by nlinarith)
  have hb : ‖G ε‖ ≤ ‖u‖ + ‖v‖ + A + R := by
    rw [hdecomp ε hε hεhalf]
    calc
      ‖u + v - step ε + err ε‖ ≤ ‖u + v - step ε‖ + ‖err ε‖ := norm_add_le _ _
      _ ≤ ‖u + v‖ + ‖step ε‖ + ‖err ε‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ ‖u‖ + ‖v‖ + A + R := by
        linarith [norm_add_le u v, hstep ε hε hεhalf]
  simpa only [pow_two] using
    mul_le_mul hb hb (norm_nonneg _) (by positivity)

/-- Specialization to the concrete Möbius regularization. This theorem records
exactly what must be supplied to finish the analytic proof: convergence of the
actual arithmetic series, a bound for the concrete step Abel orbit (N30), and
the norm remainder estimate in the exact decomposition (N24).

The three substantive hypotheses remain missing formal providers;
this theorem must not be reported as an unconditional Lean verification of the arithmetic bound. -/
theorem dyadicRegularizedNormBound_of_analytic_estimates
    (hseries : DyadicRegularizedSeriesSummable)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ‖dyadicStepAbelOrbit ε‖ ≤ A)
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R * Real.sqrt ε) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound := by
  refine ⟨hseries, ?_⟩
  let u := dyadicQuotientProjection hilbertOne
  let v := (Real.log 2)⁻¹ •
    dyadicQuotientProjection (hilbertResidue 2 (by norm_num))
  let err := fun ε => dyadicRegularizedFamily ε - (u + v - dyadicStepAbelOrbit ε)
  refine ⟨(‖u‖ + ‖v‖ + A + R) ^ 2, sq_nonneg _, ?_⟩
  intro ε hε hεhalf
  apply uniform_norm_sq_of_exact_decomposition
    dyadicRegularizedFamily dyadicStepAbelOrbit err u v A R hA hR
    (fun ε _ _ => by dsimp [err]; abel) hstep
    (fun ε hε hεhalf => herror ε hε hεhalf) ε hε hεhalf

/-- Conditional assembly of the `C d` bound, with all substantive analytic
and tail-transfer assumptions visible in the type. The norm is the actual
Pareto Hilbert norm, not a finite truncation or pointwise substitute. -/
theorem transferred_uniform_norm_sq_of_exact_decomposition
    (G step err : ℝ → ThresholdHilbert) (u v : ThresholdHilbert)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdecomp : ∀ ε, 0 < ε → ε ≤ 1 / 2 →
      G ε = u + v - step ε + err ε)
    (hstep : ∀ ε, 0 < ε → ε ≤ 1 / 2 → ‖step ε‖ ≤ A)
    (herr : ∀ ε, 0 < ε → ε ≤ 1 / 2 → ‖err ε‖ ≤ R * Real.sqrt ε)
    (P : ℕ → ThresholdHilbert →L[ℝ] ThresholdHilbert)
    (hP : ∀ X f, ‖P X f‖ ≤ ‖f‖)
    (F : ℕ → ℕ → ℝ → ThresholdHilbert)
    (htransfer : ∀ X d (hX : 0 < X) (hXd : X ≤ d),
      ∀ ε, 0 < ε → ε ≤ 1 / 2 →
      F X d ε = P X (hilbertDilation d (Nat.lt_of_lt_of_le hX hXd) (G ε))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X d, 0 < X → X ≤ d →
      ∀ ε, 0 < ε → ε ≤ 1 / 2 → ‖F X d ε‖ ^ 2 ≤ C * d := by
  refine ⟨(‖u‖ + ‖v‖ + A + R) ^ 2, sq_nonneg _, ?_⟩
  intro X d hX hXd ε hε hεhalf
  rw [htransfer X d hX hXd ε hε hεhalf]
  calc
    _ ≤ (d : ℝ) * ‖G ε‖ ^ 2 :=
      contractive_projection_dilation_norm_sq_le (P X) (hP X) d (by omega) (G ε)
    _ ≤ (d : ℝ) * (‖u‖ + ‖v‖ + A + R) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (uniform_norm_sq_of_exact_decomposition G step err u v A R hA hR
          hdecomp hstep herr ε hε hεhalf) (Nat.cast_nonneg d)
    _ = _ := mul_comm _ _

theorem hilbertDilationAdjoint_preserves_dyadicQuotient
    (m : ℕ) (hm : 0 < m) (g : ThresholdHilbert)
    (hg : g ∈ dyadicQuotientSubspace) :
    hilbertDilationAdjoint m hm g ∈ dyadicQuotientSubspace := by
  apply (mem_dyadicQuotientSubspace_iff _).mpr
  have hgf := (mem_dyadicQuotientSubspace_iff g).mp hg
  apply ext_inner_left ℝ
  intro x
  calc
    inner ℝ x (hilbertDilationAdjoint 2 (by norm_num)
        (hilbertDilationAdjoint m hm g)) =
      inner ℝ (hilbertDilation 2 (by norm_num) x)
        (hilbertDilationAdjoint m hm g) :=
          ContinuousLinearMap.adjoint_inner_right
            (hilbertDilationContinuous 2 (by norm_num)) x _
    _ = inner ℝ (hilbertDilation m hm (hilbertDilation 2 (by norm_num) x)) g :=
      ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous m hm) _ g
    _ = inner ℝ (hilbertDilation 2 (by norm_num) (hilbertDilation m hm x)) g := by
      simp only [hilbertDilation_comp, Nat.mul_comm]
    _ = inner ℝ (hilbertDilation m hm x)
        (hilbertDilationAdjoint 2 (by norm_num) g) :=
      (ContinuousLinearMap.adjoint_inner_right
        (hilbertDilationContinuous 2 (by norm_num)) _ g).symm
    _ = inner ℝ (hilbertDilation m hm x) g := by rw [hgf]
    _ = inner ℝ x (hilbertDilationAdjoint m hm g) :=
      (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous m hm) x g).symm

theorem dyadicQuotientProjection_eq_self {f : ThresholdHilbert}
    (hf : f ∈ dyadicQuotientSubspace) : dyadicQuotientProjection f = f :=
  Submodule.starProjection_eq_self_iff.mpr hf

theorem dyadicQuotientProjection_inner (f g : ThresholdHilbert) :
    inner ℝ (dyadicQuotientProjection f) g =
      inner ℝ f (dyadicQuotientProjection g) :=
  dyadicQuotientSubspace.starProjection_isSymmetric f g

/-- Dyadic dilation is exactly the identity on the dyadic quotient. -/
theorem dyadicQuotientProjection_dilation_two (f : ThresholdHilbert) :
    dyadicQuotientProjection (hilbertDilation 2 (by norm_num) f) =
      dyadicQuotientProjection f := by
  apply ext_inner_left ℝ
  intro g
  have ha := ContinuousLinearMap.adjoint_inner_right
    (hilbertDilationContinuous 2 (by norm_num)) f (dyadicQuotientProjection g)
  change inner ℝ f (hilbertDilationAdjoint 2 (by norm_num)
      (dyadicQuotientProjection g)) =
    inner ℝ (hilbertDilation 2 (by norm_num) f) (dyadicQuotientProjection g) at ha
  rw [dyadicQuotientProjection_fixed] at ha
  calc
    inner ℝ g (dyadicQuotientProjection (hilbertDilation 2 (by norm_num) f)) =
      inner ℝ (dyadicQuotientProjection g) (hilbertDilation 2 (by norm_num) f) :=
      (dyadicQuotientProjection_inner _ _).symm
    _ = inner ℝ (hilbertDilation 2 (by norm_num) f) (dyadicQuotientProjection g) :=
      real_inner_comm _ _
    _ = inner ℝ f (dyadicQuotientProjection g) := ha.symm
    _ = inner ℝ (dyadicQuotientProjection g) f := real_inner_comm _ _
    _ = inner ℝ g (dyadicQuotientProjection f) := dyadicQuotientProjection_inner _ _

/-- The projection after dilation depends only on the quotient class. -/
theorem dyadicQuotientProjection_dilation_projection
    (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    dyadicQuotientProjection (hilbertDilation m hm (dyadicQuotientProjection f)) =
      dyadicQuotientProjection (hilbertDilation m hm f) := by
  apply ext_inner_left ℝ
  intro g
  have hfix : dyadicQuotientProjection
      (hilbertDilationAdjoint m hm (dyadicQuotientProjection g)) =
      hilbertDilationAdjoint m hm (dyadicQuotientProjection g) :=
    dyadicQuotientProjection_eq_self
      (hilbertDilationAdjoint_preserves_dyadicQuotient m hm
        (dyadicQuotientProjection g) (dyadicQuotientProjection_mem g))
  have ha (x y : ThresholdHilbert) :
      inner ℝ x (hilbertDilation m hm y) =
        inner ℝ (hilbertDilationAdjoint m hm x) y := by
    calc
      inner ℝ x (hilbertDilation m hm y) =
          inner ℝ (hilbertDilation m hm y) x :=
        (real_inner_comm x (hilbertDilation m hm y)).symm
      _ = inner ℝ y (hilbertDilationAdjoint m hm x) :=
        (ContinuousLinearMap.adjoint_inner_right
          (hilbertDilationContinuous m hm) y x).symm
      _ = inner ℝ (hilbertDilationAdjoint m hm x) y :=
        (real_inner_comm y (hilbertDilationAdjoint m hm x)).symm
  calc
    inner ℝ g (dyadicQuotientProjection
        (hilbertDilation m hm (dyadicQuotientProjection f))) =
      inner ℝ (dyadicQuotientProjection g)
        (hilbertDilation m hm (dyadicQuotientProjection f)) :=
      (dyadicQuotientProjection_inner _ _).symm
    _ = inner ℝ (hilbertDilationAdjoint m hm (dyadicQuotientProjection g))
        (dyadicQuotientProjection f) := ha _ _
    _ = inner ℝ (dyadicQuotientProjection
        (hilbertDilationAdjoint m hm (dyadicQuotientProjection g))) f :=
      (dyadicQuotientProjection_inner _ _).symm
    _ = inner ℝ (hilbertDilationAdjoint m hm (dyadicQuotientProjection g)) f := by
      rw [hfix]
    _ = inner ℝ (dyadicQuotientProjection g) (hilbertDilation m hm f) := (ha _ _).symm
    _ = inner ℝ g (dyadicQuotientProjection (hilbertDilation m hm f)) :=
      dyadicQuotientProjection_inner _ _

/-- The stronger quotient-class bound needed for the induced operator. -/
theorem dyadicQuotientProjection_dilation_norm_sq_le_quotient
    (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection (hilbertDilation m hm f)‖ ^ 2 ≤
      (m : ℝ) * ‖dyadicQuotientProjection f‖ ^ 2 := by
  rw [← dyadicQuotientProjection_dilation_projection m hm f]
  exact dyadicQuotientProjection_dilation_norm_sq_le m hm (dyadicQuotientProjection f)


end
end RiemannResearch.RH.Pareto


/-!
# Scalar convergence in the concrete Möbius regularization

Source: user-provided argument, `norm_obligation_proved.md`, (N1), (N17),
and the positive-damping scalar prerequisites in §4--6.

The zeta Dirichlet series really is summable for every positive damping.
These results do not claim summability of the Hilbert-valued arithmetic series.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The positive-damping scalar Dirichlet series is an actual convergent series. -/
theorem regularizationZetaSeries_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ (-(1 + ε))) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + ε))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa only [Function.comp_def, Nat.cast_succ] using hs.comp_injective Nat.succ_injective

/-- The first Dirichlet coefficient is one and all the others are nonnegative. -/
theorem one_le_regularizationZetaSeries {ε : ℝ} (hε : 0 < ε) :
    1 ≤ regularizationZetaSeries ε := by
  have hs := regularizationZetaSeries_summable hε
  have h := hs.sum_le_tsum ({0} : Finset ℕ)
    (fun n hn => Real.rpow_nonneg (by positivity) _)
  simpa [regularizationZetaSeries] using h

theorem triadicDampingRatio_pos (ε : ℝ) : 0 < triadicDampingRatio ε := by
  unfold triadicDampingRatio
  positivity

theorem triadicDampingRatio_lt_one {ε : ℝ} (hε : 0 < ε) :
    triadicDampingRatio ε < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The damping ratios in the claimed norm theorem stay uniformly above `1/2`. -/
theorem half_le_triadicDampingRatio {ε : ℝ} (hε : ε ≤ 1 / 2) :
    1 / 2 ≤ triadicDampingRatio ε := by
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 3 ≤ 2 * Real.log 2 := by
    calc
      Real.log 3 ≤ Real.log (2 * 2) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := by rw [Real.log_mul (by norm_num) (by norm_num)]; ring
  have hexp : -(Real.log 2) ≤ Real.log 3 * (-ε) := by
    nlinarith [mul_le_mul_of_nonneg_left hε hlog3]
  have he : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  unfold triadicDampingRatio
  rw [Real.rpow_def_of_pos (by norm_num), ← he]
  exact Real.exp_le_exp.mpr hexp

theorem triadicDampingRatio_pow_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ => triadicDampingRatio ε ^ j) := by
  exact summable_geometric_of_lt_one (le_of_lt (triadicDampingRatio_pos ε))
    (triadicDampingRatio_lt_one hε)

/-- The normalization is positive whenever its Dirichlet series is used. -/
theorem dyadicRegularizationNormalization_pos {ε : ℝ} (hε : 0 < ε) :
    0 < dyadicRegularizationNormalization ε := by
  have hz : 0 < regularizationZetaSeries ε :=
    lt_of_lt_of_le (by norm_num) (one_le_regularizationZetaSeries hε)
  have hr : 0 < 1 - triadicDampingRatio ε := sub_pos.mpr
    (triadicDampingRatio_lt_one hε)
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact div_pos (mul_pos hz hr) hl

end
end RiemannResearch.RH.Pareto
