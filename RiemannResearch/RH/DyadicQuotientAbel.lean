import RiemannResearch.RH.DyadicRegularizedNorm
import RiemannResearch.Analysis.AbelOrbitGrowth
import RiemannResearch.Analysis.AbelGramBound

/-!
# Integer dilation orbits in the actual dyadic quotient

Source: user-provided September 10, 2026 handoff, (N6), (N22)--(N24).

The induced dilation is constructed from the actual weighted Hilbert operators.
Its composition law, physical orbit formula, fixed dyadic residue, and step-orbit
identification are unconditional. Quantitative Abel estimates below retain the
explicit physical orbit-growth hypothesis from (N22); its arithmetic provider
is not supplied by the abstract summation theorem.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open RiemannResearch.Analysis.AbelCoboundary

noncomputable section

/-- The actual induced integer dilation, extended to ambient H by the quotient
projection. On QH this is the operator `B_m` of (N6). -/
def dyadicQuotientDilation (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  dyadicQuotientProjection.comp
    ((hilbertDilationContinuous m hm).comp dyadicQuotientProjection)

@[simp] theorem dyadicQuotientDilation_apply (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    dyadicQuotientDilation m hm f =
      dyadicQuotientProjection (hilbertDilation m hm f) := by
  change dyadicQuotientProjection
    (hilbertDilation m hm (dyadicQuotientProjection f)) = _
  exact dyadicQuotientProjection_dilation_projection m hm f

theorem dyadicQuotientDilation_mem (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    dyadicQuotientDilation m hm f ∈ dyadicQuotientSubspace := by
  rw [dyadicQuotientDilation_apply]
  exact dyadicQuotientProjection_mem _

/-- The complete all-integer semigroup law, without double commutation of
the original dilation operators with their adjoints. -/
theorem dyadicQuotientDilation_comp (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : ThresholdHilbert) :
    dyadicQuotientDilation m hm (dyadicQuotientDilation n hn f) =
      dyadicQuotientDilation (m * n) (Nat.mul_pos hm hn) f := by
  simp only [dyadicQuotientDilation_apply,
    dyadicQuotientProjection_dilation_projection, hilbertDilation_comp]

@[simp] theorem dyadicQuotientDilation_one (f : ThresholdHilbert) :
    dyadicQuotientDilation 1 (by norm_num) f = dyadicQuotientProjection f := by
  rw [dyadicQuotientDilation_apply, hilbertDilation_one]

@[simp] theorem dyadicQuotientDilation_two (f : ThresholdHilbert) :
    dyadicQuotientDilation 2 (by norm_num) f = dyadicQuotientProjection f := by
  rw [dyadicQuotientDilation_apply, dyadicQuotientProjection_dilation_two]

theorem dyadicQuotientDilation_norm_sq_le (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    ‖dyadicQuotientDilation m hm f‖ ^ 2 ≤
      (m : ℝ) * ‖dyadicQuotientProjection f‖ ^ 2 := by
  rw [dyadicQuotientDilation_apply]
  exact dyadicQuotientProjection_dilation_norm_sq_le_quotient m hm f

/-- Actual iterates agree with the projected physical power dilations. -/
theorem dyadicQuotientDilation_orbit (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (j : ℕ) :
    orbit (dyadicQuotientDilation m hm) (dyadicQuotientProjection f) j =
      dyadicQuotientProjection (hilbertDilation (m ^ j) (pow_pos hm j) f) := by
  induction j with
  | zero => simp only [orbit_zero, pow_zero, hilbertDilation_one]
  | succ j ih =>
      rw [orbit_succ, ih, dyadicQuotientDilation_apply,
        dyadicQuotientProjection_dilation_projection, hilbertDilation_comp]
      simp only [pow_succ']

/-- The residue cocycle holds in the genuine weighted complete H. -/
theorem hilbertDilation_residue_cocycle (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    hilbertDilation m hm (hilbertResidue n hn) - hilbertResidue n hn =
      hilbertDilation n hn (hilbertResidue m hm) - hilbertResidue m hm := by
  apply hilbertSequence_injective
  simp only [hilbertSequence_sub, hilbertDilation_sequence, hilbertResidue_sequence]
  funext k
  exact dilation_cocycle m n k

/-- The concrete mean vector `Q R₂` is fixed by every induced integer dilation. -/
theorem dyadicQuotientDilation_fixed_residue_two (m : ℕ) (hm : 0 < m) :
    dyadicQuotientDilation m hm
        (dyadicQuotientProjection (hilbertResidue 2 (by norm_num))) =
      dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) := by
  have h := congrArg dyadicQuotientProjection
    (hilbertDilation_residue_cocycle m 2 hm (by norm_num))
  rw [map_sub, map_sub, dyadicQuotientProjection_dilation_two, sub_self] at h
  rw [dyadicQuotientDilation_apply, dyadicQuotientProjection_dilation_projection]
  exact sub_eq_zero.mp h

/-- The target constant already lies in the dyadic quotient. -/
@[simp] theorem dyadicQuotientProjection_one :
    dyadicQuotientProjection hilbertOne = hilbertOne := by
  apply dyadicQuotientProjection_eq_self
  exact (mem_dyadicQuotientSubspace_iff hilbertOne).mpr
    (hilbertDilationAdjoint_one 2 (by norm_num))

/-- The concrete projected Abel average, written directly with physical power
dilations. Its series interpretation is justified by the summability theorem
below under the stated physical growth hypothesis. -/
def dyadicDilationAbelAverage (m : ℕ) (hm : 0 < m) (r : ℝ)
    (f : ThresholdHilbert) : ThresholdHilbert :=
  average r (fun j : ℕ =>
    dyadicQuotientProjection (hilbertDilation (m ^ j) (pow_pos hm j) f))

theorem dyadicDilationAbelAverage_eq_orbit (m : ℕ) (hm : 0 < m) (r : ℝ)
    (f : ThresholdHilbert) :
    dyadicDilationAbelAverage m hm r f =
      average r (orbit (dyadicQuotientDilation m hm) (dyadicQuotientProjection f)) := by
  unfold dyadicDilationAbelAverage
  congr 1
  funext j
  exact (dyadicQuotientDilation_orbit m hm f j).symm

/-- The step Abel orbit from the norm-obligation statement is the orbit of the
actual induced triadic operator, with the exact initial vector `Q T₃ 1`. -/
theorem dyadicStepAbelOrbit_eq_induced_orbit (ε : ℝ) :
    dyadicStepAbelOrbit ε =
      average (triadicDampingRatio ε)
        (orbit (dyadicQuotientDilation 3 (by norm_num))
          (dyadicQuotientProjection (hilbertDilation 3 (by norm_num) hilbertOne))) := by
  simp only [dyadicStepAbelOrbit, average, series,
    dyadicQuotientDilation_orbit, hilbertDilation_comp, pow_succ]

/-- Positive damping makes every physical orbit of square-root growth absolutely
summable in the actual quotient norm. The physical growth estimate is explicit. -/
theorem dyadicDilationAbel_summable_of_sqrt_growth
    (m : ℕ) (hm : 0 < m) (r C : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C) (f : ThresholdHilbert)
    (hf : ∀ j : ℕ,
      ‖dyadicQuotientProjection (hilbertDilation (m ^ j) (pow_pos hm j) f)‖ ≤
        C * Real.sqrt ((j : ℝ) + 1)) :
    Summable (fun j : ℕ => r ^ j •
      dyadicQuotientProjection (hilbertDilation (m ^ j) (pow_pos hm j) f)) :=
  summable_geometric_of_sqrt_growth r C hr0 hr1 hC _ hf

theorem dyadicDilationAbel_norm_le_of_sqrt_growth
    (m : ℕ) (hm : 0 < m) (r C : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C) (f : ThresholdHilbert)
    (hf : ∀ j : ℕ,
      ‖dyadicQuotientProjection (hilbertDilation (m ^ j) (pow_pos hm j) f)‖ ≤
        C * Real.sqrt ((j : ℝ) + 1)) :
    ‖dyadicDilationAbelAverage m hm r f‖ ≤ C / Real.sqrt (1 - r) :=
  norm_average_le_of_sqrt_growth r C hr0 hr1 hC _ hf

/-- The generic square-root coboundary estimate now applies to the actual
weighted quotient and the actual signed physical difference `f - T_m f`.
The only substantive analytic input is the displayed physical orbit growth. -/
theorem dyadicDilationAbel_coboundary_norm_le_of_sqrt_growth
    (m : ℕ) (hm : 0 < m) (r C : ℝ)
    (hrhalf : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1) (hC : 0 ≤ C)
    (f : ThresholdHilbert)
    (hf : ∀ j : ℕ,
      ‖dyadicQuotientProjection (hilbertDilation (m ^ j) (pow_pos hm j) f)‖ ≤
        C * Real.sqrt ((j : ℝ) + 1)) :
    ‖dyadicDilationAbelAverage m hm r (f - hilbertDilation m hm f)‖ ≤
      4 * C * Real.sqrt (1 - r) := by
  have hseed : dyadicQuotientProjection (f - hilbertDilation m hm f) =
      dyadicQuotientProjection f -
        dyadicQuotientDilation m hm (dyadicQuotientProjection f) := by
    rw [map_sub, dyadicQuotientDilation_apply,
      dyadicQuotientProjection_dilation_projection]
  rw [dyadicDilationAbelAverage_eq_orbit, hseed]
  apply norm_orbit_average_coboundary_le_sqrt
    (dyadicQuotientDilation m hm) r C hrhalf hr1 hC (dyadicQuotientProjection f)
  intro j
  simpa only [dyadicQuotientDilation_orbit] using hf j

/-- Concrete specialization at the handoff's damping ratio `3^(-ε)`. This is
the norm estimate required by (N23) once the explicit potential satisfies N22. -/
theorem dyadicTriadicAbel_coboundary_norm_le
    (ε C : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hC : 0 ≤ C)
    (f : ThresholdHilbert)
    (hf : ∀ j : ℕ,
      ‖dyadicQuotientProjection (hilbertDilation (3 ^ j) (by positivity) f)‖ ≤
        C * Real.sqrt ((j : ℝ) + 1)) :
    ‖dyadicDilationAbelAverage 3 (by norm_num) (triadicDampingRatio ε)
        (f - hilbertDilation 3 (by norm_num) f)‖ ≤
      4 * C * Real.sqrt (1 - triadicDampingRatio ε) :=
  dyadicDilationAbel_coboundary_norm_le_of_sqrt_growth 3 (by norm_num)
    (triadicDampingRatio ε) C (half_le_triadicDampingRatio hεhalf)
    (triadicDampingRatio_lt_one hε) hC f hf

/-- The actual step orbit is uniformly bounded once its concrete diagonal
and off-diagonal Gram estimates are supplied. The general Gram theorem
derives series summability internally; no average-norm hypothesis is used. -/
theorem dyadicStepAbelOrbit_norm_sq_le_of_gram
    (D A : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hdiag : ∀ j : ℕ,
      ‖dyadicQuotientProjection
        (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne)‖ ^ 2 ≤
        D * ((j : ℝ) + 1))
    (hprefix : ∀ N, RiemannResearch.Analysis.prefixSum a N ≤ A * N)
    (hoff : ∀ j k : ℕ, j < k →
      |inner ℝ (dyadicQuotientProjection
          (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne))
        (dyadicQuotientProjection
          (hilbertDilation (3 ^ (k + 1)) (by positivity) hilbertOne))| ≤ a (k - j))
    (ε : ℝ) (hε : 0 < ε) :
    ‖dyadicStepAbelOrbit ε‖ ^ 2 ≤ D + 2 * A := by
  exact RiemannResearch.Analysis.AbelGram.norm_average_sq_le
    (triadicDampingRatio ε) D A (triadicDampingRatio_pos ε).le
    (triadicDampingRatio_lt_one hε) hD hA
    (fun j : ℕ => dyadicQuotientProjection
      (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne))
    a ha hdiag hprefix hoff

end
end RiemannResearch.RH.Pareto
