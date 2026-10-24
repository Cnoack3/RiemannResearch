import RiemannResearch.RH.ParetoMellinSourcePerturbation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity

/-!
# The full complex metric on finite Mellin sources

Source: the user's fifth Ramanujan transfer program, October 2026.
The mixed integral, including its complex phase, precedes the sharp
Cauchy--Schwarz and reverse-triangle bounds. No coordinatewise absolute
value replacement or discarded signed correction is used in the identities.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι]

theorem finiteMellinKernel_mixed_integral (s c d : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (∫ x in Ioi (1 : ℝ), finiteMellinKernel s c x *
      starRingEnd ℂ (finiteMellinKernel s d x)) = mellinGramPairing s c d := by
  classical
  have hi (i j : ι) : IntegrableOn (fun x =>
      (starRingEnd ℂ (c i) * d j) * (paretoMellinKernel (s i) x *
        starRingEnd ℂ (paretoMellinKernel (s j) x))) (Ioi 1) :=
    (paretoMellinKernel_cross_integrable (s i) (s j) (hs i) (hs j)).const_mul _
  have he : (fun x => finiteMellinKernel s c x *
      starRingEnd ℂ (finiteMellinKernel s d x)) =
      fun x => ∑ i, ∑ j, (starRingEnd ℂ (c i) * d j) *
        (paretoMellinKernel (s i) x *
          starRingEnd ℂ (paretoMellinKernel (s j) x)) := by
    funext x
    have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
      change star (star z) = z
      exact star_star z
    simp only [finiteMellinKernel, map_sum, map_mul, hconj,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  unfold mellinGramPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, paretoMellinKernel_gram (s i) (s j) (hs i) (hs j)]
  rfl

variable [DecidableEq ι]

/-- Hermitian inverse-Gram pairing, retaining its complete complex phase. -/
def mellinSourcePairing (s b e : ι → ℂ) : ℂ :=
  ∑ i, starRingEnd ℂ (mellinInverseCoefficients s b i) * e i

theorem mellinSourcePairing_eq_integral (s b e : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinSourcePairing s b e =
      ∫ x in Ioi (1 : ℝ), finiteMellinKernel s (mellinInverseCoefficients s b) x *
        starRingEnd ℂ (finiteMellinKernel s (mellinInverseCoefficients s e) x) := by
  rw [finiteMellinKernel_mixed_integral s _ _ hs,
    mellinGramPairing_eq_of_normal s _ _ e (mellinInverseCoefficients_normal s e hdet)]
  rfl

theorem mellinSourcePairing_conj (s b e : ι → ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    starRingEnd ℂ (mellinSourcePairing s b e) = mellinSourcePairing s e b := by
  have hb := mellinGramPairing_eq_of_normal s
    (mellinInverseCoefficients s b) (mellinInverseCoefficients s e) e
    (mellinInverseCoefficients_normal s e hdet)
  have he := mellinGramPairing_eq_of_normal s
    (mellinInverseCoefficients s e) (mellinInverseCoefficients s b) b
    (mellinInverseCoefficients_normal s b hdet)
  change _ = mellinSourcePairing s b e at hb
  change _ = mellinSourcePairing s e b at he
  rw [← hb, mellinGramPairing_conj, he]

/-- Sharp matrix-aware Cauchy--Schwarz, stronger than any real-cross bound. -/
theorem mellinSourcePairing_norm_sq_le (s b e : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    ‖mellinSourcePairing s b e‖ ^ 2 ≤
      mellinInverseCapacity s b * mellinInverseCapacity s e := by
  have h := RemoteLaplaceTail.norm_integral_mul_sq_le
    (finiteMellinKernel_memLp s (mellinInverseCoefficients s b) hs)
    (finiteMellinKernel_memLp s (mellinInverseCoefficients s e) hs).star
  change
    ‖∫ x in Ioi (1 : ℝ), finiteMellinKernel s (mellinInverseCoefficients s b) x *
      starRingEnd ℂ (finiteMellinKernel s (mellinInverseCoefficients s e) x)‖ ^ 2 ≤
    (∫ x in Ioi (1 : ℝ), ‖finiteMellinKernel s (mellinInverseCoefficients s b) x‖ ^ 2) *
      (∫ x in Ioi (1 : ℝ),
        ‖starRingEnd ℂ (finiteMellinKernel s (mellinInverseCoefficients s e) x)‖ ^ 2) at h
  simpa only [← mellinSourcePairing_eq_integral s b e hs hdet,
    Complex.norm_conj, ← mellinInverseCapacity_eq_kernel_energy s b hs hdet,
    ← mellinInverseCapacity_eq_kernel_energy s e hs hdet] using h

/-- No nonzero source has zero capacity: the inverse-Gram metric is definite. -/
theorem mellinInverseCapacity_eq_zero_iff (s b : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinInverseCapacity s b = 0 ↔ b = 0 := by
  constructor
  · intro hz
    have hc : mellinInverseCoefficients s b = 0 := by
      funext i
      have h := mellinSourcePairing_norm_sq_le s b
        (fun j => if j = i then 1 else 0) hs hdet
      have he : mellinSourcePairing s b (fun j => if j = i then 1 else 0) =
          starRingEnd ℂ (mellinInverseCoefficients s b i) := by
        simp [mellinSourcePairing]
      rw [he, hz, zero_mul, Complex.norm_conj] at h
      change mellinInverseCoefficients s b i = 0
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (mellinInverseCoefficients s b i)]
    funext i
    have h := mellinInverseCoefficients_normal s b hdet i
    rw [hc] at h
    simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] using h.symm
  · intro hz
    subst b
    simp [mellinInverseCapacity]

theorem mellinInverseCapacity_pos_iff (s b : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    0 < mellinInverseCapacity s b ↔ b ≠ 0 := by
  have hn := mellinInverseCapacity_nonneg s b hs hdet
  have hz := mellinInverseCapacity_eq_zero_iff s b hs hdet
  constructor
  · intro hp hb
    have he := hz.mpr hb
    linarith
  · intro hb
    have he : mellinInverseCapacity s b ≠ 0 := fun h => hb (hz.mp h)
    exact lt_of_le_of_ne hn (Ne.symm he)

theorem mellinSourcePairing_norm_le (s b e : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    ‖mellinSourcePairing s b e‖ ≤
      Real.sqrt (mellinInverseCapacity s b) * Real.sqrt (mellinInverseCapacity s e) := by
  have hb := mellinInverseCapacity_nonneg s b hs hdet
  have he := mellinInverseCapacity_nonneg s e hs hdet
  have h := mellinSourcePairing_norm_sq_le s b e hs hdet
  have hp : 0 ≤ Real.sqrt (mellinInverseCapacity s b) *
      Real.sqrt (mellinInverseCapacity s e) := by positivity
  have hsq : (Real.sqrt (mellinInverseCapacity s b) *
      Real.sqrt (mellinInverseCapacity s e)) ^ 2 =
      mellinInverseCapacity s b * mellinInverseCapacity s e := by
    rw [mul_pow, Real.sq_sqrt hb, Real.sq_sqrt he]
  nlinarith [norm_nonneg (mellinSourcePairing s b e)]

theorem mellinSourceCross_abs_le (s b e : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    |mellinSourceCross s b e| ≤
      Real.sqrt (mellinInverseCapacity s b) * Real.sqrt (mellinInverseCapacity s e) := by
  exact (Complex.abs_re_le_norm (mellinSourcePairing s b e)).trans
    (mellinSourcePairing_norm_le s b e hs hdet)

/-- Exact capacities obey both sharp squared triangle bounds. -/
theorem mellinInverseCapacity_sub_source_bounds (s b e : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    (Real.sqrt (mellinInverseCapacity s b) -
        Real.sqrt (mellinInverseCapacity s e)) ^ 2 ≤ mellinInverseCapacity s (b - e) ∧
      mellinInverseCapacity s (b - e) ≤
        (Real.sqrt (mellinInverseCapacity s b) +
          Real.sqrt (mellinInverseCapacity s e)) ^ 2 := by
  have hb := Real.sq_sqrt (mellinInverseCapacity_nonneg s b hs hdet)
  have he := Real.sq_sqrt (mellinInverseCapacity_nonneg s e hs hdet)
  have hc := abs_le.mp (mellinSourceCross_abs_le s b e hs hdet)
  have h := mellinInverseCapacity_sub_source s b e hdet
  constructor <;> nlinarith [hc.1, hc.2]

/-- The square root of the complete inverse capacity is Lipschitz in its own metric. -/
theorem mellinInverseCapacity_sqrt_reverse_triangle (s b e : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    |Real.sqrt (mellinInverseCapacity s b) - Real.sqrt (mellinInverseCapacity s e)| ≤
      Real.sqrt (mellinInverseCapacity s (b - e)) := by
  have h := (mellinInverseCapacity_sub_source_bounds s b e hs hdet).1
  have hr := Real.sq_sqrt (mellinInverseCapacity_nonneg s (b - e) hs hdet)
  have ha := sq_abs (Real.sqrt (mellinInverseCapacity s b) -
    Real.sqrt (mellinInverseCapacity s e))
  nlinarith [abs_nonneg (Real.sqrt (mellinInverseCapacity s b) -
    Real.sqrt (mellinInverseCapacity s e)), Real.sqrt_nonneg (mellinInverseCapacity s (b - e))]

/-- A whole-source perturbation budget retains its inverse-Gram geometry. -/
theorem finiteMellinKernel_source_metric_lower (f : ThresholdHilbert) (s b e : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0)
    (hsig : ∀ i, paretoMellin f (s i) = b i - e i) :
    (Real.sqrt (mellinInverseCapacity s b) -
      Real.sqrt (mellinInverseCapacity s e)) ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := finiteMellinKernel_inverse_completion f s hs hdet
  have he : (fun i => paretoMellin f (s i)) = b - e := funext hsig
  rw [he] at h
  have hr : 0 ≤ ∫ x in Ioi (1 : ℝ),
      ‖mellinWeightedStep f x - starRingEnd ℂ
        (finiteMellinKernel s (mellinInverseCoefficients s (b - e)) x)‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hb := (mellinInverseCapacity_sub_source_bounds s b e hs hdet).1
  linarith

end RiemannResearch.RH.Pareto
