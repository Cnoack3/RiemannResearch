import RiemannResearch.RH.CRTDelayedProjection

set_option autoImplicit false

/-!
# Three-generator corrections preserving the exact head and period mean

Source: the user-requested three-generator strict-improvement argument.
This module supplies the arithmetic direction and exact scalar energy decrease.
Nonzero correlation is an explicit hypothesis here; an independent detection
theorem must supply it before the unconditional strict-improvement endpoint.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ArithmeticCumulative.CesaroResidue
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.Analysis.Cesaro

/-- A single correction supported on three residue generators. -/
def threeGeneratorDirection (d n : ℕ) : ℝ :=
  meanPulse d n - meanPulse (2*d) n

theorem threeGeneratorDirection_eq (d n : ℕ) :
    threeGeneratorDirection d n =
      3*residueFraction (2*d) n - residueFraction d n -
        2*residueFraction (4*d) n := by
  unfold threeGeneratorDirection meanPulse
  rw [show 2*(2*d) = 4*d by ring]
  ring

theorem threeGeneratorDirection_legal (d : ℕ) (hd : 0 < d) :
    threeGeneratorDirection d ∈ legalSeedSpan (Set.Ici 1) := by
  exact (legalSeedSpan (Set.Ici 1)).sub_mem
    (meanPulse_legal d hd) (meanPulse_legal (2*d) (by omega))

theorem threeGeneratorDirection_zero_before (d n : ℕ) (hn : n < d) :
    threeGeneratorDirection d n = 0 := by
  simp only [threeGeneratorDirection, meanPulse_zero_before d n hn,
    meanPulse_zero_before (2*d) n (by omega), sub_self]

theorem threeGeneratorDirection_periodic (d n : ℕ) :
    threeGeneratorDirection d (n+4*d) = threeGeneratorDirection d n := by
  unfold threeGeneratorDirection
  rw [show 4*d = (2*d)*2 by ring,
    periodic_multiple (meanPulse d) (2*d) (meanPulse_periodic d) 2 n]
  rw [show (2*d)*2 = 2*(2*d) by ring, meanPulse_periodic]

theorem threeGeneratorDirection_periodMean (d : ℕ) (hd : 0 < d) :
    periodMean (threeGeneratorDirection d) (4*d) = 0 := by
  have heq : threeGeneratorDirection d =
      (fun n => meanPulse d n + (-1 : ℝ)*meanPulse (2*d) n) := by
    ext n
    dsimp [threeGeneratorDirection]
    ring
  rw [heq, periodMean_add_mul]
  have hfirst : periodMean (meanPulse d) (4*d) = 1/2 := by
    rw [show 4*d = (2*d)*2 by ring,
      periodMean_multiple (meanPulse d) (2*d) 2 (by omega) (by omega)
        (meanPulse_periodic d), meanPulse_periodMean d hd]
  have hsecond : periodMean (meanPulse (2*d)) (4*d) = 1/2 := by
    rw [show 4*d = 2*(2*d) by ring,
      meanPulse_periodMean (2*d) (by omega)]
  rw [hfirst, hsecond]
  norm_num

/-- An explicit common period for the corrected witness. -/
theorem add_threeGenerator_periodic (F : ℕ → ℝ) (Q d : ℕ)
    (hper : ∀ n, F (n+Q) = F n) (u : ℝ) (n : ℕ) :
    F (n+Q*(4*d)) + u*threeGeneratorDirection d (n+Q*(4*d)) =
      F n + u*threeGeneratorDirection d n := by
  rw [periodic_multiple F Q hper (4*d) n,
    show Q*(4*d) = (4*d)*Q by ring,
    periodic_multiple (threeGeneratorDirection d) (4*d)
      (threeGeneratorDirection_periodic d) Q n]

theorem add_threeGenerator_zero_mean (F : ℕ → ℝ) (Q d : ℕ)
    (hQ : 0 < Q) (hd : 0 < d)
    (hper : ∀ n, F (n+Q) = F n) (hm : periodMean F Q = 0) (u : ℝ) :
    periodMean (fun n => F n + u*threeGeneratorDirection d n) (Q*(4*d)) = 0 := by
  rw [periodMean_add_mul,
    periodMean_multiple F Q (4*d) hQ (by omega) hper, hm]
  have hW : periodMean (threeGeneratorDirection d) (Q*(4*d)) = 0 := by
    rw [show Q*(4*d) = (4*d)*Q by ring,
      periodMean_multiple (threeGeneratorDirection d) (4*d) Q (by omega) hQ
        (threeGeneratorDirection_periodic d),
      threeGeneratorDirection_periodMean d hd]
  rw [hW]
  ring

theorem add_threeGenerator_mem_zeroMeanHeadClass (Y d : ℕ)
    (hYd : Y < d) (F : ℕ → ℝ) (hF : F ∈ zeroMeanHeadClass Y) (u : ℝ) :
    (fun n => F n + u*threeGeneratorDirection d n) ∈ zeroMeanHeadClass Y := by
  have hd : 0 < d := by omega
  obtain ⟨Q, hQ, hper, hm⟩ := hF.2
  refine ⟨add_mul_mem_conditionalHeadClass Y F (threeGeneratorDirection d) hF.1
    (threeGeneratorDirection_legal d hd)
    (fun n _ hn => threeGeneratorDirection_zero_before d n (by omega)) u,
    Q*(4*d), by positivity, ?_, ?_⟩
  · exact add_threeGenerator_periodic F Q d hper u
  · exact add_threeGenerator_zero_mean F Q d hQ hd hper hm u

/-- The concrete period grows at most linearly with the chosen scale. -/
theorem threeGenerator_common_period_bound (Q d D : ℕ) (hd : d ≤ D) :
    Q*(4*d) ≤ 4*Q*D := by
  calc
    Q*(4*d) = (4*Q)*d := by ring
    _ ≤ (4*Q)*D := Nat.mul_le_mul_left (4*Q) hd

/-- Nonzero actual correlation certifies a positive-energy direction. -/
theorem threeGenerator_energy_pos_of_correlation (F : ℕ → ℝ) (d : ℕ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (hd : 0 < d)
    (hi : conditionalMeanInner F (threeGeneratorDirection d) ≠ 0) :
    0 < conditionalMeanSquare (threeGeneratorDirection d) := by
  have hn := conditionalMeanSquare_nonneg (threeGeneratorDirection d)
  have hne : conditionalMeanSquare (threeGeneratorDirection d) ≠ 0 := by
    intro hz
    exact hi (conditionalMeanInner_eq_zero_of_energy_zero F
      (threeGeneratorDirection d) hF (threeGeneratorDirection_legal d hd) hz)
  exact lt_of_le_of_ne hn (Ne.symm hne)

/-- Exact optimal energy, membership and strict decrease for a detected scale.
No estimate on the magnitude of the positive decrease is asserted. -/
theorem threeGenerator_strict_improvement_of_correlation (Y d : ℕ)
    (hYd : Y < d) (F : ℕ → ℝ) (hF : F ∈ zeroMeanHeadClass Y)
    (hi : conditionalMeanInner F (threeGeneratorDirection d) ≠ 0) :
    let u := -conditionalMeanInner F (threeGeneratorDirection d) /
      conditionalMeanSquare (threeGeneratorDirection d)
    let G := fun n => F n + u*threeGeneratorDirection d n
    G ∈ zeroMeanHeadClass Y ∧
      conditionalMeanSquare G = conditionalMeanSquare F -
        (conditionalMeanInner F (threeGeneratorDirection d))^2 /
          conditionalMeanSquare (threeGeneratorDirection d) ∧
      conditionalMeanSquare G < conditionalMeanSquare F := by
  dsimp only
  have hd : 0 < d := by omega
  have hg := threeGenerator_energy_pos_of_correlation F d hF.1.1 hd hi
  have he := conditionalMeanSquare_optimal_scalar F (threeGeneratorDirection d)
    hF.1.1 (threeGeneratorDirection_legal d hd) (ne_of_gt hg)
  refine ⟨add_threeGenerator_mem_zeroMeanHeadClass Y d hYd F hF _, he, ?_⟩
  rw [he]
  exact sub_lt_self _ (div_pos (sq_pos_of_ne_zero hi) hg)

end RiemannResearch.RH.CRTBlock
