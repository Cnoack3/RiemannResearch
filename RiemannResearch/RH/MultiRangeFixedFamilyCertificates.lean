import RiemannResearch.RH.MultiRangeOptimizerConvergence
import RiemannResearch.RH.MultiRangeFiniteMinimum
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixInverse

/-! Unconditional convergence for each fixed finite anchored divisor family.
The limit is the actual attained infinite-energy minimum, with full signed
Gram interactions. All constants here depend on the fixed family. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro Analysis.FiniteSignedQuadratic
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

theorem anchorGram_eq_finiteMeanGram {D : ℕ} (A : ℕ) (d : Fin D → ℕ) :
    anchorGram A d = finiteMeanGram (fun i => divisorAnchorDirection A (d i)) := by
  ext i j
  unfold anchorGram finiteMeanGram conditionalTailPairing conditionalMeanInner
  apply tsum_congr
  intro k
  simp only [Nat.add_zero]
  ring

theorem anchorFiniteMeanOptimizer_eq {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) :
    finiteMeanOptimizer F (fun i => divisorAnchorDirection A (d i)) =
      -anchorInverseCoeff A d hA hd hinj F := by
  unfold anchorInverseCoeff
  rw [gramEquiv_symm_eq_inv_mulVec, anchorGram_eq_finiteMeanGram]
  rfl

theorem anchorPrefixOptimizer_tendsto {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    Tendsto (prefixMeanOptimizer F (fun i => divisorAnchorDirection A (d i))) atTop
      (𝓝 (-anchorInverseCoeff A d hA hd hinj F)) := by
  rw [← anchorFiniteMeanOptimizer_eq A d hA hd hinj F]
  apply prefixMeanOptimizer_tendsto F _ hF
  · intro i
    exact divisorAnchorDirection_legal A (d i) hA (by have := (hd i).1; omega)
  · rw [← anchorGram_eq_finiteMeanGram]
    exact (anchorGram_posDef A d hA hd hinj).det_pos.ne'

theorem anchorAffineEnergy_continuous {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 0 < d i) (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    Continuous (fun x : Fin D → ℝ =>
      conditionalMeanSquare (fun n => F n + anchorSynthesis A d x n)) := by
  have he : (fun x : Fin D → ℝ => conditionalMeanSquare
      (fun n => F n + anchorSynthesis A d x n)) =
      (fun x => conditionalMeanSquare F + 2 * (∑ i, x i * anchorSource A d F i) +
        quadratic (anchorGram A d) x) := by
    funext x
    exact anchor_affine_energy A d hA hd F hF x
  rw [he]
  unfold quadratic
  fun_prop

/-- Both bounds converge to the same actual infinite-energy minimum. The upper
bound uses the explicit eventual coefficient bound derived from convergence.
The finite-prefix points are the actual inverse-Gram coefficients. -/
theorem anchorFixedFamily_certificates_tendsto {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ t, |cesaro F t| ≤ B) :
    let U := fun i => divisorAnchorDirection A (d i)
    let x := prefixMeanOptimizer F U
    let FN := fun N n => F n + anchorSynthesis A d (x N) n
    let L := B + ∑ i, (|finiteMeanOptimizer F U i|+1)*(((A : ℝ)/(d i : ℝ)+1)/2)
    let Emin := conditionalMeanSquare (fun n => F n + anchorSynthesis A d
      (-anchorInverseCoeff A d hA hd hinj F) n)
    Tendsto (fun N => conditionalMeanPrefix (FN N) N) atTop (𝓝 Emin) ∧
    Tendsto (fun N => conditionalMeanUpperCertificate (FN N) L N) atTop (𝓝 Emin) := by
  dsimp only
  let U := fun i => divisorAnchorDirection A (d i)
  let x := prefixMeanOptimizer F U
  let FN := fun N n => F n + anchorSynthesis A d (x N) n
  let L := B + ∑ i, (|finiteMeanOptimizer F U i|+1)*(((A : ℝ)/(d i : ℝ)+1)/2)
  let Emin := conditionalMeanSquare (fun n => F n + anchorSynthesis A d
    (-anchorInverseCoeff A d hA hd hinj F) n)
  change Tendsto (fun N => conditionalMeanPrefix (FN N) N) atTop (𝓝 Emin) ∧
    Tendsto (fun N => conditionalMeanUpperCertificate (FN N) L N) atTop (𝓝 Emin)
  have hd0 : ∀ i, 0 < d i := fun i => by have := (hd i).1; omega
  have hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1) :=
    fun i => divisorAnchorDirection_legal A (d i) hA (hd0 i)
  have hdet : (finiteMeanGram U).det ≠ 0 := by
    rw [show finiteMeanGram U = anchorGram A d from (anchorGram_eq_finiteMeanGram A d).symm]
    exact (anchorGram_posDef A d hA hd hinj).det_pos.ne'
  have hlegal (N : ℕ) : FN N ∈ legalSeedSpan (Set.Ici 1) :=
    (legalSeedSpan _).add_mem hF (anchorSynthesis_legal A d (x N) hA hd0)
  have hL : 0 ≤ L := by
    dsimp [L]
    apply add_nonneg hB
    apply Finset.sum_nonneg
    intro i _
    positivity
  have hmean : ∀ᶠ N in atTop, ∀ t, |cesaro (FN N) t| ≤ L :=
    prefixMeanOptimizer_mean_eventually_bounded F U hF hU hdet B
      (fun i => ((A : ℝ)/(d i : ℝ)+1)/2) (by intro i; positivity) hb
      (fun i t => divisorAnchorDirection_mean_bound A (d i) t hA (hd0 i))
  have henergy : Tendsto (fun N => conditionalMeanSquare (FN N)) atTop (𝓝 Emin) :=
    (anchorAffineEnergy_continuous A d hA hd0 F hF).continuousAt.tendsto.comp
      (anchorPrefixOptimizer_tendsto A d hA hd hinj F hF)
  have hwidth : Tendsto (fun N : ℕ => 2 / ((N : ℝ)+2)*L^2) atTop (𝓝 0) := by
    have hh := conditionalMeanUpperCertificate_tendsto (fun _ => 0)
      (legalSeedSpan (Set.Ici 1)).zero_mem L hL (by intro t; simpa [cesaro] using hL)
    unfold conditionalMeanUpperCertificate at hh
    simpa [conditionalMeanPrefix, conditionalMeanSquare, cesaro] using hh
  have hgap : Tendsto (fun N => conditionalMeanSquare (FN N) -
      conditionalMeanPrefix (FN N) N) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hwidth
    · filter_upwards [hmean] with N hN
      obtain ⟨hc1, hc2⟩ := conditionalMeanSquare_finite_certificate (FN N) (hlegal N) N L hL
        (fun t _ => hN t)
      change conditionalMeanPrefix (FN N) N ≤ conditionalMeanSquare (FN N) at hc1
      exact sub_nonneg.mpr hc1
    · filter_upwards [hmean] with N hN
      obtain ⟨hc1, hc2⟩ := conditionalMeanSquare_finite_certificate (FN N) (hlegal N) N L hL
        (fun t _ => hN t)
      change conditionalMeanSquare (FN N) ≤ conditionalMeanPrefix (FN N) N + _ at hc2
      linarith [hc2]
  have hprefix : Tendsto (fun N => conditionalMeanPrefix (FN N) N) atTop (𝓝 Emin) := by
    have hh := henergy.sub hgap
    simpa only [sub_sub_cancel, sub_zero] using hh
  refine ⟨hprefix, ?_⟩
  have hh := hprefix.add hwidth
  simpa only [add_zero, conditionalMeanUpperCertificate] using hh

end RiemannResearch.RH.Pareto
