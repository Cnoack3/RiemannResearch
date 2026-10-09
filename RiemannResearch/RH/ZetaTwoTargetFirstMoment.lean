import RiemannResearch.RH.ZetaTwoConductorFiveBound
import RiemannResearch.RH.ZetaTwoResolvent
import RiemannResearch.RH.ZetaTwoRadicalFourBound
import RiemannResearch.RH.ZetaTwoParetoTransfer

/-!
# Target-specific first moments of the actual squarefree optimizer

Source: user-requested paper consequence in
`RH/ConductorRecoveryStatus20261009.md`, section 4, and independently developed
exact first-moment and Mobius-displacement assembly, 9 October 2026.

The universal reciprocal-form cap is used only on the complete screened
vector. No radical compatibility is assumed for that vector. All residuals,
normal equations, projections and correction terms are the actual QHilbert
objects; the complete physical sums and both optimizer correction squares
are retained. Cofinal first-moment decay is an explicit open arithmetic
provider, not an unconditional conclusion.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.ZetaTwoTargetFirstMoment
open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoReciprocalBound
open ZetaTwoConductorFiveBound ZetaTwoResolvent
open scoped BigOperators
def firstMoment (n : ℕ) : ℝ :=
  inner ℝ (residual n) (reciprocalD (residual n)) / error n

theorem firstMoment_nonneg (n : ℕ) : 0 ≤ firstMoment n :=
  div_nonneg (reciprocalD_positive _) (error_pos n).le

theorem screenedResidual_sq_le_firstMoment (n : ℕ) (hn : 4 ≤ n) :
    ‖screenedResidual n‖ ^ 2 ≤ (10745 / 28906 : ℝ) *
      inner ℝ (residual n) (reciprocalD (residual n)) := by
  have hg := stage_contains_two_three n (by omega)
  have hg5 := stage_contains_five n hn
  exact screened_sq_le_firstMoment (10745 / 28906) (by norm_num) (stage n)
    (fun f hf => conductorFive_firstMoment_le_margin f
      (((stage n).mem_orthogonal _).mp hf _ hg.1)
      (((stage n).mem_orthogonal _).mp hf _ hg.2)
      (((stage n).mem_orthogonal _).mp hf _ hg5)) (residual n)

theorem secondMoment_le_firstMoment (n : ℕ) (hn : 4 ≤ n) :
    secondMoment n ≤ (10745 / 28906 : ℝ) * firstMoment n := by
  unfold secondMoment firstMoment
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (screenedResidual_sq_le_firstMoment n hn)
    (error_pos n).le

theorem firstMoment_sq_le_secondMoment (n : ℕ) :
    (firstMoment n) ^ 2 ≤ secondMoment n := by
  have hc := real_inner_mul_inner_self_le (residual n) (screenedResidual n)
  rw [residual_inner_screened, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hc
  unfold firstMoment secondMoment
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos (error_pos n) 2) (error_pos n)).mpr
  have hc' : (inner ℝ (residual n) (reciprocalD (residual n))) ^ 2 ≤
      error n * ‖screenedResidual n‖ ^ 2 := by simpa only [pow_two, error] using hc
  have hp := mul_le_mul_of_nonneg_right hc' (error_pos n).le
  nlinarith


theorem firstMoment_pos (n : ℕ) : 0 < firstMoment n := by
  apply div_pos _ (error_pos n)
  have ha := reciprocalD_positive (residual n)
  by_contra h
  have hz : inner ℝ (residual n) (reciprocalD (residual n)) = 0 := by
    linarith
  exact residual_ne_zero n (reciprocalD_faithful _ hz)

theorem firstMoment_le_sqrt_secondMoment (n : ℕ) :
    firstMoment n ≤ Real.sqrt (secondMoment n) := by
  have hsq := firstMoment_sq_le_secondMoment n
  have hnon : 0 ≤ secondMoment n :=
    div_nonneg (sq_nonneg _) (error_pos n).le
  have hsqrt := Real.sq_sqrt hnon
  nlinarith [firstMoment_nonneg n, Real.sqrt_nonneg (secondMoment n)]

/-- The complete physical reciprocal sum; no head or tail is truncated. -/
theorem firstMoment_physical (n : ℕ) :
    firstMoment n =
      (∑' k : ℕ, positiveQWeight k *
        (qSequence (residual n) k) ^ 2 / (k : ℝ)) / error n := by
  unfold firstMoment
  rw [reciprocalD_inner_physical]

/-- Both ordinary screening and the weighted optimizer mismatch are retained. -/
theorem completeCorrection_le_firstMoment (n : ℕ) (hn : 4 ≤ n) :
    (quarticFloor n + weightedMismatch n - screening n) / error n ≤
      (10745 / 28906 : ℝ) * firstMoment n := by
  have h := secondMoment_le_firstMoment n hn
  rw [secondMoment, screenedResidual_energy_exact, signedCorrection,
    ← add_sub_assoc] at h
  exact h

/-- Exact normalized complete head-tail identity precedes its estimate. -/
theorem firstMoment_gap_exact (n : ℕ) :
    (3 / 8 : ℝ) - firstMoment n =
      (tailEnergy (3 / 8) (residual n) - headEnergy (3 / 8) (residual n)) /
        (ZetaTwoProbability.zetaTwo * error n) := by
  have h := reciprocal_gap_exact (3 / 8) (residual n)
  unfold firstMoment
  rw [← h]
  change (3 / 8 : ℝ) -
    inner ℝ (residual n) (reciprocalD (residual n)) / error n =
    ZetaTwoProbability.zetaTwo * ((3 / 8 : ℝ) * error n -
      inner ℝ (residual n) (reciprocalD (residual n))) /
        (ZetaTwoProbability.zetaTwo * error n)
  field_simp [ne_of_gt ZetaTwoProbability.zetaTwo_pos, ne_of_gt (error_pos n)]


theorem firstMoment_le_margin (n : ℕ) (hn : 4 ≤ n) :
    firstMoment n ≤ (10745 / 28906 : ℝ) := by
  have hg := stage_contains_two_three n (by omega)
  have hg5 := stage_contains_five n hn
  unfold firstMoment
  apply (div_le_iff₀ (error_pos n)).mpr
  exact conductorFive_firstMoment_le_margin (residual n)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg.1)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg.2)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg5)

/-- Use the signed target pairing before Cauchy: this improves recovery
over replacing the first moment by the square root of the second. -/
theorem error_le_harmonic_firstMoment (n M : ℕ) (hM : 0 < M) :
    error n ≤ (ZetaTwoResolvent.harmonic M / ZetaTwoProbability.zetaTwo) *
      (firstMoment n + 1 / (M : ℝ)) := by
  have h := stage_resolvent_cauchy n M hM
  have he : inner ℝ (residual n) (reciprocalD (residual n)) =
      error n * firstMoment n := by
    unfold firstMoment
    field_simp [ne_of_gt (error_pos n)]
  rw [he] at h
  have hh : error n * error n ≤ error n *
      ((ZetaTwoResolvent.harmonic M / ZetaTwoProbability.zetaTwo) *
        (firstMoment n + 1 / (M : ℝ))) := by nlinarith only [h]
  by_contra hbad
  have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hbad) (error_pos n)
  exact (not_lt_of_ge hh) hlt

theorem mem_closure_of_cofinal_firstMoment
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hfirst : Tendsto (fun j => firstMoment (κ j)) atTop (𝓝 0)) :
    qOne ∈ closure := by
  apply mem_closure_of_cofinal_secondMoment κ hκ
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun j =>
      div_nonneg (sq_nonneg _) (error_pos (κ j)).le))
  · filter_upwards [hκ.eventually (Filter.eventually_ge_atTop 4)] with j hj
    exact secondMoment_le_firstMoment (κ j) hj
  · simpa using hfirst.const_mul (10745 / 28906 : ℝ)

theorem firstMoment_tendsto_zero_of_mem_closure (h : qOne ∈ closure) :
    Tendsto firstMoment atTop (𝓝 0) := by
  have hsecond := secondMoment_tendsto_zero_of_mem_closure h
  have hsqrt : Tendsto (fun n => Real.sqrt (secondMoment n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsecond
  exact squeeze_zero firstMoment_nonneg firstMoment_le_sqrt_secondMoment hsqrt

/-- Exact all-stage closure criterion; its decay provider remains open. -/
theorem mem_closure_iff_firstMoment :
    qOne ∈ closure ↔ Tendsto firstMoment atTop (𝓝 0) :=
  ⟨firstMoment_tendsto_zero_of_mem_closure,
    fun h => mem_closure_of_cofinal_firstMoment id tendsto_id h⟩

/-- A common cofinal sequence suffices; no monotonicity is imposed on moments. -/
theorem mem_closure_iff_cofinal_firstMoment :
    qOne ∈ closure ↔ ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧
      Tendsto (fun j => firstMoment (κ j)) atTop (𝓝 0) := by
  constructor
  · intro h
    exact ⟨id, tendsto_id, firstMoment_tendsto_zero_of_mem_closure h⟩
  · rintro ⟨κ, hκ, hm⟩
    exact mem_closure_of_cofinal_firstMoment κ hκ hm

open RiemannResearch.LinearAlgebra
/-- The literal squarefree Möbius trial is a member of the actual stage. -/
theorem mobiusTrial_mem_stage (n : ℕ) : mobiusTrial n ∈ stage n := by
  unfold mobiusTrial finiteSchurCombination
  apply (stage n).sum_mem
  intro i hi
  apply (stage n).smul_mem
  unfold stage RiemannResearch.Analysis.ExhaustiveWalk.walkSpan
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The full optimizer displacement is legal, without any bound on its size. -/
theorem optimizer_sub_mobiusTrial_mem_stage (n : ℕ) :
    optimizer n - mobiusTrial n ∈ stage n := by
  exact (stage n).sub_mem ((stage n).starProjection_apply_mem qOne)
    (mobiusTrial_mem_stage n)

/-- The displacement coefficients are exactly `c_i + μ(i+2)` for actual
normal-equation optimizer coefficients. Zero dictionary atoms remain legal
and no inverse of a redundant Gram matrix is assumed. -/
theorem exists_mobius_displacement_coefficients (n : ℕ) :
    ∃ c : Fin n → ℝ,
      finiteSchurCombination (fun i : Fin n => squarefreeAtom i) c = optimizer n ∧
      (∀ i : Fin n, inner ℝ (squarefreeAtom i)
        (finiteSchurCombination (fun j : Fin n => squarefreeAtom j) c) =
          inner ℝ (squarefreeAtom i) qOne) ∧
      finiteSchurCombination (fun i : Fin n => squarefreeAtom i)
        (fun i => c i + (ArithmeticFunction.moebius (i.val + 2) : ℝ)) =
          optimizer n - mobiusTrial n := by
  obtain ⟨c, hc, hnormal⟩ := exists_optimizer_coefficients n
  refine ⟨c, hc, hnormal, ?_⟩
  rw [← hc]
  unfold mobiusTrial finiteSchurCombination
  simp only [add_smul, neg_smul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, sub_neg_eq_add]

/-- The complete trial error equals the optimizer error plus the full
ordinary optimizer displacement square. -/
theorem mobiusTrial_norm_exact (n : ℕ) :
    ‖qOne - mobiusTrial n‖ ^ 2 =
      error n + ‖optimizer n - mobiusTrial n‖ ^ 2 := by
  have horth : inner ℝ (residual n) (optimizer n - mobiusTrial n) = 0 := by
    rw [real_inner_comm]
    exact ((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _
      (optimizer_sub_mobiusTrial_mem_stage n)
  have he : qOne - mobiusTrial n =
      residual n + (optimizer n - mobiusTrial n) := by
    unfold ZetaTwoOptimizerStage.residual
    abel
  rw [he, norm_add_sq_real, horth]
  unfold error
  ring

/-- The actual error retains the entire moving optimizer displacement. -/
theorem error_eq_mobiusTrial_sub_displacement (n : ℕ) :
    error n = ‖qOne - mobiusTrial n‖ ^ 2 -
      ‖optimizer n - mobiusTrial n‖ ^ 2 := by
  have h := mobiusTrial_norm_exact n
  linarith

/-- Exact signed reciprocal-form expansion of the actual residual.
Both the moving displacement square in the positive reciprocal form and
the signed cross pairing remain. Every pairing is in the actual Hilbert
space and therefore includes the entire infinite arithmetic tail. -/
theorem reciprocalEnergy_eq_mobiusTrial_signed_displacement (n : ℕ) :
    inner ℝ (residual n) (reciprocalD (residual n)) =
      inner ℝ (qOne - mobiusTrial n) (reciprocalD (qOne - mobiusTrial n)) -
      2 * inner ℝ (qOne - mobiusTrial n)
        (reciprocalD (optimizer n - mobiusTrial n)) +
      inner ℝ (optimizer n - mobiusTrial n)
        (reciprocalD (optimizer n - mobiusTrial n)) := by
  let R : QHilbert := qOne - mobiusTrial n
  let U : QHilbert := optimizer n - mobiusTrial n
  have he : residual n = R - U := by
    dsimp [R, U, ZetaTwoOptimizerStage.residual]
    abel
  have hcross : inner ℝ U (reciprocalD R) = inner ℝ R (reciprocalD U) := by
    rw [real_inner_comm, reciprocalD_symmetric]
  change inner ℝ (residual n) (reciprocalD (residual n)) =
    inner ℝ R (reciprocalD R) - 2 * inner ℝ R (reciprocalD U) +
      inner ℝ U (reciprocalD U)
  rw [he, map_sub]
  simp only [inner_sub_left, inner_sub_right]
  rw [hcross]
  ring



/-- Exact normalized Mobius correction identity, including the full signed
cross pairing and both complete displacement energies. -/
theorem firstMoment_eq_mobius_signed_displacement (n : ℕ) :
    firstMoment n =
      (inner ℝ (qOne - mobiusTrial n) (reciprocalD (qOne - mobiusTrial n)) -
        2 * inner ℝ (qOne - mobiusTrial n)
          (reciprocalD (optimizer n - mobiusTrial n)) +
        inner ℝ (optimizer n - mobiusTrial n)
          (reciprocalD (optimizer n - mobiusTrial n))) /
      (‖qOne - mobiusTrial n‖ ^ 2 - ‖optimizer n - mobiusTrial n‖ ^ 2) := by
  unfold firstMoment
  rw [reciprocalEnergy_eq_mobiusTrial_signed_displacement,
    error_eq_mobiusTrial_sub_displacement]

/-- The actual residual has its proved radical constraint. This cap is not
asserted for the screened reciprocal image. -/
theorem firstMoment_le_radical_margin (n : ℕ) (hn : 4 ≤ n) :
    firstMoment n ≤ (39138061 / 126426000 : ℝ) :=
  ZetaTwoRadicalFourBound.residual_firstMoment_normalized_le_margin n hn

theorem secondMoment_le_radical_margin (n : ℕ) (hn : 4 ≤ n) :
    secondMoment n ≤ (84107693089 / 730893991200 : ℝ) := by
  calc
    _ ≤ (10745 / 28906 : ℝ) * firstMoment n := secondMoment_le_firstMoment n hn
    _ ≤ (10745 / 28906 : ℝ) * (39138061 / 126426000 : ℝ) :=
      mul_le_mul_of_nonneg_left (firstMoment_le_radical_margin n hn) (by norm_num)
    _ = _ := by norm_num

/-- The fixed saving bounds the entire signed correction assembly. -/
theorem completeCorrection_le_radical_margin (n : ℕ) (hn : 4 ≤ n) :
    (quarticFloor n + weightedMismatch n - screening n) / error n ≤
      (84107693089 / 730893991200 : ℝ) := by
  have h := secondMoment_le_radical_margin n hn
  rw [secondMoment, screenedResidual_energy_exact, signedCorrection,
    ← add_sub_assoc] at h
  exact h

/-- Conditional research reduction: the cofinal normalized arithmetic saving
is the sole displayed provider. It remains open. -/
theorem riemannHypothesis_of_cofinal_firstMoment
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hfirst : Tendsto (fun j => firstMoment (κ j)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
    (mem_closure_of_cofinal_firstMoment κ hκ hfirst)

end RiemannResearch.RH.ZetaTwoTargetFirstMoment
