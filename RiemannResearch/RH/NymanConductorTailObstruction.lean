import RiemannResearch.RH.NymanActualTailEnergy
import RiemannResearch.Analysis.SubpowerTailObstruction
import RiemannResearch.RH.CountableZetaDetector
import Mathlib.Topology.Order.Bornology

/-!
# Artificial conductor zeros force canonical-tail energy

Source: continuation of the user-provided Nyman--Weil arithmetic-tail
argument, developed in this session from the exact transform and support
providers. The bounds concern actual integrals and the actual canonical
inverse-prefix construction. No RH hypothesis is used.

The nonzero artificial-zero signature is an explicit premise of the
obstruction. A final existence theorem supplies a concrete class of heads
that detect the actual zeta zeros and satisfy this obstruction. The more
general finite-jet argument in NymanConductorTailObstruction.md is not yet
formalized here.
-/

open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.RH
open MeasureTheory.BilateralLaplace
open ZetaConductorRegularization ArithmeticConductorCommonZeros

/-- Exact negative head signature at any zero of the full conductor multiplier. -/
theorem centeredTransform_nymanCompletionTail_of_conductorZeta_zero
    (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : conductorZeta n s = 0) :
    centeredTransform (nymanCompletionTail n M hn v) s =
      -centeredTransform (poleCancellationOperator v) s := by
  rw [centeredTransform_nymanCompletionTail_sub n M hn hv ha hb s,
    centeredTransform_nymanCompletedTest n M hn hv ha hb s, hs,
    mul_zero, zero_mul, zero_sub]

/-- Linear energy cost of an artificial conductor signature, without assuming
that the artificial point is a zeta zero. -/
theorem nymanCompletionTail_conductor_energy_lower_bound
    (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0) :
    Real.exp a * ((M + 1 : ℕ) : ℝ) *
      ‖centeredTransform (poleCancellationOperator v) s‖ ^ 2 ≤
        RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) := by
  have hre : s.re = 1 := conductorSymbol_zero_re n (by omega) s hP
  have hright : 1 / 2 < s.re := by rw [hre]; norm_num
  have hZ : conductorZeta n s = 0 := by
    rw [conductorZeta_of_ne_one n hs, hP, mul_zero]
  have h := RemoteLaplaceTail.supported_signature_energy_lower_bound
    (nymanCompletionTail n M hn v) s hright
    (a + Real.log (M + 1 : ℕ))
    (memLp_two_nymanCompletionTail n M hn hv ha hb)
    (fun y hy => nymanCompletionTail_zero_below n M hn ha hy)
    (centeredTransform (poleCancellationOperator v) s)
    (centeredTransform_nymanCompletionTail_of_conductorZeta_zero n M hn hv ha hb hZ)
  have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  simpa only [hre, show (2 : ℝ) * 1 - 1 = 1 by norm_num,
    one_mul, Real.exp_add, Real.exp_log hM] using h

/-- The canonical family cannot have subpower energy when this signature is nonzero. -/
theorem nymanCompletionTail_not_subpower_of_conductor_signature
    (n : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0)
    (hdetect : centeredTransform (poleCancellationOperator v) s ≠ 0) :
    ¬ (∀ ε : ℝ, 0 < ε → Tendsto
      (fun M : ℕ => Real.exp (-ε * Real.log (M + 1 : ℕ)) *
        RemoteLaplaceTail.energy (nymanCompletionTail n M hn v)) atTop (𝓝 0)) := by
  intro hgrowth
  apply hdetect
  have hre := conductorSymbol_zero_re n (by omega) s hP
  have hright : 1 / 2 < s.re := by rw [hre]; norm_num
  have hZ : conductorZeta n s = 0 := by
    rw [conductorZeta_of_ne_one n hs, hP, mul_zero]
  apply RemoteLaplaceTail.signature_eq_zero_of_supported_subpower_tail hright
    (fun M => memLp_two_nymanCompletionTail n M hn hv ha hb)
    (fun M y hy => nymanCompletionTail_zero_below n M hn ha hy)
    (centeredTransform (poleCancellationOperator v) s) _ hgrowth
  intro M
  exact centeredTransform_nymanCompletionTail_of_conductorZeta_zero n M hn hv ha hb hZ


/-- For every fixed conductor, a genuine compact zeta-detecting head can have
a strictly positive linear canonical-tail energy floor. Detector existence
alone cannot supply the RH growth premise. -/
theorem exists_zeta_detecting_potential_with_linear_conductor_tail
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (v : ℝ → ℂ) (a b C : ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧ HasCompactSupport v ∧
      (∀ x < a, v x = 0) ∧ (∀ x > b, v x = 0) ∧ 0 < C ∧
      (∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ →
        centeredTransform (poleCancellationOperator v) ρ ≠ 0) ∧
      ∀ M : ℕ, C * ((M + 1 : ℕ) : ℝ) ≤
        RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) := by
  let s : ℂ := 1 + (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) /
    (Real.log n : ℂ)
  have hP : conductorSymbol n s = 0 := by
    simpa only [s, Int.cast_one] using
      conductorSymbol_explicit_zero n (by omega) 1
  have hs1 : s ≠ 1 := by
    simpa only [s, Int.cast_one] using
      conductorSymbol_extra_zero_ne_one n (by omega) 1 (by norm_num)
  have hre : s.re = 1 := conductorSymbol_zero_re n (by omega) s hP
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [hre, Complex.zero_re] at this
    norm_num at this
  obtain ⟨f, hf, hfc, _, hf0, hf1, hd⟩ :=
    exists_smooth_compact_pole_annihilating_countable_detector
      (zeta_strip_zeros_countable.insert s)
      (by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact ⟨hs0, hs1⟩
        · refine ⟨?_, hz.not_trivial.2⟩
          intro he
          have hp := hz.2.1
          simp [he] at hp)
  let a : ℝ := sInf (tsupport f)
  let b : ℝ := sSup (tsupport f)
  have hsub : tsupport f ⊆ Set.Icc a b :=
    hfc.isBounded.subset_Icc_sInf_sSup
  have ha : ∀ x < a, f x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    exact (not_le_of_gt hx) (hsub hxt).1
  have hb : ∀ x > b, f x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    exact (not_le_of_gt hx) (hsub hxt).2
  obtain ⟨v, hv, hvc, hvs, hvf⟩ :=
    exists_compact_smooth_polarPotential hf ha hb hf0 hf1
  have hva : ∀ x < a, v x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    exact (not_le_of_gt hx) (hvs hxt).1
  have hvb : ∀ x > b, v x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    exact (not_le_of_gt hx) (hvs hxt).2
  let C : ℝ := Real.exp a * ‖centeredTransform f s‖ ^ 2
  have hC : 0 < C :=
    mul_pos (Real.exp_pos _) (pow_pos
      (norm_pos_iff.mpr (hd s (Set.mem_insert _ _))) 2)
  refine ⟨v, a, b, C, hv, hvc, hva, hvb, hC, ?_, ?_⟩
  · intro ρ hρ
    rw [hvf]
    exact hd ρ (Set.mem_insert_of_mem _ hρ)
  · intro M
    have h := nymanCompletionTail_conductor_energy_lower_bound n M hn
      hv hva hvb hs1 hP
    rw [hvf] at h
    dsimp [C]
    nlinarith


end RiemannResearch.RH
