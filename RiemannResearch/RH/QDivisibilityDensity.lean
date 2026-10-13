import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.NoorLogarithmDensity
import RiemannResearch.Analysis.CoefficientShift
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Completeness of the actual divisibility dictionary in the zeta-two space

Source: direct transfer of the already formalized finite Möbius-sieve density
in `NoorLogarithmDensity` through a coordinate shift and the exact inverse-square
normalization. No new dominated-convergence argument is needed here.

This is a theorem about all divisibility indicators, equivalently products of
finitely many prime-power divisibility indicators. It is not density of only
the individual prime-power indicators, nor density of legal residue atoms.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QDivisibilityDensity
open ZetaTwoProbability ZetaTwoHilbert
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.Noor

/-- The physical indicator 1_{d|n}, with the irrelevant zero coordinate removed. -/
def positiveDivisor (d n : ℕ) : ℝ :=
  if n = 0 then 0 else if d ∣ n then 1 else 0

theorem positiveDivisor_abs_le_one (d n : ℕ) : |positiveDivisor d n| ≤ 1 := by
  unfold positiveDivisor
  split_ifs <;> norm_num

def qDivisor (d : ℕ) : QHilbert :=
  encodeQ (positiveDivisor d)
    (boundedQ_square_summable _ 1 zero_le_one (positiveDivisor_abs_le_one d))

@[simp] theorem qSequence_qDivisor (d : ℕ) :
    qSequence (qDivisor d) = positiveDivisor d :=
  qSequence_encodeQ _ _ (by simp [positiveDivisor])

/-- Exact inverse-square normalization, including the positive-coordinate shift. -/
theorem sqrt_qWeight_mul_sqrt_zetaTwo (n : ℕ) :
    Real.sqrt (qWeight n) * Real.sqrt zetaTwo =
      1 / ((n + 1 : ℕ) : ℝ) := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : qWeight n * zetaTwo = 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    unfold qWeight positiveQWeight
    field_simp [hn, ne_of_gt zetaTwo_pos]
  rw [← Real.sqrt_mul (qWeight_pos n).le, he,
    Real.sqrt_div zero_le_one, Real.sqrt_one,
    Real.sqrt_sq (Nat.cast_nonneg (n + 1))]

/-- The existing Noor vector is exactly a nonzero scalar multiple of the
actual Q-encoded divisibility indicator after dropping its zero coordinate. -/
theorem leftShift_logVector_eq_qDivisor (d : ℕ) :
    leftShift (logVector d) = ((d : ℝ) * Real.sqrt zetaTwo) • qDivisor d := by
  apply Subtype.ext
  funext n
  change logSequence d (n + 1) =
    ((d : ℝ) * Real.sqrt zetaTwo) *
      (Real.sqrt (qWeight n) * positiveDivisor d (n + 1))
  by_cases hd : d ∣ n + 1
  · simp only [logSequence, hd, if_true, positiveDivisor, Nat.succ_ne_zero,
      if_false, mul_one]
    calc
      (d : ℝ) / ((n + 1 : ℕ) : ℝ) =
          (d : ℝ) * (Real.sqrt (qWeight n) * Real.sqrt zetaTwo) := by
        rw [sqrt_qWeight_mul_sqrt_zetaTwo]
        ring
      _ = _ := by ring
  · simp [logSequence, positiveDivisor, hd]

/-- Unconditional totality in the actual inverse-square Hilbert space. -/
theorem eq_zero_of_orthogonal_qDivisor (f : QHilbert)
    (hf : ∀ d : ℕ, 0 < d → inner ℝ f (qDivisor d) = 0) : f = 0 := by
  have hshift : rightShift f = 0 := by
    apply eq_zero_of_orthogonal_logVector
    · simp [rightShift]
    · intro d hd
      rw [shift_inner, leftShift_logVector_eq_qDivisor, inner_smul_right,
        hf d hd, mul_zero]
  apply Subtype.ext
  funext n
  have he := congrArg (fun g : Space => g (n + 1)) hshift
  simpa only [rightShift, cons_succ, lp.coeFn_zero, Pi.zero_apply] using he

/-- The full divisibility dictionary is dense. Composite divisors represent
the finite intersections of prime-power divisibility events. -/
theorem qDivisor_span_dense :
    (Submodule.span ℝ (Set.range (fun d : ℕ+ => qDivisor (d : ℕ)))).topologicalClosure =
      ⊤ := by
  let K : Submodule ℝ QHilbert :=
    Submodule.span ℝ (Set.range (fun d : ℕ+ => qDivisor (d : ℕ)))
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm
    · intro f hf
      have hz : f = 0 := by
        apply eq_zero_of_orthogonal_qDivisor
        intro d hd
        have hmem : qDivisor d ∈ K :=
          Submodule.subset_span ⟨(⟨d, hd⟩ : ℕ+), rfl⟩
        have he := hf (qDivisor d) hmem
        simpa only [real_inner_comm] using he
      simpa only [Submodule.mem_bot] using hz
    · exact bot_le
  change K.topologicalClosure = ⊤
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth,
    Submodule.bot_orthogonal_eq_top]

end RiemannResearch.RH.QDivisibilityDensity
