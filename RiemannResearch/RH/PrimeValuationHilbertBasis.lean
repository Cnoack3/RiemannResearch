/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Module
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
/-!
# A complete level basis for the actual prime-valuation subspace

Source: user-provided valuation/Meixner basis research direction,
20 October 2026; see FpOrthonormalBasisResearch20261020.md.
The subspace is defined by physical coordinate constancy on valuation fibers,
not by assuming a dense dictionary. Its closedness follows from coordinate
continuity. Exact-level indicators have positive geometric Zipf masses.
Their normalized Hilbert vectors are orthonormal, and orthogonality to every
level forces every positive coordinate to vanish, proving completeness.

This basis consists of indicators, not Meixner polynomials. It supplies a
complete actual valuation space for subsequent polynomial and target work.
It is not the legal squarefree closure.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimeValuationBasis
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity

/-- All actual Q-Hilbert vectors whose physical coordinates depend only on v_p. -/
def valuationSpace (p : ℕ) : Submodule ℝ QHilbert where
  carrier := {f | ∀ n : ℕ, n ≠ 0 →
    qSequence f n = qSequence f (p ^ n.factorization p)}
  zero_mem' := by
    intro n hn
    change qSequenceLinear 0 n = qSequenceLinear 0 _
    simp
  add_mem' := by
    intro f g hf hg n hn
    change qSequenceLinear (f + g) n = qSequenceLinear (f + g) _
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) (hf n hn) (hg n hn)
  smul_mem' := by
    intro c f hf n hn
    change qSequenceLinear (c • f) n = qSequenceLinear (c • f) _
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg (c * ·) (hf n hn)

/-- Valuation dependence is preserved by convergence in the full Q norm. -/
theorem valuationSpace_isClosed (p : ℕ) : IsClosed (valuationSpace p : Set QHilbert) := by
  change IsClosed {f : QHilbert | ∀ n : ℕ, n ≠ 0 →
    qSequence f n = qSequence f (p ^ n.factorization p)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro hn
  exact isClosed_eq (SquarefreeRadicalDifference.continuous_qSequence n)
    (SquarefreeRadicalDifference.continuous_qSequence _)

instance (p : ℕ) : CompleteSpace (valuationSpace p) :=
  (valuationSpace_isClosed p).completeSpace_coe

/-- Indicator vector of the exact valuation level k. -/
def valuationLevel (p k : ℕ) : QHilbert := qDivisor (p ^ k) - qDivisor (p ^ (k+1))
/-- The full Zipf mass of the exact level, as the difference of two divisibility tails. -/
def valuationMass (p k : ℕ) : ℝ :=
  1 / ((p : ℝ) ^ k)^2 - 1 / ((p : ℝ) ^ (k+1))^2

/-- Positive coordinates are exactly the indicator of v_p(n) = k. -/
theorem valuationLevel_sequence (p k n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (valuationLevel p k) n = if n.factorization p = k then 1 else 0 := by
  change qSequenceLinear (_ - _) n = _
  rw [map_sub]
  change qSequence (qDivisor (p ^ k)) n - qSequence (qDivisor (p ^ (k+1))) n = _
  simp only [qSequence_qDivisor, positiveDivisor, hn, ↓reduceIte,
    hp.pow_dvd_iff_le_factorization hn]
  split_ifs <;> try omega
  all_goals norm_num

/-- Each exact-level vector belongs to the physically defined valuation subspace. -/
theorem valuationLevel_mem (p k : ℕ) (hp : p.Prime) :
    valuationLevel p k ∈ valuationSpace p := by
  intro n hn
  rw [valuationLevel_sequence p k n hp hn,
    valuationLevel_sequence p k _ hp (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hp.factorization]

/-- Every valuation level has strictly positive mass. -/
theorem valuationMass_pos (p k : ℕ) (hp : p.Prime) : 0 < valuationMass p k := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h0 : (0 : ℝ) < (p : ℝ)^k := by positivity
  unfold valuationMass
  rw [sub_pos, one_div_lt_one_div (by positivity) (by positivity)]
  rw [pow_succ (p : ℝ) k, mul_pow]
  have hd : 0 < (p : ℝ)^2 - 1 := by nlinarith
  nlinarith [mul_pos (sq_pos_of_pos h0) hd]

/-- The exact mean of an entire valuation level, including its infinite tail. -/
theorem qOne_inner_valuationLevel (p k : ℕ) (hp : p.Prime) :
    inner ℝ qOne (valuationLevel p k) = valuationMass p k := by
  rw [valuationLevel, inner_sub_right,
    qOne_inner_qDivisor _ (pow_pos hp.pos _), qOne_inner_qDivisor _ (pow_pos hp.pos _)]
  simp [valuationMass, Nat.cast_pow]

/-- Pairing a valuation observable with a level reads its value times the level mass. -/
theorem inner_valuationLevel (p k : ℕ) (hp : p.Prime)
    (f : QHilbert) (hf : f ∈ valuationSpace p) :
    inner ℝ f (valuationLevel p k) =
      qSequence f (p ^ k) * valuationMass p k := by
  rw [← qOne_inner_valuationLevel p k hp, ← real_inner_smul_left]
  rw [qInner_eq_inversePowerMean, qInner_eq_inversePowerMean]
  unfold inversePowerMean
  apply tsum_congr
  intro n
  have hn : n + 1 ≠ 0 := Nat.succ_ne_zero _
  have h := hf (n+1) hn
  have hs : qSequence (qSequence f (p ^ k) • qOne) (n+1) = qSequence f (p ^ k) := by
    change qSequenceLinear (_ • qOne) (n+1) = _
    rw [map_smul]
    change qSequence f (p ^ k) * qSequence qOne (n+1) = _
    rw [qSequence_qOne]
    simp [qOneSequence]
  dsimp only
  rw [hs]
  rw [valuationLevel_sequence p k (n+1) hp hn]
  by_cases he : (n+1).factorization p = k
  · rw [he] at h
    simp only [he, if_pos, mul_one, h]
  · simp [he]

/-- Disjoint exact levels have a diagonal Gram matrix. -/
theorem valuationLevel_inner (p : ℕ) (hp : p.Prime) (j k : ℕ) :
    inner ℝ (valuationLevel p j) (valuationLevel p k) =
      if j = k then valuationMass p k else 0 := by
  rw [inner_valuationLevel p k hp _ (valuationLevel_mem p j hp),
    valuationLevel_sequence p j _ hp (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hp.factorization, eq_comm]


/-- A normalized exact-level vector in the actual valuation subspace. -/
def valuationUnit (p : ℕ) (hp : p.Prime) (k : ℕ) : valuationSpace p :=
  ⟨(Real.sqrt (valuationMass p k))⁻¹ • valuationLevel p k,
    (valuationSpace p).smul_mem _ (valuationLevel_mem p k hp)⟩

/-- The normalized level vectors are orthonormal under the actual Zipf law. -/
theorem valuationUnit_orthonormal (p : ℕ) (hp : p.Prime) :
    Orthonormal ℝ (valuationUnit p hp) := by
  rw [orthonormal_iff_ite]
  intro j k
  change inner ℝ ((Real.sqrt (valuationMass p j))⁻¹ • valuationLevel p j)
    ((Real.sqrt (valuationMass p k))⁻¹ • valuationLevel p k) = _
  rw [real_inner_smul_left, real_inner_smul_right, valuationLevel_inner p hp]
  by_cases he : j = k
  · subst j
    simp only [↓reduceIte]
    have hs0 : Real.sqrt (valuationMass p k) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (valuationMass_pos p k hp))
    have hs := Real.sq_sqrt (valuationMass_pos p k hp).le
    field_simp
    nlinarith [hs]
  · simp [he]

/-- The exact normalized level coefficient of any valuation observable. -/
theorem valuationUnit_coefficient (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p) (k : ℕ) :
    inner ℝ f (valuationUnit p hp k) =
      qSequence f.val (p ^ k) * Real.sqrt (valuationMass p k) := by
  change inner ℝ f.val ((Real.sqrt (valuationMass p k))⁻¹ • valuationLevel p k) = _
  rw [real_inner_smul_right, inner_valuationLevel p k hp f.val f.property]
  have hs0 : Real.sqrt (valuationMass p k) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (valuationMass_pos p k hp))
  have hs := Real.sq_sqrt (valuationMass_pos p k hp).le
  field_simp
  nlinarith [congrArg (fun x : ℝ => qSequence f.val (p ^ k) * x) hs]

/-- No nonzero valuation observable is orthogonal to every exact level. -/
theorem eq_zero_of_orthogonal_valuationUnit (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p) (hf : ∀ k, inner ℝ f (valuationUnit p hp k) = 0) :
    f = 0 := by
  have hv (k : ℕ) : qSequence f.val (p ^ k) = 0 := by
    have h := hf k
    rw [valuationUnit_coefficient] at h
    exact (mul_eq_zero.mp h).resolve_right
      (ne_of_gt (Real.sqrt_pos.mpr (valuationMass_pos p k hp)))
  apply Subtype.ext
  apply qSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    rw [f.property (n+1) (Nat.succ_ne_zero _), hv]
    change 0 = qSequenceLinear 0 (n+1)
    simp

/-- The normalized level vectors have dense span in the full valuation subspace. -/
theorem valuationUnit_span_dense (p : ℕ) (hp : p.Prime) :
    (Submodule.span ℝ (Set.range (valuationUnit p hp))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℝ (Set.range (valuationUnit p hp))
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm
    · intro f hf
      have hz : f = 0 := by
        apply eq_zero_of_orthogonal_valuationUnit p hp f
        intro k
        have hmem : valuationUnit p hp k ∈ K := Submodule.subset_span ⟨k, rfl⟩
        have he := hf _ hmem
        simpa only [real_inner_comm] using he
      simpa only [Submodule.mem_bot] using hz
    · exact bot_le
  change K.topologicalClosure = ⊤
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth,
    Submodule.bot_orthogonal_eq_top]

/-- A complete Hilbert basis of all square-integrable prime-valuation observables. -/
def valuationHilbertBasis (p : ℕ) (hp : p.Prime) :
    HilbertBasis ℕ ℝ (valuationSpace p) :=
  HilbertBasis.mk (valuationUnit_orthonormal p hp)
    (by rw [valuationUnit_span_dense])

@[simp] theorem valuationHilbertBasis_apply (p : ℕ) (hp : p.Prime) (k : ℕ) :
    valuationHilbertBasis p hp k = valuationUnit p hp k := by
  simp only [valuationHilbertBasis, HilbertBasis.coe_mk]

/-- Unconditional reconstruction in the actual Q norm, with every level included. -/
theorem valuation_hasSum (p : ℕ) (hp : p.Prime) (f : valuationSpace p) :
    HasSum (fun k => (qSequence f.val (p ^ k) * Real.sqrt (valuationMass p k)) •
      valuationUnit p hp k) f := by
  have hc (k : ℕ) : inner ℝ (valuationUnit p hp k) f =
      qSequence f.val (p ^ k) * Real.sqrt (valuationMass p k) := by
    rw [real_inner_comm, valuationUnit_coefficient]
  simpa only [HilbertBasis.repr_apply_apply, valuationHilbertBasis_apply, hc] using
    (valuationHilbertBasis p hp).hasSum_repr f

/-- Full geometric-weighted Parseval identity for every valuation observable. -/
theorem valuation_parseval (p : ℕ) (hp : p.Prime) (f : valuationSpace p) :
    (∑' k : ℕ, valuationMass p k * (qSequence f.val (p ^ k))^2) = ‖f‖^2 := by
  have h := (valuationHilbertBasis p hp).tsum_inner_mul_inner f f
  have hc (k : ℕ) :
      inner ℝ f (valuationUnit p hp k) * inner ℝ (valuationUnit p hp k) f =
        valuationMass p k * (qSequence f.val (p ^ k))^2 := by
    rw [real_inner_comm f (valuationUnit p hp k), valuationUnit_coefficient]
    nlinarith [Real.sq_sqrt (valuationMass_pos p k hp).le]
  simpa only [valuationHilbertBasis_apply, hc, real_inner_self_eq_norm_sq] using h

/-- The constant belongs to the actual valuation subspace. -/
theorem qOne_mem_valuationSpace (p : ℕ) (hp : p.Prime) :
    qOne ∈ valuationSpace p := by
  intro n hn
  rw [qSequence_qOne]
  simp [qOneSequence, hn, hp.ne_zero]

end RiemannResearch.RH.PrimeValuationBasis
