import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.RadicalDifferenceTotality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact radical differences of the actual squarefree optimizer

For a squarefree conductor, the residue atom's discrete jump depends only
on divisibility at the current site. Thus all actual squarefree stages,
and their target residuals obey
the same radical difference relation. Strong limits retain it. The reciprocal row is the complete
four-site signed pairing, written without a finite-support encoding.

These are exact unconditional identities. The reciprocal row is retained,
and its decay is not asserted. Source: the user-directed research continuation
and an independently developed sparse-dual extension, 8 October 2026.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.SquarefreeRadicalDifference

open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ZetaTwoHilbert
open UniqueFactorizationMonoid

/-- The exact jump retains the wrap at a divisible site. -/
theorem residueFraction_difference (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    residueFraction d m - residueFraction d (m - 1) =
      1 / (d : ℝ) - (if d ∣ m then 1 else 0) := by
  have hstep : m % d = ((m - 1) % d + 1) % d := by
    have he : m = (m - 1) + 1 := by omega
    calc
      m % d = ((m - 1) + 1) % d := congrArg (fun k : ℕ => k % d) he
      _ = ((m - 1) % d + 1) % d := by
        rw [Nat.add_mod]
        simp only [Nat.mod_eq_of_lt (by omega : 1 < d)]
  have hr : (m - 1) % d < d := Nat.mod_lt _ (by omega)
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by omega)
  by_cases hdiv : d ∣ m
  · have hmzero : m % d = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hprev : (m - 1) % d = d - 1 := by
      by_contra hne
      have hlt : (m - 1) % d + 1 < d := by omega
      rw [Nat.mod_eq_of_lt hlt] at hstep
      omega
    unfold residueFraction
    rw [if_pos hdiv, hmzero, hprev, Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_div]
    field_simp [hdR]
    ring
  · have hlt : (m - 1) % d + 1 < d := by
      by_contra hn
      have he : (m - 1) % d + 1 = d := by omega
      rw [he, Nat.mod_self] at hstep
      exact hdiv (Nat.dvd_of_mod_eq_zero hstep)
    rw [Nat.mod_eq_of_lt hlt] at hstep
    unfold residueFraction
    rw [if_neg hdiv, hstep, Nat.cast_add, Nat.cast_one]
    field_simp [hdR]
    ring

/-- Equal divisor events give equal complete residue differences. -/
theorem residueFraction_difference_eq_of_dvd_iff
    (d m a : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) (ha : 1 ≤ a)
    (hdiv : d ∣ m ↔ d ∣ a) :
    residueFraction d m - residueFraction d (m - 1) =
      residueFraction d a - residueFraction d (a - 1) := by
  rw [residueFraction_difference d m hd hm,
    residueFraction_difference d a hd ha]
  simp only [hdiv]

/-- Every squarefree atom's jump depends only on the radical of the site. -/
theorem residueFraction_difference_radical
    (d m : ℕ) (hd : 2 ≤ d) (hs : Squarefree d) (hm : 2 ≤ m) :
    residueFraction d m - residueFraction d (m - 1) =
      residueFraction d (radical m) - residueFraction d (radical m - 1) := by
  apply residueFraction_difference_eq_of_dvd_iff d m (radical m) hd
    (by omega) (Nat.radical_pos m)
  exact (dvd_radical_iff hs.isRadical (by omega : m ≠ 0)).symm

/-- Difference of two literal positive physical coordinates. -/
def qDifference (x : QHilbert) (m : ℕ) : ℝ :=
  qSequence x m - qSequence x (m - 1)

private theorem qSequence_add' (x y : QHilbert) (k : ℕ) :
    qSequence (x + y) k = qSequence x k + qSequence y k :=
  congrFun (qSequenceLinear.map_add x y) k

private theorem qSequence_sub' (x y : QHilbert) (k : ℕ) :
    qSequence (x - y) k = qSequence x k - qSequence y k :=
  congrFun (qSequenceLinear.map_sub x y) k

private theorem qSequence_smul' (c : ℝ) (x : QHilbert) (k : ℕ) :
    qSequence (c • x) k = c * qSequence x k :=
  congrFun (qSequenceLinear.map_smul c x) k

private theorem qSequence_zero' (k : ℕ) : qSequence (0 : QHilbert) k = 0 :=
  congrFun (map_zero qSequenceLinear) k

theorem qDifference_zero (m : ℕ) : qDifference 0 m = 0 := by
  simp only [qDifference, qSequence_zero', sub_self]

theorem qDifference_add (x y : QHilbert) (m : ℕ) :
    qDifference (x + y) m = qDifference x m + qDifference y m := by
  simp only [qDifference, qSequence_add']
  ring

theorem qDifference_sub (x y : QHilbert) (m : ℕ) :
    qDifference (x - y) m = qDifference x m - qDifference y m := by
  simp only [qDifference, qSequence_sub']
  ring

theorem qDifference_smul (c : ℝ) (x : QHilbert) (m : ℕ) :
    qDifference (c • x) m = c * qDifference x m := by
  simp only [qDifference, qSequence_smul']
  ring

theorem qDifference_qOne (m : ℕ) (hm : 2 ≤ m) :
    qDifference qOne m = 0 := by
  simp only [qDifference, qSequence_qOne]
  simp [qOneSequence, show m ≠ 0 by omega, show m - 1 ≠ 0 by omega]

/-- Every vector in the literal squarefree residue span obeys the relation. -/
theorem span_difference_eq_of_same_squarefree_divisors
    (S : Set ℕ) (hlegal : ∀ d ∈ S, Squarefree d ∧ 2 ≤ d)
    (m a : ℕ) (hm : 2 ≤ m) (ha : 2 ≤ a)
    (hdiv : ∀ d : ℕ, Squarefree d → 2 ≤ d → (d ∣ m ↔ d ∣ a))
    (x : QHilbert) (hx : x ∈ Submodule.span ℝ (qResidue '' S)) :
    qDifference x m = qDifference x a := by
  induction hx using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨d, hd, rfl⟩ := hw
      unfold qDifference
      simp only [qSequence_qResidue]
      exact residueFraction_difference_eq_of_dvd_iff d m a
        (hlegal d hd).2 (by omega) (by omega)
        (hdiv d (hlegal d hd).1 (hlegal d hd).2)
  | zero => rw [qDifference_zero, qDifference_zero]
  | add x y hx hy ihx ihy =>
      rw [qDifference_add, qDifference_add, ihx, ihy]
  | smul c x hx ih =>
      rw [qDifference_smul, qDifference_smul, ih]

/-- Radical reduction for every actual squarefree legal approximant. -/
theorem span_difference_radical
    (S : Set ℕ) (hlegal : ∀ d ∈ S, Squarefree d ∧ 2 ≤ d)
    (m : ℕ) (hm : 2 ≤ m) (x : QHilbert)
    (hx : x ∈ Submodule.span ℝ (qResidue '' S)) :
    qDifference x m = qDifference x (radical m) := by
  apply span_difference_eq_of_same_squarefree_divisors S hlegal
    m (radical m) hm (Nat.two_le_radical_iff.mpr hm) ?_ x hx
  intro d hs hd
  exact (dvd_radical_iff hs.isRadical (by omega : m ≠ 0)).symm

/-- The literal target residual retains the same identity, for every legal trial. -/
theorem trialResidual_difference_radical
    (S : Set ℕ) (hlegal : ∀ d ∈ S, Squarefree d ∧ 2 ≤ d)
    (m : ℕ) (hm : 2 ≤ m) (x : QHilbert)
    (hx : x ∈ Submodule.span ℝ (qResidue '' S)) :
    qDifference (qOne - x) m = qDifference (qOne - x) (radical m) := by
  rw [qDifference_sub, qDifference_sub, qDifference_qOne m hm,
    qDifference_qOne (radical m) (Nat.two_le_radical_iff.mpr hm),
    span_difference_radical S hlegal m hm x hx]

/-- Physical coordinate evaluation is continuous in the complete Q norm. -/
theorem continuous_qSequence (k : ℕ) :
    Continuous (fun x : QHilbert => qSequence x k) := by
  cases k with
  | zero => exact continuous_const
  | succ n =>
      change Continuous (fun x : QHilbert => x n / Real.sqrt (qWeight n))
      exact (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).continuous.div_const _

theorem continuous_qDifference (m : ℕ) :
    Continuous (fun x : QHilbert => qDifference x m) := by
  unfold qDifference
  exact (continuous_qSequence m).sub (continuous_qSequence (m - 1))

/-- Strong limits preserve the complete physical radical difference. -/
theorem limit_difference_radical
    (u : ℕ → QHilbert) (x : QHilbert) (hu : Tendsto u atTop (𝓝 x))
    (hidentity : ∀ n m : ℕ, 2 ≤ m →
      qDifference (u n) m = qDifference (u n) (radical m))
    (m : ℕ) (hm : 2 ≤ m) :
    qDifference x m = qDifference x (radical m) := by
  have hleft := ((continuous_qDifference m).continuousAt.tendsto).comp hu
  have hright := ((continuous_qDifference (radical m)).continuousAt.tendsto).comp hu
  have heq : (fun n => qDifference (u n) m) =
      (fun n => qDifference (u n) (radical m)) := by
    funext n
    exact hidentity n m hm
  simp only [Function.comp_def] at hleft hright
  rw [← heq] at hright
  exact tendsto_nhds_unique hleft hright

/-- Exact algebraic recovery; the reciprocal difference remains signed. -/
theorem reciprocal_difference_recovery (x : QHilbert) (m : ℕ) (hm : 2 ≤ m) :
    qSequence x m / (m : ℝ) =
      qDifference x m - ((m : ℝ) - 1) * qDifference (reciprocalD x) m := by
  have hmR : (1 : ℝ) < m := by
    exact_mod_cast (show 1 < m by omega)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans hmR)
  have hprevne : (m : ℝ) - 1 ≠ 0 := by linarith
  unfold qDifference
  rw [qSequence_reciprocalD, qSequence_reciprocalD,
    Nat.cast_sub (by omega : 1 ≤ m)]
  norm_num only [Nat.cast_one]
  field_simp [hmne, hprevne]
  ring

/-- Complete signed reciprocal dual row: all four physical sites survive. -/
def reciprocalRadicalRow (x : QHilbert) (m : ℕ) : ℝ :=
  qDifference (reciprocalD x) m - qDifference (reciprocalD x) (radical m)

/-- Recover a physical coordinate from the radical base and the exact row. -/
theorem reciprocal_radical_row_recovery
    (x : QHilbert) (m : ℕ) (hm : 2 ≤ m)
    (hidentity : qDifference x m = qDifference x (radical m)) :
    qSequence x m / (m : ℝ) =
      qDifference x (radical m) - ((m : ℝ) - 1) *
        (qDifference (reciprocalD x) (radical m) + reciprocalRadicalRow x m) := by
  rw [reciprocal_difference_recovery x m hm, hidentity]
  unfold reciprocalRadicalRow
  ring

/-- Literal inverse-square summability of the normalized physical values. -/
theorem qNormalized_square_summable (x : QHilbert) :
    Summable (fun k : ℕ => (qSequence x k / (k : ℝ)) ^ 2) := by
  have hs := (qSequence_square_summable x).mul_left
    RiemannResearch.RH.ZetaTwoProbability.zetaTwo
  apply hs.congr
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hZ := ne_of_gt RiemannResearch.RH.ZetaTwoProbability.zetaTwo_pos
    unfold positiveQWeight
    field_simp [hkR, hZ]

/-- The two full radical difference families have trivial common kernel
in the actual inverse-square Hilbert space. Neither family is omitted. -/
theorem eq_zero_of_radical_differences_and_reciprocal_rows
    (x : QHilbert)
    (hrad : ∀ m : ℕ, 2 ≤ m → qDifference x m = qDifference x (radical m))
    (hrows : ∀ m : ℕ, 2 ≤ m → reciprocalRadicalRow x m = 0) : x = 0 := by
  have hphysical :=
    RiemannResearch.Analysis.RadicalDifferenceTotality.zero_of_summable_radical_invariant_differences
      (qSequence_zero x) (qNormalized_square_summable x)
      (by simpa [qDifference, RiemannResearch.Analysis.RadicalDifferenceTotality.backwardDifference]
        using hrad)
      (by
        intro m hm
        have h := hrows m hm
        unfold reciprocalRadicalRow qDifference at h
        simp only [qSequence_reciprocalD] at h
        exact sub_eq_zero.mp h)
  apply qSequence_injective
  funext k
  simpa only [qSequence_zero'] using hphysical k

end RiemannResearch.RH.SquarefreeRadicalDifference
