import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.LinearAlgebra.RankTwoWoodbury
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Totient

/-!
# Rank-two reduction for the existing DPP occupation probability

Source: user-provided Ramanujan / Green / Schur calculation,
22 September 2026; this supplies the definitions and finite reduction.

The probability is the canonical `IntegerDPP.qN`. The packet Gram and its
inverse come from the actual full Pareto Hilbert vectors. The displayed
rank-two evaluation of that Gram, the inverse of its cotangent component,
and the nonzero two-dimensional Schur denominator remain explicit premises.
This does not claim a uniform bound or limiting saturation.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.LinearAlgebra.RankTwoWoodbury

def finiteTotientSource (n : ℕ) (i : Fin n) : ℝ :=
  (Nat.totient (i.val + 2) : ℝ)

def finiteVonMangoldtSource (n : ℕ) (i : Fin n) : ℝ :=
  ArithmeticFunction.vonMangoldt (i.val + 2)

/-- A conditional finite algebraic evaluation of the genuine occupation
probability. In particular, the marked inverse quadratic is not postulated.
-/
theorem qN_eq_rankTwo_markedFormula
    (n : ℕ) (F R : Matrix (Fin n) (Fin n) ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hXi : finitePacketGram n =
      rankTwoMatrix Real.pi F (finiteVonMangoldtSource n) (finiteTotientSource n))
    (hD :
      ((finiteTotientSource n) ⬝ᵥ (R *ᵥ (finiteTotientSource n))) *
        ((finiteVonMangoldtSource n) ⬝ᵥ (R *ᵥ (finiteVonMangoldtSource n))) -
      ((finiteTotientSource n) ⬝ᵥ (R *ᵥ (finiteVonMangoldtSource n)) +
        2 * Real.pi) ^ 2 ≠ 0) :
    IntegerDPP.qN n = progressionWeight (IntegerDPP.residueModulus n) 1 *
      markedFormula Real.pi R (finiteTotientSource n)
        (finiteVonMangoldtSource n) (finiteMoebiusSource n) := by
  let y : Fin n → ℝ :=
    inverseSource (finitePacket_independent n) (finiteMoebiusSource n)
  have hy : finitePacketGram n *ᵥ y = finiteMoebiusSource n := by
    rw [finitePacketGram, gramMatrix_mulVec]
    funext i
    exact inverseSource_normal (finitePacket_independent n) (finiteMoebiusSource n) i
  have hquad := solved_marked_quadratic Real.pi F R (finitePacketGram n)
    (finiteTotientSource n) (finiteVonMangoldtSource n) (finiteMoebiusSource n) y
    hRF hR hXi hy Real.pi_ne_zero hD
  rw [qN_eq_packetInverseGram]
  congr 1
  rw [finitePacketGram, gramMatrix_inverseSource (finitePacket_independent n)]
  exact hquad

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto

open RiemannResearch.LinearAlgebra.RankTwoWoodbury

/-- The exact finite cotangent sum. The fractional factor is expressed with
the natural remainder, so no analytic fractional-part convention is hidden.
For `b = 0` or `b = 1` the indexing set is empty. -/
def cotangentV (a b : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 b,
    ((a * r % b : ℕ) : ℝ) / (b : ℝ) *
      (Real.cos (Real.pi * (r : ℝ) / (b : ℝ)) /
        Real.sin (Real.pi * (r : ℝ) / (b : ℝ)))

/-- The proposed arithmetic cotangent core entry, with both divisor sums
and both orientations of `V` retained. Its equality with a component of the
actual Pareto Gram matrix is not part of this definition. -/
def ramanujanCotangentCoreEntry (d e : ℕ) : ℝ :=
  -(1 / 2 : ℝ) *
    ∑ a ∈ d.divisors, ∑ b ∈ e.divisors,
      (ArithmeticFunction.moebius (d / a) : ℝ) *
        (ArithmeticFunction.moebius (e / b) : ℝ) *
        (cotangentV a b + cotangentV b a)

theorem ramanujanCotangentCoreEntry_comm (d e : ℕ) :
    ramanujanCotangentCoreEntry d e = ramanujanCotangentCoreEntry e d := by
  unfold ramanujanCotangentCoreEntry
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The specified cotangent matrix for the actual conductors `2,...,n+1`. -/
def finiteCotangentCore (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ramanujanCotangentCoreEntry (i.val + 2) (j.val + 2)

theorem finiteCotangentCore_transpose (n : ℕ) :
    (finiteCotangentCore n)ᵀ = finiteCotangentCore n := by
  ext i j
  exact ramanujanCotangentCoreEntry_comm (j.val + 2) (i.val + 2)

/-- Specialization to the fully specified finite cotangent core. The actual
Gram identification `hXi`, the supplied core inverse and its symmetry, and
the nonzero Schur denominator remain explicit. -/
theorem qN_eq_cotangent_markedFormula
    (n : ℕ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hRF : R * finiteCotangentCore n = 1) (hR : Rᵀ = R)
    (hXi : finitePacketGram n =
      rankTwoMatrix Real.pi (finiteCotangentCore n)
        (finiteVonMangoldtSource n) (finiteTotientSource n))
    (hD :
      ((finiteTotientSource n) ⬝ᵥ (R *ᵥ (finiteTotientSource n))) *
        ((finiteVonMangoldtSource n) ⬝ᵥ (R *ᵥ (finiteVonMangoldtSource n))) -
      ((finiteTotientSource n) ⬝ᵥ (R *ᵥ (finiteVonMangoldtSource n)) +
        2 * Real.pi) ^ 2 ≠ 0) :
    IntegerDPP.qN n = progressionWeight (IntegerDPP.residueModulus n) 1 *
      markedFormula Real.pi R (finiteTotientSource n)
        (finiteVonMangoldtSource n) (finiteMoebiusSource n) := by
  exact qN_eq_rankTwo_markedFormula n (finiteCotangentCore n) R hRF hR hXi hD

end RiemannResearch.RH.Pareto
