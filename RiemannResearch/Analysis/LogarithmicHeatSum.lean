import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring

/-!
# The logarithmic eigenvalue heat sum

The weights corresponding to eigenvalues log (n+1) sum to zeta on Re(s)>1.
This proves an eigenvalue sum only, not an unbounded self-adjoint operator,
trace class, or the identification with an operator trace.

Source: user-provided Hilbert--Polya discussion, 13 October 2026. The zeta
identification uses Mathlib's LSeries_one_eq_riemannZeta.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.LogarithmicHeatSum

def heatWeight (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-s * (Real.log ((n + 1 : ℕ) : ℝ) : ℂ))

theorem heatWeight_eq_term (s : ℂ) (n : ℕ) :
    heatWeight s n = LSeries.term (1 : ℕ → ℂ) s (n + 1) := by
  have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
  rw [heatWeight, LSeries.term_of_ne_zero hn]
  simp only [Pi.one_apply, one_div]
  rw [← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
    ← Complex.natCast_log]
  congr 1
  ring

theorem summable_heatWeight {s : ℂ} (hs : 1 < s.re) :
    Summable (heatWeight s) := by
  have hsum : Summable (LSeries.term (1 : ℕ → ℂ) s) :=
    LSeriesSummable_one_iff.mpr hs
  have hshift :
      Summable (fun n : ℕ => LSeries.term (1 : ℕ → ℂ) s (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  apply hshift.congr
  intro n
  exact (heatWeight_eq_term s n).symm

/-- Exact spectral-weight sum; no operator trace is claimed. -/
theorem tsum_heatWeight_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, heatWeight s n) = riemannZeta s := by
  have hsum : Summable (LSeries.term (1 : ℕ → ℂ) s) :=
    LSeriesSummable_one_iff.mpr hs
  have hsplit := hsum.sum_add_tsum_nat_add 1
  change
    (∑ n ∈ Finset.range 1, LSeries.term (1 : ℕ → ℂ) s n) +
      (∑' n : ℕ, LSeries.term (1 : ℕ → ℂ) s (n + 1)) =
      LSeries (1 : ℕ → ℂ) s at hsplit
  have hhead :
      (∑ n ∈ Finset.range 1, LSeries.term (1 : ℕ → ℂ) s n) = 0 := by
    simp [LSeries.term]
  rw [hhead, zero_add] at hsplit
  calc
    (∑' n : ℕ, heatWeight s n) =
        ∑' n : ℕ, LSeries.term (1 : ℕ → ℂ) s (n + 1) :=
      tsum_congr (heatWeight_eq_term s)
    _ = LSeries (1 : ℕ → ℂ) s := hsplit
    _ = riemannZeta s := LSeries_one_eq_riemannZeta hs

end RiemannResearch.Analysis.LogarithmicHeatSum
