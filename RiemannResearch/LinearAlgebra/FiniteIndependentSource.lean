import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite independence obstruction to simultaneous signed-source cancellation

The coefficient field is embedded in the reals. In the arithmetic application
it is a finite real algebraic field and `ell` consists of old prime logs plus
one fresh prime log. `hIndependent` is the finite scalar-independence input
supplied on paper by Baker. Its formal arithmetic provider remains explicit.
The separate cyclotomic trace argument must provide `v jComposite != 0`.
The arithmetic Baker and trace providers remain open formal dependencies.

Source: paper continuation crt_baker_mean_source_handoff.txt, Sections 6 and 10.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.FiniteIndependentSource

variable {K τ κ : Type*} [Field K] [Fintype τ]

def linearSource (f : K →+* ℝ) (ell : τ → ℝ) (a : τ → K) : ℝ :=
  ∑ i, f (a i) * ell i

def signedSource (f : K →+* ℝ) (ell : τ → ℝ)
    (a : κ → τ → K) (v : κ → K) (m Q : ℝ) (j : κ) : ℝ :=
  m * linearSource f ell (a j) - (Q / 2) * f (v j)

/-- The full algebraic linear combination; both signed summands are retained. -/
theorem linearSource_sub_scaled (f : K →+* ℝ) (ell : τ → ℝ)
    (a b : τ → K) (u v : K) :
    linearSource f ell (fun i => u * a i - v * b i) =
      f u * linearSource f ell a - f v * linearSource f ell b := by
  unfold linearSource
  simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
  congr 1 <;> rw [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- A prime coordinate containing the fresh log and a composite coordinate
omitting it cannot both have zero signed source if the latter charge is nonzero.
No positive sign assumption on `m` or `Q` is made. -/
theorem two_signed_sources_not_both_zero
    (f : K →+* ℝ) (ell : τ → ℝ)
    (hIndependent : ∀ a : τ → K,
      linearSource f ell a = 0 → ∀ i, a i = 0)
    (a : κ → τ → K) (v : κ → K) (m Q : ℝ)
    (jPrime jComposite : κ) (fresh : τ)
    (hm : m ≠ 0)
    (hPrime : a jPrime fresh = 1)
    (hComposite : a jComposite fresh = 0)
    (hv : v jComposite ≠ 0) :
    signedSource f ell a v m Q jPrime ≠ 0 ∨
      signedSource f ell a v m Q jComposite ≠ 0 := by
  by_cases hp : signedSource f ell a v m Q jPrime = 0
  · right
    intro hc
    have hp' : m * linearSource f ell (a jPrime) - (Q / 2) * f (v jPrime) = 0 := hp
    have hc' : m * linearSource f ell (a jComposite) -
        (Q / 2) * f (v jComposite) = 0 := hc
    have hproduct : m * (f (v jPrime) * linearSource f ell (a jComposite) -
        f (v jComposite) * linearSource f ell (a jPrime)) = 0 := by
      nlinarith only [congrArg (fun x : ℝ => f (v jPrime) * x) hc',
        congrArg (fun x : ℝ => f (v jComposite) * x) hp']
    have hrel : f (v jPrime) * linearSource f ell (a jComposite) -
        f (v jComposite) * linearSource f ell (a jPrime) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hm
    have hsum : linearSource f ell
        (fun i => v jPrime * a jComposite i - v jComposite * a jPrime i) = 0 := by
      rw [linearSource_sub_scaled]
      exact hrel
    have hfresh := hIndependent _ hsum fresh
    have hvzero : v jComposite = 0 := by
      simpa only [hPrime, hComposite, mul_zero, mul_one, zero_sub,
        neg_eq_zero] using hfresh
    exact hv hvzero
  · exact Or.inl hp

end RiemannResearch.LinearAlgebra.FiniteIndependentSource
