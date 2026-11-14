import RiemannResearch.NumberTheory.PrimePowerFormalCoordinates
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
/-!
# Global formal Dirichlet logarithmic coordinates
Source: V_vector_space_RH.pdf, Section 1.
Normalized prime-local series reconstruct a unique multiplicative arithmetic
function by finite prime factorization. Composing this equivalence with the
formal local exp/log equivalence gives the all-degree global coordinate
bijection. The distinguished family eta reconstructs the constant-one
arithmetic function on positive integers.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.PrimePowerFormalCoordinates
open PowerSeries
abbrev LocalFamily := Nat.Primes → {f : PowerSeries ℂ // constantCoeff f = 1}
abbrev MultiplicativeFunction := {f : ArithmeticFunction ℂ // f.IsMultiplicative}

def atNaturalPrime (F : LocalFamily) (p : ℕ) : PowerSeries ℂ :=
  if hp : Nat.Prime p then (F ⟨p,hp⟩).val else 1

theorem atNaturalPrime_constant (F : LocalFamily) (p : ℕ) :
    constantCoeff (atNaturalPrime F p) = 1 := by
  unfold atNaturalPrime
  split_ifs with hp
  · exact (F ⟨p,hp⟩).property
  · simp

def reconstruct (F : LocalFamily) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod (fun p k => coeff k (atNaturalPrime F p))
  map_zero' := by simp

theorem reconstruct_apply (F : LocalFamily) {n : ℕ} (hn : n ≠ 0) :
    reconstruct F n = n.factorization.prod (fun p k => coeff k (atNaturalPrime F p)) := by
  simp [reconstruct, hn]

theorem reconstruct_multiplicative (F : LocalFamily) : (reconstruct F).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · simp [reconstruct]
  · intro m n hm hn hmn
    rw [reconstruct_apply F (mul_ne_zero hm hn), reconstruct_apply F hm,
      reconstruct_apply F hn, Nat.factorization_mul_of_coprime hmn]
    apply Finsupp.prod_add_index_of_disjoint
    simpa only [Nat.support_factorization] using hmn.disjoint_primeFactors

theorem reconstruct_prime_power (F : LocalFamily) (p : Nat.Primes) (k : ℕ) :
    reconstruct F (p.1 ^ k) = coeff k (F p).val := by
  rw [reconstruct_apply F (pow_ne_zero _ p.property.ne_zero),
    p.property.factorization_pow]
  rw [Finsupp.prod_single_index]
  · rw [atNaturalPrime, dif_pos p.property]
    rfl
  · simpa only [coeff_zero_eq_constantCoeff_apply] using atNaturalPrime_constant F p.1

def localize (f : MultiplicativeFunction) : LocalFamily :=
  fun p => ⟨mk (fun k => f.val (p.1 ^ k)), by
    simpa [← coeff_zero_eq_constantCoeff_apply] using f.property.1⟩

theorem reconstruct_localize (f : MultiplicativeFunction) :
    reconstruct (localize f) = f.val := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    _ (reconstruct_multiplicative (localize f)) f.val f.property).mpr
  intro p k hp
  simpa only [localize, coeff_mk] using reconstruct_prime_power (localize f) ⟨p,hp⟩ k

theorem localize_reconstruct (F : LocalFamily) :
    localize ⟨reconstruct F, reconstruct_multiplicative F⟩ = F := by
  funext p
  apply Subtype.ext
  ext k
  simp only [localize, coeff_mk, reconstruct_prime_power]

def localMultiplicativeEquiv : LocalFamily ≃ MultiplicativeFunction where
  toFun F := ⟨reconstruct F, reconstruct_multiplicative F⟩
  invFun := localize
  left_inv := localize_reconstruct
  right_inv f := Subtype.ext (reconstruct_localize f)

/-- Coefficientwise formal Dirichlet exponential and logarithm, at every prime. -/
def dirichletExpLogEquiv :
    (Nat.Primes → {h : PowerSeries ℂ // constantCoeff h = 0}) ≃ MultiplicativeFunction :=
  primeFamilyEquiv.trans localMultiplicativeEquiv

def etaFamily : Nat.Primes → {h : PowerSeries ℂ // constantCoeff h = 0} :=
  fun _ => ⟨eta, eta_constantCoeff⟩

theorem dirichletExp_eta (n : ℕ) (hn : n ≠ 0) :
    (dirichletExpLogEquiv etaFamily).val n = 1 := by
  change reconstruct (fun _ => ⟨expOf eta, constantCoeff_expOf eta_constantCoeff⟩) n = 1
  rw [reconstruct_apply _ hn]
  classical
  apply Finset.prod_eq_one
  intro p hp
  have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp (by simpa only [Nat.support_factorization] using hp)).1
  simp [atNaturalPrime, hpp, expOf_eta]
end RiemannResearch.NumberTheory.PrimePowerFormalCoordinates
