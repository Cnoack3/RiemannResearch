import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Prime-power support and completely multiplicative twists

Source: user-provided V_Zeta_Zeros_Fourier_Chebyshev_Handoff_2026-09-16,
Sections 2--4 and 12. This module proves support/projection and finite
convolution-polynomial equivariance, without assuming analytic convergence
or a coefficientwise infinite exp/log theorem.
-/
noncomputable section
open scoped BigOperators
namespace ArithmeticFunction

variable {K : Type*} [CommRing K]

def primePowerSupported (f : ArithmeticFunction K) : Prop :=
  ∀ n, ¬ IsPrimePow n → f n = 0

def primePowerProject (f : ArithmeticFunction K) : ArithmeticFunction K :=
  ⟨fun n => if IsPrimePow n then f n else 0, by simp⟩

@[simp] theorem primePowerProject_apply (f : ArithmeticFunction K) (n : ℕ) :
    primePowerProject f n = if IsPrimePow n then f n else 0 := rfl

theorem primePowerProject_supported (f : ArithmeticFunction K) :
    primePowerSupported (primePowerProject f) := by
  intro n hn
  simp [hn]

theorem primePowerProject_eq_self_iff (f : ArithmeticFunction K) :
    primePowerProject f = f ↔ primePowerSupported f := by
  constructor
  · intro h
    rw [← h]
    exact primePowerProject_supported f
  · intro h
    ext n
    by_cases hn : IsPrimePow n
    · simp [hn]
    · simp [hn, h n hn]

@[simp] theorem primePowerProject_idempotent (f : ArithmeticFunction K) :
    primePowerProject (primePowerProject f) = primePowerProject f :=
  (primePowerProject_eq_self_iff _).mpr (primePowerProject_supported f)

def primePowerProjection : ArithmeticFunction K →ₗ[K] ArithmeticFunction K where
  toFun := primePowerProject
  map_add' f g := by
    ext n
    by_cases hn : IsPrimePow n <;> simp [hn]
  map_smul' c f := by
    ext n
    by_cases hn : IsPrimePow n <;> simp [hn]

theorem vonMangoldt_primePowerSupported : primePowerSupported vonMangoldt := by
  intro n hn
  exact vonMangoldt_eq_zero_iff.mpr hn

/-- Normalized completely multiplicative weights, including weights vanishing at primes. -/
def completeTwist (c : ℕ →* K) (f : ArithmeticFunction K) : ArithmeticFunction K :=
  ⟨fun n => c n * f n, by simp⟩

@[simp] theorem completeTwist_apply (c : ℕ →* K) (f : ArithmeticFunction K) (n : ℕ) :
    completeTwist c f n = c n * f n := rfl

@[simp] theorem completeTwist_one (c : ℕ →* K) : completeTwist c 1 = 1 := by
  ext n
  by_cases hn : n = 1 <;> simp [hn]

@[simp] theorem completeTwist_add (c : ℕ →* K) (f g : ArithmeticFunction K) :
    completeTwist c (f + g) = completeTwist c f + completeTwist c g := by
  ext n
  simp [mul_add]

@[simp] theorem completeTwist_mul (c : ℕ →* K) (f g : ArithmeticFunction K) :
    completeTwist c (f * g) = completeTwist c f * completeTwist c g := by
  ext n
  simp only [completeTwist_apply, mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
  rw [← he, map_mul]
  ring

/-- Twisting is an algebra endomorphism for Dirichlet convolution. -/
def completeTwistHom (c : ℕ →* K) : ArithmeticFunction K →+* ArithmeticFunction K where
  toFun := completeTwist c
  map_zero' := by ext n; simp
  map_one' := completeTwist_one c
  map_add' := completeTwist_add c
  map_mul' := completeTwist_mul c

@[simp] theorem completeTwist_pow (c : ℕ →* K) (f : ArithmeticFunction K) (r : ℕ) :
    completeTwist c (f ^ r) = completeTwist c f ^ r :=
  (completeTwistHom c).map_pow f r

@[simp] theorem completeTwist_smul (c : ℕ →* K) (a : K) (f : ArithmeticFunction K) :
    completeTwist c (a • f) = a • completeTwist c f := by
  ext n
  simp [mul_left_comm]

/-- In particular, every finite exp/log truncation commutes with twisting. -/
theorem completeTwist_polynomial (c : ℕ →* K) (a : ℕ → K)
    (f : ArithmeticFunction K) (N : ℕ) :
    completeTwist c (∑ r ∈ Finset.range N, a r • f ^ r) =
      ∑ r ∈ Finset.range N, a r • (completeTwist c f) ^ r := by
  change (completeTwistHom c) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact (completeTwist_smul c (a r) (f ^ r)).trans
    (congrArg (fun g => a r • g) (completeTwist_pow c f r))

theorem completeTwist_project (c : ℕ →* K) (f : ArithmeticFunction K) :
    completeTwist c (primePowerProject f) = primePowerProject (completeTwist c f) := by
  ext n
  by_cases hn : IsPrimePow n <;> simp [hn]

section Domain
variable [IsDomain K]
theorem completeTwist_eq_zero_iff (c : ℕ →* K) (f : ArithmeticFunction K) :
    completeTwist c f = 0 ↔ ∀ n, c n ≠ 0 → f n = 0 := by
  constructor
  · intro h n hn
    have he := congrArg (fun g : ArithmeticFunction K => g n) h
    simpa only [completeTwist_apply, zero_apply, mul_eq_zero, hn, false_or] using he
  · intro h
    ext n
    by_cases hn : c n = 0
    · simp [hn]
    · simp [h n hn]

theorem completeTwist_injective (c : ℕ →* K) (hc : ∀ n, n ≠ 0 → c n ≠ 0) :
    Function.Injective (completeTwist c) := by
  intro f g h
  ext n
  by_cases hn : n = 0
  · simp [hn]
  · have he := congrArg (fun a : ArithmeticFunction K => a n) h
    exact mul_left_cancel₀ (hc n hn) he
end Domain
end ArithmeticFunction
