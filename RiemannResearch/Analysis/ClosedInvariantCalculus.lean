import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Functional calculus preserving a closed linear subspace

The bounded operators preserving a closed real subspace form a closed subalgebra.
Consequently operator exponentials, logarithm series, and convergent Neumann
series preserve the subspace. The Neumann identities require summability of the
powers, which is weaker than a strict bound on the norm of the first power.

The logarithm is defined by the explicit series for `log (I-T)`. Its convergence
is proved under absolute summability of the operator powers, in particular when
the operator norm is less than one. No exponential/logarithm inverse identity is claimed.
-/

noncomputable section

namespace RiemannResearch.Analysis.ClosedInvariantCalculus

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)

/-- The unital real algebra of bounded operators preserving `V`. -/
def invariantAlgebra (V : Submodule ℝ E) : Subalgebra ℝ (E →L[ℝ] E) where
  carrier := {T | ∀ x ∈ V, T x ∈ V}
  zero_mem' := by
    intro x hx
    exact V.zero_mem
  one_mem' := by
    intro x hx
    exact hx
  add_mem' := by
    intro T S hT hS x hx
    exact V.add_mem (hT x hx) (hS x hx)
  mul_mem' := by
    intro T S hT hS x hx
    exact hT (S x) (hS x hx)
  algebraMap_mem' := by
    intro r x hx
    change r • x ∈ V
    exact V.smul_mem r hx

@[simp] theorem mem_invariantAlgebra (V : Submodule ℝ E) (T : E →L[ℝ] E) :
    T ∈ invariantAlgebra V ↔ ∀ x ∈ V, T x ∈ V := Iff.rfl

/-- Closedness is in the operator norm topology. -/
theorem isClosed_invariantAlgebra (V : Submodule ℝ E) (hV : IsClosed (V : Set E)) :
    IsClosed (invariantAlgebra V : Set (E →L[ℝ] E)) := by
  change IsClosed {T : E →L[ℝ] E | ∀ x ∈ V, T x ∈ V}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun hx =>
    hV.preimage (ContinuousEvalConst.continuous_eval_const x)

theorem exp_mem_invariantAlgebra (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    {T : E →L[ℝ] E} (hT : T ∈ invariantAlgebra V) :
    NormedSpace.exp T ∈ invariantAlgebra V :=
  NormedSpace.exp_mem (R := ℝ) (isClosed_invariantAlgebra V hV) hT

/-- Infinite operator sums preserve the closed subspace. -/
theorem tsum_mem_invariantAlgebra {ι : Type*} (V : Submodule ℝ E)
    (hV : IsClosed (V : Set E)) {T : ι → (E →L[ℝ] E)}
    (hT : ∀ i, T i ∈ invariantAlgebra V) :
    (∑' i, T i) ∈ invariantAlgebra V :=
  tsum_mem (isClosed_invariantAlgebra V hV) hT

/-- The series logarithm of `I-T`, with the usual zero value if not summable. -/
def logOneSub (T : E →L[ℝ] E) : E →L[ℝ] E :=
  -(∑' k : ℕ, (1 / ((k + 1 : ℕ) : ℝ)) • T ^ (k + 1))

theorem log_one_sub_mem_invariantAlgebra (V : Submodule ℝ E)
    (hV : IsClosed (V : Set E)) {T : E →L[ℝ] E} (hT : T ∈ invariantAlgebra V) :
    logOneSub T ∈ invariantAlgebra V := by
  change -(∑' k : ℕ, (1 / ((k + 1 : ℕ) : ℝ)) • T ^ (k + 1)) ∈ invariantAlgebra V
  refine (invariantAlgebra V).neg_mem (tsum_mem_invariantAlgebra V hV ?_)
  intro k
  exact (invariantAlgebra V).toSubmodule.smul_mem
    (1 / ((k + 1 : ℕ) : ℝ)) ((invariantAlgebra V).pow_mem hT (k + 1))

theorem summable_logOneSub_series_of_summable_norm_powers [CompleteSpace E]
    {T : E →L[ℝ] E} (hpow : Summable fun n : ℕ => ‖T ^ n‖) :
    Summable fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ)) • T ^ (k + 1) := by
  have htail : Summable fun k : ℕ => ‖T ^ (k + 1)‖ :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖T ^ n‖) 1).2 hpow
  apply htail.of_norm_bounded
  intro k
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hc : ‖(1 / ((k + 1 : ℕ) : ℝ))‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 hk
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)

theorem summable_logOneSub_series_of_norm_lt_one [CompleteSpace E] [Nontrivial E]
    {T : E →L[ℝ] E} (hT : ‖T‖ < 1) :
    Summable fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ)) • T ^ (k + 1) := by
  apply summable_logOneSub_series_of_summable_norm_powers
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_pow_le T n) (summable_geometric_of_lt_one (norm_nonneg T) hT)

/-- The Neumann operator; inverse identities are stated below with summability. -/
def neumann (T : E →L[ℝ] E) : E →L[ℝ] E := ∑' n : ℕ, T ^ n

theorem neumann_mem_invariantAlgebra (V : Submodule ℝ E)
    (hV : IsClosed (V : Set E)) {T : E →L[ℝ] E} (hT : T ∈ invariantAlgebra V) :
    neumann T ∈ invariantAlgebra V :=
  tsum_mem_invariantAlgebra V hV fun n => (invariantAlgebra V).pow_mem hT n

theorem neumann_mul_one_sub {T : E →L[ℝ] E}
    (hpow : Summable fun n : ℕ => T ^ n) : neumann T * (1 - T) = 1 :=
  hpow.tsum_pow_mul_one_sub

theorem one_sub_mul_neumann {T : E →L[ℝ] E}
    (hpow : Summable fun n : ℕ => T ^ n) : (1 - T) * neumann T = 1 :=
  hpow.one_sub_mul_tsum_pow

/-- A summable Neumann series makes `I-T` a unit with a subspace-preserving inverse. -/
def oneSubUnit (T : E →L[ℝ] E) (hpow : Summable fun n : ℕ => T ^ n) :
    (E →L[ℝ] E)ˣ where
  val := 1 - T
  inv := neumann T
  val_inv := one_sub_mul_neumann hpow
  inv_val := neumann_mul_one_sub hpow

theorem neumann_apply_mem (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    {T : E →L[ℝ] E} (hT : ∀ x ∈ V, T x ∈ V) {x : E} (hx : x ∈ V) :
    neumann T x ∈ V :=
  neumann_mem_invariantAlgebra V hV hT x hx

theorem exp_apply_mem (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    {T : E →L[ℝ] E} (hT : ∀ x ∈ V, T x ∈ V) {x : E} (hx : x ∈ V) :
    NormedSpace.exp T x ∈ V :=
  exp_mem_invariantAlgebra V hV hT x hx

theorem log_one_sub_apply_mem (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    {T : E →L[ℝ] E} (hT : ∀ x ∈ V, T x ∈ V) {x : E} (hx : x ∈ V) :
    logOneSub T x ∈ V :=
  log_one_sub_mem_invariantAlgebra V hV hT x hx

/-- A Neumann-invertible Euler factor preserves membership in both directions. -/
theorem one_sub_apply_mem_iff (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    {T : E →L[ℝ] E} (hT : ∀ x ∈ V, T x ∈ V)
    (hpow : Summable fun n : ℕ => T ^ n) (x : E) :
    (1 - T) x ∈ V ↔ x ∈ V := by
  constructor
  · intro hx
    have hback := neumann_apply_mem V hV hT hx
    change (neumann T * (1 - T)) x ∈ V at hback
    simpa only [neumann_mul_one_sub hpow, ContinuousLinearMap.one_apply] using hback
  · exact ((invariantAlgebra V).sub_mem (invariantAlgebra V).one_mem hT) x

/-- Exponentiating an invariant bounded operator gives an automorphism of the
closed subspace, not a way to insert new vectors into that subspace. -/
theorem exp_apply_mem_iff [CompleteSpace E] (V : Submodule ℝ E)
    (hV : IsClosed (V : Set E)) {T : E →L[ℝ] E}
    (hT : ∀ x ∈ V, T x ∈ V) (x : E) :
    NormedSpace.exp T x ∈ V ↔ x ∈ V := by
  constructor
  · intro hx
    have hneg : -T ∈ invariantAlgebra V := (invariantAlgebra V).neg_mem hT
    have hback := exp_apply_mem V hV hneg hx
    have hinv : NormedSpace.exp (-T) * NormedSpace.exp T = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl T).neg_left,
        neg_add_cancel, NormedSpace.exp_zero]
    change (NormedSpace.exp (-T) * NormedSpace.exp T) x ∈ V at hback
    simpa only [hinv, ContinuousLinearMap.one_apply] using hback
  · exact exp_apply_mem V hV hT

end RiemannResearch.Analysis.ClosedInvariantCalculus
