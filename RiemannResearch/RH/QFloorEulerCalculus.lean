import RiemannResearch.RH.QFloorEulerOperators

/-!
# Exponential and convergent logarithm calculus on the actual Q legal closure

Every nontrivial floor dilation has absolutely summable operator powers. This
proves convergence of its logarithm series, including the prime two despite the
coarse first-power norm bound. Exponentials of finite combinations of the floor
dilations preserve membership in the legal closure in both directions.
-/

noncomputable section

open scoped BigOperators Topology

namespace RiemannResearch.RH.QFloorEulerCalculus

open ZetaTwoHilbert QFloorDilation QFloorEulerOperators QFullResidueProjection
open RiemannResearch.Analysis.ClosedInvariantCalculus

/-- Absolute summability is stronger than the Neumann summability needed for
the Euler inverse, and also controls the logarithm series. -/
theorem floorDilation_norm_powers_summable (m : ℕ) (hm : 1 < m) :
    Summable (fun k : ℕ => ‖floorDilation m (by omega) ^ k‖) := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hlt : Real.sqrt (1 / (m : ℝ)) < 1 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / (m : ℝ) by positivity)
    have hd : (1 : ℝ) / m < 1 := (div_lt_one (by positivity)).mpr hmR
    nlinarith [Real.sqrt_nonneg (1 / (m : ℝ))]
  have hg : Summable (fun k : ℕ => (Real.sqrt (1 / (m : ℝ))) ^ k) :=
    summable_geometric_of_lt_one (Real.sqrt_nonneg _) hlt
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (floorDilation_pow_norm_le m (by omega)) (hg.mul_left (Real.sqrt 2))

theorem floorDilation_log_series_summable (m : ℕ) (hm : 1 < m) :
    Summable (fun k : ℕ =>
      (1 / ((k + 1 : ℕ) : ℝ)) • floorDilation m (by omega) ^ (k + 1)) :=
  summable_logOneSub_series_of_summable_norm_powers
    (floorDilation_norm_powers_summable m hm)

/-- The convergent operator series for the logarithm of the local Euler factor. -/
def floorLog (m : ℕ) (hm : 1 < m) : QHilbert →L[ℝ] QHilbert :=
  logOneSub (floorDilation m (by omega))

theorem floorLog_hasSum (m : ℕ) (hm : 1 < m) :
    HasSum (fun k : ℕ =>
      -((1 / ((k + 1 : ℕ) : ℝ)) • floorDilation m (by omega) ^ (k + 1)))
      (floorLog m hm) :=
  (floorDilation_log_series_summable m hm).hasSum.neg

theorem floorLog_mem_legalClosure (m : ℕ) (hm : 1 < m)
    (f : QHilbert) (hf : f ∈ closure) : floorLog m hm f ∈ closure :=
  log_one_sub_apply_mem closure (by exact isClosed_closure)
    (floorDilation_mem_legalClosure m (by omega)) hf

theorem exp_floorDilation_mem_iff (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    NormedSpace.exp (floorDilation m hm) f ∈ closure ↔ f ∈ closure :=
  exp_apply_mem_iff closure (by exact isClosed_closure)
    (floorDilation_mem_legalClosure m hm) f

/-- Any finite real combination of prime/integer floor generators may be
exponentiated without changing whether a vector belongs to the legal closure. -/
theorem exp_floor_sum_mem_iff {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (f : QHilbert) :
    NormedSpace.exp (∑ i ∈ s, a i • floorDilation (m i) (hm i)) f ∈ closure ↔
      f ∈ closure := by
  apply exp_apply_mem_iff closure (by exact isClosed_closure)
  change (∑ i ∈ s, a i • floorDilation (m i) (hm i)) ∈ invariantAlgebra closure
  exact (invariantAlgebra closure).sum_mem fun i hi =>
    (invariantAlgebra closure).smul_mem (floorDilation_invariant (m i) (hm i)) (a i)

/-- Exponentiating a convergent local logarithm series preserves membership too;
this theorem does not identify its exponential with the Euler factor. -/
theorem exp_floorLog_mem_iff (m : ℕ) (hm : 1 < m) (f : QHilbert) :
    NormedSpace.exp (floorLog m hm) f ∈ closure ↔ f ∈ closure :=
  exp_apply_mem_iff closure (by exact isClosed_closure)
    (floorLog_mem_legalClosure m hm) f

end RiemannResearch.RH.QFloorEulerCalculus
