import RiemannResearch.RH.IntegerDPPWindow
import RiemannResearch.RH.IntegerDPPWindowGenerating
import Mathlib.Topology.Instances.Matrix

/-!
# Finite-window convergence to the infinite arithmetic DPP

Source: the user's request to take the DPP to infinity, and the previously
constructed arithmetic laws and projection-kernel convergence. Continuity of
finite determinants proves convergence of inclusion probabilities, hole
probabilities, and multivariate window generating functions.

No spatial coupling or RH hypothesis is needed. The standard interpretation in
terms of finite-dimensional laws follows discrete DPP terminology in Lyons,
arXiv:math/0204325; no external probability theorem is used below.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.IntegerDPP

theorem integerLaw_inclusion_tendsto (m : ℕ) (e : Fin m ↪ ℕ) :
    Tendsto (fun n => (integerLaw n).real {x | ∀ i, x (e i) = true}) atTop
      (𝓝 (limitingLaw.real {x | ∀ i, x (e i) = true})) := by
  have hfin (n : ℕ) :
      (integerLaw n).real {x | ∀ i, x (e i) = true} =
        Matrix.det (Matrix.of (fun i j => integerKernel n (e i) (e j))) :=
    (integerLaw_isDPP n).correlation m e
  have hinf :
      limitingLaw.real {x | ∀ i, x (e i) = true} =
        Matrix.det (Matrix.of (fun i j => limitingKernel (e i) (e j))) :=
    limitingLaw_isDPP.correlation m e
  simp_rw [hfin, hinf]
  exact (continuous_id.matrix_det.tendsto _).comp
    (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
      integerKernel_tendsto (e i) (e j))

theorem integerLaw_finite_gap_tendsto (m : ℕ) (e : Fin m ↪ ℕ) :
    Tendsto (fun n => (integerLaw n).real {x | ∀ i, x (e i) = false}) atTop
      (𝓝 (limitingLaw.real {x | ∀ i, x (e i) = false})) := by
  simp_rw [integerLaw_finite_gap, limitingLaw_finite_gap]
  apply (continuous_id.matrix_det.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.sub (integerKernel_tendsto (e i) (e j))

theorem integerLaw_window_generating_tendsto
    (m : ℕ) (e : Fin m ↪ ℕ) (z : Fin m → ℝ) :
    Tendsto (fun n =>
      ∫ x, ∏ i : Fin m, if x (e i) = true then z i else 1 ∂integerLaw n) atTop
      (𝓝 (∫ x, ∏ i : Fin m, if x (e i) = true then z i else 1 ∂limitingLaw)) := by
  simp_rw [integerLaw_window_generating, limitingLaw_window_generating]
  apply (continuous_id.matrix_det.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.of_apply]
  exact ((integerKernel_tendsto (e i) (e j)).const_mul (z i)).add
    (tendsto_const_nhds.sub (integerKernel_tendsto (e i) (e j)))

end RiemannResearch.RH.Pareto.IntegerDPP
