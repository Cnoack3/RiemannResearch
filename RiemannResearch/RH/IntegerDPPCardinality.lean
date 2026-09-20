import RiemannResearch.Probability.DeterminantalCardinality
import RiemannResearch.RH.IntegerDPPTrace
import RiemannResearch.RH.IntegerDPPExistence

/-!
# Arithmetic projection DPPs have exactly the prescribed rank

Source: the user-provided projection DPP construction. The general
rank-and-trace cardinality theorem is specialized using the actual arithmetic
projection's checked rank bound and trace. No RH or coupling assumption is used.
-/

noncomputable section
open MeasureTheory
open scoped Classical ENNReal
namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.DPP

theorem integerLaw_cardinality (n : ℕ) :
    ∀ᵐ x ∂integerLaw n, setCount {i | x i = true} = n :=
  (integerLaw_isDPP n).setCount_eq_ae_of_rank_trace n
    (fun e => integerKernel_principal_det_zero_of_rank n e)
    (integerKernel_diagonal_summable n) (integerKernel_diagonal_tsum n)

end RiemannResearch.RH.Pareto.IntegerDPP
