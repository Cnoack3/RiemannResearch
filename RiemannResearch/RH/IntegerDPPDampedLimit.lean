import RiemannResearch.Probability.MultiplicativeOccupancyLower
import RiemannResearch.RH.IntegerDPPDampedMinimum
import RiemannResearch.RH.ParetoProductBenchmark

/-!
# Infinite-window damped determinant criterion

Source: user-provided damped Fredholm criterion, 2026-09-20. This proves the
convergence criterion for the actual finite compressions of the limiting
arithmetic kernel. The separate identification with an operator-theoretic
Fredholm determinant is not assumed. The benchmark is evaluated explicitly.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.Occupancy

def prefixEmbedding (m : ℕ) : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

def dampedPrefixDeterminant (m : ℕ) : ℝ :=
  dampedWindowDeterminant m (prefixEmbedding m) (fun i => paretoWeight i.val)

theorem paretoWeight_lt_one (i : ℕ) : paretoWeight i < 1 := by
  unfold paretoWeight
  have hn := Nat.cast_nonneg (α := ℝ) i
  apply (div_lt_one (by positivity)).mpr
  nlinarith

theorem dampedPrefix_lower (m : ℕ) :
    (∏ i ∈ Finset.range (m + 1), (1 - paretoWeight i)) * (1 + limitingVacancy) ≤
      dampedPrefixDeterminant (m + 1) := by
  have h := integral_product_first_site_lower limitingLaw m
    (fun i : Fin (m + 1) => paretoWeight i.val)
    (fun i => ⟨paretoWeight_pos i.val, paretoWeight_lt_one i.val⟩)
    (by norm_num [paretoWeight]) (fun x i => x i.val)
    (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))
  change (benchmark (fun i : Fin (m + 1) => paretoWeight i.val)) *
    (1 + limitingLaw.real {x | x 0 = false}) ≤
      (∫ x, product (fun i : Fin (m + 1) => paretoWeight i.val)
        (fun i => x (prefixEmbedding (m + 1) i)) ∂limitingLaw) at h
  rw [← dampedWindowDeterminant_eq_integral (m+1) (prefixEmbedding (m+1)),
    limitingLaw_first_site_vacancy] at h
  rw [benchmark, Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 - paretoWeight i) (m + 1)] at h
  exact h

theorem dampedPrefix_tendsto_benchmark_iff :
    Tendsto dampedPrefixDeterminant atTop (𝓝 paretoProductBenchmark) ↔
      limitingVacancy = 0 := by
  constructor
  · intro h
    have hb := (pareto_product_tendsto_benchmark.mul_const (1 + limitingVacancy)).comp
      (tendsto_add_atTop_nat 1)
    have hd := h.comp (tendsto_add_atTop_nat 1)
    have hh : paretoProductBenchmark * (1 + limitingVacancy) ≤ paretoProductBenchmark :=
      le_of_tendsto_of_tendsto hb hd (Filter.Eventually.of_forall dampedPrefix_lower)
    nlinarith [paretoProductBenchmark_pos, limitingVacancy_nonneg]
  · intro h
    have ht := limitingVacancy_zero_iff_top.mp h
    have hocc : ∀ᵐ x ∂limitingLaw, {i | x i = true} = Set.univ := by
      apply limitingLaw_isDPP.full_occupation_ae_iff.mpr
      intro i
      apply (limitingKernel_diagonal_one_iff i).mpr
      rw [ht]
      trivial
    have he (m : ℕ) : dampedPrefixDeterminant m =
        ∏ i ∈ Finset.range m, (1 - paretoWeight i) := by
      change dampedWindowDeterminant m (prefixEmbedding m) _ = _
      rw [dampedWindowDeterminant_eq_integral]
      have hae : (fun x => product (fun i : Fin m => paretoWeight i.val)
          (fun i => x (prefixEmbedding m i))) =ᵐ[limitingLaw]
          (fun _ => benchmark (fun i : Fin m => paretoWeight i.val)) := by
        filter_upwards [hocc] with x hx
        have hall (i : Fin m) : x (prefixEmbedding m i) = true := by
          have hm : prefixEmbedding m i ∈ ({j | x j = true} : Set ℕ) := by rw [hx]; trivial
          exact hm
        simp only [product, hall, if_true, benchmark]
      rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]
      exact Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 - paretoWeight i) m
    have hef : dampedPrefixDeterminant =
        (fun m => ∏ i ∈ Finset.range m, (1 - paretoWeight i)) := funext he
    rw [hef]
    exact pareto_product_tendsto_benchmark

theorem riemannHypothesis_of_dampedPrefix_benchmark
    (h : Tendsto dampedPrefixDeterminant atTop (𝓝 paretoProductBenchmark)) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_vacancy_tendsto_zero
    (vacancy_tendsto_zero_iff_limitingVacancy_zero.mpr
      (dampedPrefix_tendsto_benchmark_iff.mp h))

end RiemannResearch.RH.Pareto.IntegerDPP
