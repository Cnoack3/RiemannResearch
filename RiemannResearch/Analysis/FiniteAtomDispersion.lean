import RiemannResearch.Analysis.FiniteWeightedVariance
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Exact pooling of repeated atoms and corrected shell concentration

Source: Christian Noack, `sdf_modified.pdf`, 21 July 2026, section 14.9,
Lemma 14.6 and equations (135)--(137). The first Cauchy--Schwarz bound
is valid; the asserted dimension-free implication from the per-atom
bound is not. We retain the complete pooled variance and bias term,
and give an unbounded dyadic counterfamily to that inference.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteAtomDispersion
open FiniteWeightedVariance
variable {ι κ : Type*} [DecidableEq κ]

def fiber (s : Finset ι) (label : ι → κ) (d : κ) : Finset ι :=
  s.filter (fun i => label i = d)

def atomMean (s : Finset ι) (label : ι → κ) (a : ι → ℝ) (d : κ) : ℝ :=
  mean (fiber s label d) (fun _ => 1) a

def loss (s : Finset ι) (label : ι → κ) (a : ι → ℝ) (u : κ → ℝ) : ℝ :=
  ∑ i ∈ s, (a i - u (label i)) ^ 2

def pooledDispersion (s : Finset ι) (label : ι → κ) (a : ι → ℝ) : ℝ :=
  ∑ d ∈ s.image label, variance (fiber s label d) (fun _ => 1) a

theorem fiber_mass_pos (s : Finset ι) (label : ι → κ) (d : κ)
    (hd : d ∈ s.image label) : 0 < mass (fiber s label d) (fun _ => 1) := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
  have hn : (fiber s label (label i)).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
  simpa [mass] using (show (0 : ℝ) < (fiber s label (label i)).card by
    exact_mod_cast Finset.card_pos.mpr hn)

theorem loss_eq_fiber_sum (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u : κ → ℝ) :
    loss s label a u = ∑ d ∈ s.image label,
      ∑ i ∈ fiber s label d, (a i - u d) ^ 2 := by
  have hm (i : ι) (hi : i ∈ s) : label i ∈ s.image label := Finset.mem_image_of_mem _ hi
  rw [loss, ← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- The exact optimum and all coefficient-bias squares; no independence is used. -/
theorem loss_eq_pooled_add_bias (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u : κ → ℝ) :
    loss s label a u = pooledDispersion s label a +
      ∑ d ∈ s.image label, (fiber s label d).card *
        (atomMean s label a d - u d) ^ 2 := by
  rw [loss_eq_fiber_sum, pooledDispersion, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  simpa [atomMean, mass, sub_eq_add_neg] using
    translation_energy (fiber s label d) (fun _ => 1) a (-u d)
      (fiber_mass_pos s label d hd).ne'

theorem atomMean_minimizes (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u : κ → ℝ) :
    loss s label a (atomMean s label a) = pooledDispersion s label a ∧
      pooledDispersion s label a ≤ loss s label a u := by
  constructor
  · rw [loss_eq_pooled_add_bias]
    simp
  · rw [loss_eq_pooled_add_bias]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun d hd => by positivity))

/-- The optimum is an explicit sum of pairwise within-atom differences. -/
theorem pooledDispersion_eq_pairwise (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) :
    pooledDispersion s label a =
      ∑ d ∈ s.image label,
        (∑ i ∈ fiber s label d, ∑ j ∈ fiber s label d, (a i - a j) ^ 2) /
          (2 * (fiber s label d).card) := by
  apply Finset.sum_congr rfl
  intro d hd
  have hm := fiber_mass_pos s label d hd
  have hid := pairwise_identity (fiber s label d) (fun _ => 1) a hm.ne'
  have hp : (0 : ℝ) < (fiber s label d).card := by simpa [mass] using hm
  apply (eq_div_iff (by positivity : (2 : ℝ) * (fiber s label d).card ≠ 0)).mpr
  simpa [mass, mul_comm, mul_left_comm, mul_assoc] using hid.symm

omit [DecidableEq κ] in
/-- Correct aggregate L2-to-L1 bound, retaining the actual number of returns. -/
theorem l1_sq_le_card_mul_loss (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u : κ → ℝ) :
    (∑ i ∈ s, |a i - u (label i)|) ^ 2 ≤ s.card * loss s label a u := by
  simpa [loss, sq_abs] using
    Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => |a i - u (label i)|)

omit [DecidableEq κ] in
/-- A total squared error E^2, rather than E^2 times the shell length
for every atom, gives the claimed square-root shell scale. -/
theorem l1_sq_le_of_total_loss (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u : κ → ℝ) (C H E : ℝ)
    (hcard : (s.card : ℝ) ≤ C * H) (hloss : loss s label a u ≤ E ^ 2) :
    (∑ i ∈ s, |a i - u (label i)|) ^ 2 ≤ C * H * E ^ 2 := by
  calc
    _ ≤ (s.card : ℝ) * loss s label a u := l1_sq_le_card_mul_loss s label a u
    _ ≤ (s.card : ℝ) * E ^ 2 := mul_le_mul_of_nonneg_left hloss (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg E)

/-- A single atom with unit errors satisfies V=H and N=H, but S=H. -/
theorem one_atom_unit_errors (H : ℕ) :
    loss (Finset.range H) (fun _ => (0 : ℕ)) (fun _ => 1) (fun _ => 0) = H ∧
      (∑ _i ∈ Finset.range H, |(1 : ℝ)|) = H := by
  simp [loss]

/-- Hence no uniform constant repairs the manuscript's claimed implication
from V <= E^2 H and N <= H to S^2 <= K H E^2. -/
theorem no_uniform_dyadic_inference (K : ℝ) :
    ∃ j : ℕ, K * (2 : ℝ) ^ j <
      (∑ _i ∈ Finset.range (2 ^ j), |(1 : ℝ)|) ^ 2 := by
  obtain ⟨j,hj⟩ := exists_nat_gt K
  have hjpow : (j : ℝ) < (2 : ℝ) ^ j := by
    exact_mod_cast (Nat.lt_two_pow_self : j < 2 ^ j)
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  refine ⟨j, ?_⟩
  simp only [abs_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

end RiemannResearch.Analysis.FiniteAtomDispersion
