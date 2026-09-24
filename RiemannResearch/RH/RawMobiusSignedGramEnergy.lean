import RiemannResearch.RH.RawMobiusBudgetQuantitative
import RiemannResearch.RH.NaturalMobiusSourceLimits
import RiemannResearch.RH.ParetoPrimeSourceDivergence

/-!
# The signed Gram part of the raw Mobius energy

The actual full norm splits into the logarithmic Mobius mean, a diagonal
bounded by twice the harmonic sum, and every signed distinct-pair Gram term.
Existing unconditional source limits control all fixed heads. The growing
off-diagonal upper bound remains a substantive arithmetic hypothesis.

Source: the user's September 24, 2026 request to pursue RH using established
results and independently developed arguments. The exact expansion is finite
Hilbert-space algebra. The analytic inputs are the local checked
NaturalMobiusSourceLimits and RawMobiusBudgetQuantitative modules.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Actual signed residue atom, with zero only at the unused index zero. -/
def rawMobiusSignedAtom (d : ℕ) : ThresholdHilbert :=
  if hd : 0 < d then
    (ArithmeticFunction.moebius d : ℝ) • normalizedResidueHilbert d hd
  else 0

def rawMobiusDiagonalEnergy (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ‖rawMobiusSignedAtom d‖ ^ 2

/-- Both orientations of every distinct pair are retained, with their signs. -/
def rawMobiusOffDiagonalEnergy (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    ∑ e ∈ (Finset.Icc 1 N).erase d,
      inner ℝ (rawMobiusSignedAtom d) (rawMobiusSignedAtom e)

theorem rawMobiusHilbert_eq_signed_sum (N : ℕ) :
    rawMobiusHilbert N = -(∑ d ∈ Finset.Icc 1 N, rawMobiusSignedAtom d) := by
  unfold rawMobiusHilbert
  congr 1
  calc
    _ = ∑ d ∈ (Finset.Icc 1 N).attach, rawMobiusSignedAtom d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < (d : ℕ) := (Finset.mem_Icc.mp d.property).1
      simp only [rawMobiusSignedAtom, dif_pos hdpos]
    _ = _ := Finset.sum_attach (Finset.Icc 1 N) rawMobiusSignedAtom

theorem rawMobiusDiagonalEnergy_nonneg (N : ℕ) :
    0 ≤ rawMobiusDiagonalEnergy N :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem rawMobiusSignedAtom_norm_sq_le (d : ℕ) (hd : 0 < d) :
    ‖rawMobiusSignedAtom d‖ ^ 2 ≤ 2 / (d : ℝ) := by
  rw [rawMobiusSignedAtom, dif_pos hd, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  have hm : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hm2 : (ArithmeticFunction.moebius d : ℝ)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      pow_le_pow_left₀ (abs_nonneg (ArithmeticFunction.moebius d : ℝ)) hm 2
  calc
    _ ≤ 1 * ‖normalizedResidueHilbert d hd‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)
    _ ≤ _ := by simpa using normalizedResidue_norm_sq_le d hd

private theorem rawMobiusDiagonalEnergy_le_reciprocal_sum (N : ℕ) :
    rawMobiusDiagonalEnergy N ≤ 2 * ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
  unfold rawMobiusDiagonalEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  simpa only [mul_one_div] using
    rawMobiusSignedAtom_norm_sq_le d (Finset.mem_Icc.mp hd).1

private theorem rawMobius_reciprocal_sum_eq_harmonic (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ)) = (harmonic N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), harmonic_succ]
    push_cast
    rw [ih]
    simp only [one_div]

theorem rawMobiusDiagonalEnergy_le_harmonic (N : ℕ) :
    rawMobiusDiagonalEnergy N ≤ 2 * (harmonic N : ℝ) := by
  simpa only [rawMobius_reciprocal_sum_eq_harmonic] using
    rawMobiusDiagonalEnergy_le_reciprocal_sum N

private theorem rawMobius_sum_norm_sq_eq_diagonal_add_offDiagonal (N : ℕ) :
    ‖∑ d ∈ Finset.Icc 1 N, rawMobiusSignedAtom d‖ ^ 2 =
      rawMobiusDiagonalEnergy N + rawMobiusOffDiagonalEnergy N := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum]
  unfold rawMobiusDiagonalEnergy rawMobiusOffDiagonalEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_erase_add _
    (fun e => inner ℝ (rawMobiusSignedAtom d) (rawMobiusSignedAtom e)) hd,
    real_inner_self_eq_norm_sq]
  ring

theorem rawMobius_norm_sq_eq_diagonal_offDiagonal (N : ℕ) :
    ‖hilbertOne - rawMobiusHilbert N‖ ^ 2 =
      1 + 2 * logarithmicMobiusMean N +
        rawMobiusDiagonalEnergy N + rawMobiusOffDiagonalEnergy N := by
  have hp := rawMobiusResidual_inner_one_eq_logarithmicMean N
  have he := rawMobius_sum_norm_sq_eq_diagonal_add_offDiagonal N
  rw [rawMobiusHilbert_eq_signed_sum] at hp ⊢
  simp only [sub_neg_eq_add] at hp ⊢
  rw [inner_add_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq] at hp
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
    real_inner_self_eq_norm_sq]
  have hs := real_inner_comm hilbertOne
    (∑ d ∈ Finset.Icc 1 N, rawMobiusSignedAtom d)
  nlinarith

theorem rawMobiusOffDiagonalEnergy_le_budget (N : ℕ) (hN : 0 < N) :
    rawMobiusOffDiagonalEnergy N ≤
      rawMobiusSquareBudget N - 2 * logarithmicMobiusMean N := by
  have he := rawMobius_energy_le_square_window N hN
  change ‖hilbertOne - rawMobiusHilbert N‖^2 ≤ rawMobiusSquareBudget N + 1 at he
  rw [rawMobius_norm_sq_eq_diagonal_offDiagonal] at he
  linarith [rawMobiusDiagonalEnergy_nonneg N]

theorem rawMobiusBudget_le_offDiagonal_add_reciprocal (N : ℕ) :
    rawMobiusSquareBudget N ≤
      2 * rawMobiusOffDiagonalEnergy N +
        4 * ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) +
        2 + 4 * logarithmicMobiusMean N := by
  have hb := rawMobiusSquareBudget_le_two_raw_norm_sq N
  rw [rawMobius_norm_sq_eq_diagonal_offDiagonal] at hb
  linarith [rawMobiusDiagonalEnergy_le_reciprocal_sum N]

theorem rawMobiusBudget_eventual_signed_sandwich :
    ∀ᶠ N : ℕ in atTop,
      rawMobiusOffDiagonalEnergy N - 4 ≤ rawMobiusSquareBudget N ∧
      rawMobiusSquareBudget N ≤ 2 * rawMobiusOffDiagonalEnergy N +
        4 * ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
  have hlo := logarithmicMobiusMean_tendsto_neg_one.eventually
    (lt_mem_nhds (by norm_num : (-2 : ℝ) < -1))
  have hhi := logarithmicMobiusMean_tendsto_neg_one.eventually
    (gt_mem_nhds (by norm_num : (-1 : ℝ) < -1/2))
  filter_upwards [hlo, hhi, eventually_ge_atTop (1 : ℕ)] with N hlo hhi hN
  constructor
  · have h := rawMobiusOffDiagonalEnergy_le_budget N hN
    linarith
  · have h := rawMobiusBudget_le_offDiagonal_add_reciprocal N
    linarith


private theorem eventually_one_add_log_nat_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 1+Real.log ((N : ℝ)+1) ≤ ((N : ℝ)+1)^ε := by
  have hb : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop hε).comp hb
  have hi : Tendsto (fun N : ℕ => 1/((N : ℝ)+1)^ε) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hp
  have hl := (Real.tendsto_pow_log_div_pow_atTop ε 1 hε).comp hb
  simp only [Real.rpow_one] at hl
  have ht : Tendsto (fun N : ℕ =>
      (1+Real.log ((N : ℝ)+1))/((N : ℝ)+1)^ε) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_add, ← add_div] using hi.add hl
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with N hN
  have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos
    (by positivity : 0 < (N : ℝ)+1) ε)).mp hN
  simpa only [one_mul] using hh.le

theorem frequently_power_rawMobiusBudget_iff_offDiagonal
    (ε : ℝ) (hε : 0 < ε) :
    (∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      rawMobiusSquareBudget N ≤ C*((N : ℝ)+1)^ε) ↔
    (∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      rawMobiusOffDiagonalEnergy N ≤ C*((N : ℝ)+1)^ε) := by
  constructor
  · rintro ⟨C,hC⟩
    refine ⟨C+4, ?_⟩
    apply (hC.and_eventually rawMobiusBudget_eventual_signed_sandwich).mono
    intro N hN
    have hp : 1 ≤ ((N : ℝ)+1)^ε :=
      Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) N]) hε.le
    nlinarith [hN.1, hN.2.1]
  · rintro ⟨C,hC⟩
    refine ⟨2*C+4, ?_⟩
    have he := rawMobiusBudget_eventual_signed_sandwich.and
      ((eventually_one_add_log_nat_le_rpow ε hε).and (eventually_ge_atTop 1))
    apply (hC.and_eventually he).mono
    intro N hN
    have hnpos : (0 : ℝ) < N := by exact_mod_cast hN.2.2.2
    have hlog : Real.log (N : ℝ) ≤ Real.log ((N : ℝ)+1) :=
      Real.log_le_log hnpos (by linarith)
    have hH := harmonic_le_one_add_log N
    have hs := hN.2.1.2
    rw [rawMobius_reciprocal_sum_eq_harmonic] at hs
    nlinarith [hN.1, hN.2.2.1]

/-- Only the signed distinct-pair upper estimate remains an arithmetic input. -/
theorem riemannHypothesis_of_frequently_subpower_raw_offDiagonal
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      rawMobiusOffDiagonalEnergy N ≤ C*((N : ℝ)+1)^ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_subpower_raw_square_budget
  intro ε hε
  exact (frequently_power_rawMobiusBudget_iff_offDiagonal ε hε).mpr (hsub ε hε)


end RiemannResearch.RH.Pareto
