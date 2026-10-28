/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QPrimePowerSieve
import RiemannResearch.RH.QPrimePowerPrimorial
import RiemannResearch.Analysis.FinitePrimeProductBounds
import RiemannResearch.Analysis.PrimeProductHeadGrowth
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit squarefree CRT approximants and a complete-energy obstruction

Source: the user-directed squarefree infinite-CRT research program,
28 October 2026. The construction and estimates are assembled here from
finite divisor inversion and existing finite prime-product bounds.
B. Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis", https://arxiv.org/abs/math/0607733, Theorem 1
and Remark 4, supports the weighted squarefree-closure interpretation.

Two actual finite legal families are kept separate. The corrected family
has expanding exact heads and converges pointwise to one. The raw Mobius
family also converges pointwise to one, but its complete Q norm diverges.
The exact corrected energy retains its signed mixed term.

No uniform energy bound, constant closure, or Riemann Hypothesis is proved
in this module. See CRTLegalApproximants20261028.md for the separate,
not-yet-formalized energy obstruction for the corrected family.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.QCRTCoprimeApproximation
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QPrimePowerSieve QSquarefreeLatticePackets

def coprimeApprox (L : ℕ) : QHilbert :=
  sieveVector L 1 + (Nat.totient L : ℝ) • qResidue L

theorem coprimeApprox_mem_divisorStage (L : ℕ) :
    coprimeApprox L ∈ divisorStage L := by
  exact (divisorStage L).add_mem (sieveVector_mem_divisorStage L 1)
    ((divisorStage L).smul_mem _ (Submodule.subset_span ⟨L, dvd_refl L, rfl⟩))

theorem coprimeApprox_legal (L : ℕ) (hL : 0 < L) (hsf : Squarefree L) :
    coprimeApprox L ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan L hL hsf (coprimeApprox_mem_divisorStage L)

theorem coprimeApprox_sequence (L n : ℕ) (hL : 0 < L) :
    qSequence (coprimeApprox L) n =
      sieveCount L 1 n - (Nat.totient L : ℝ) * (n / L : ℕ) := by
  have hseq : qSequence (coprimeApprox L) n =
      qSequence (sieveVector L 1) n + (Nat.totient L : ℝ) * residueFraction L n := by
    change qSequenceLinear (_ + _ • _) n = _
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change qSequence (sieveVector L 1) n + (Nat.totient L : ℝ) *
      qSequence (qResidue L) n = _
    rw [qSequence_qResidue]
  rw [hseq, qSequence_sieveVector L 1 n hL,
    sieveSlope_eq_totient L 1 hL (Nat.mem_divisors.mpr ⟨one_dvd L, ne_of_gt hL⟩)]
  simp only [Nat.div_one]
  have hm : ((n % L : ℕ) : ℝ) + (L : ℝ) * (n / L : ℕ) = n := by
    exact_mod_cast Nat.mod_add_div n L
  unfold residueFraction
  have hLR : (L : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem sieveCount_one_head (L H n : ℕ)
    (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L)
    (hn : 0 < n) (hnH : n ≤ H) : sieveCount L 1 n = 1 := by
  rw [sieveCount_eq_card]
  have he : (Finset.Icc 1 n).filter (fun k => Nat.gcd k L = 1) = {1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hk, hkn⟩, hg⟩
      by_contra hk1
      have hp := Nat.minFac_prime hk1
      have hpk : k.minFac ≤ k := Nat.minFac_le (by omega)
      have hpd := hcover k.minFac hp (hpk.trans (hkn.trans hnH))
      have hd := Nat.dvd_gcd (Nat.minFac_dvd k) hpd
      rw [hg] at hd
      exact hp.not_dvd_one hd
    · rintro rfl
      exact ⟨⟨by omega, hn⟩, by simp⟩
  rw [he]
  simp

theorem coprimeApprox_exact_head (L H n : ℕ) (hL : 0 < L)
    (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L)
    (hHL : H < L) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (coprimeApprox L) n = 1 := by
  rw [coprimeApprox_sequence L n hL, Nat.div_eq_of_lt (hnH.trans_lt hHL),
    Nat.cast_zero, mul_zero, sub_zero]
  exact sieveCount_one_head L H n hcover hn hnH

def approximant (j : ℕ) : QHilbert := coprimeApprox (primorial (j + 2))

theorem approximant_legal (j : ℕ) : approximant j ∈ qSquarefreeCRTSpan :=
  coprimeApprox_legal _ (primorial_pos _) (squarefree_primorial _)

theorem approximant_exact_head (j n : ℕ) (hn : 0 < n) (hnj : n ≤ j + 1) :
    qSequence (approximant j) n = 1 := by
  apply coprimeApprox_exact_head (primorial (j + 2)) (j + 1) n (primorial_pos _)
  · intro p hp hpj
    exact hp.dvd_primorial_iff.mpr (by omega)
  · exact lt_of_lt_of_le (by omega : j + 1 < j + 2) le_primorial_self
  · exact hn
  · exact hnj

theorem approximant_pointwise (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j => qSequence (approximant j) n) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with j hj
  exact (approximant_exact_head j n hn (by omega)).symm


open RiemannResearch.Analysis

/-- The uncorrected Möbius sieve, with actual finite squarefree support. -/
def rawApproximant (H : ℕ) : QHilbert := sieveVector (primorial H) 1

theorem rawApproximant_legal (H : ℕ) : rawApproximant H ∈ qSquarefreeCRTSpan :=
  sieveVector_mem_squarefreeSpan _ _ (primorial_pos _) (squarefree_primorial _)

theorem sieveSlope_primorial_one (H : ℕ) (hH : 2 ≤ H) :
    sieveSlope (primorial H) 1 = finitePrimeProduct H := by
  rw [sieveSlope_eq_totient _ _ (primorial_pos _)
    (Nat.mem_divisors.mpr ⟨one_dvd _, primorial_ne_zero H⟩), Nat.div_one]
  have h2 : 2 ∣ primorial H := Nat.prime_two.dvd_primorial_iff.mpr hH
  have h := sieveSlope_primorial_two H hH
  rw [sieveSlope_eq_totient _ _ (primorial_pos _)
    (Nat.mem_divisors.mpr ⟨h2, primorial_ne_zero H⟩),
    totient_div_two_of_squarefree _ (squarefree_primorial H) h2] at h
  exact h

theorem rawApproximant_head (H n : ℕ) (hH : 2 ≤ H)
    (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (rawApproximant H) n = 1 - finitePrimeProduct H * (n : ℝ) := by
  rw [rawApproximant, qSequence_sieveVector _ _ _ (primorial_pos _),
    sieveSlope_primorial_one H hH,
    sieveCount_one_head (primorial H) H n
      (fun p hp hpH => hp.dvd_primorial_iff.mpr hpH) hn hnH]

theorem rawApproximant_pointwise (n : ℕ) (hn : 0 < n) :
    Tendsto (fun H => qSequence (rawApproximant H) n) atTop (𝓝 1) := by
  have ht : Tendsto (fun H => 1 - finitePrimeProduct H * (n : ℝ))
      atTop (𝓝 1) := by
    simpa only [zero_mul, sub_zero] using
      tendsto_const_nhds.sub (finitePrimeProduct_tendsto_zero.mul_const (n : ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (max 2 n)] with H hH
  exact (rawApproximant_head H n ((le_max_left 2 n).trans hH)
    hn ((le_max_right 2 n).trans hH)).symm

theorem rawApproximant_norm_lower (H : ℕ) (hH : 2 ≤ H) :
    finitePrimeProduct H ^ 2 * (H : ℝ) / (2 * zetaTwo) - 1 ≤
      ‖rawApproximant H‖ ^ 2 := by
  simpa only [one_pow] using
    head_norm_lower (rawApproximant H) (fun _ => 1) (finitePrimeProduct H) 1 H
      (by norm_num) (by intro n hn; norm_num)
      (fun n hn => rawApproximant_head H n hH
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2)

theorem rawApproximant_norm_sq_tendsto_atTop :
    Tendsto (fun H => ‖rawApproximant H‖ ^ 2) atTop atTop := by
  have hg := finitePrimeProduct_head_tendsto_atTop zetaTwo zetaTwo_pos
  apply tendsto_atTop.2
  intro b
  filter_upwards [hg.eventually (eventually_ge_atTop (b + 1)),
    eventually_ge_atTop 2] with H hH hH2
  have he := rawApproximant_norm_lower H hH2
  nlinarith [sq_nonneg (Nat.log 2 H : ℝ)]

theorem rawApproximant_norm_tendsto_atTop :
    Tendsto (fun H => ‖rawApproximant H‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [rawApproximant_norm_sq_tendsto_atTop.eventually
    (eventually_ge_atTop ((max b 0) ^ 2))] with H hH
  have hmax : 0 ≤ max b 0 := le_max_right _ _
  exact (le_max_left b 0).trans ((sq_le_sq₀ hmax (norm_nonneg _)).mp hH)


/-- The actual coefficients are the complete signed divisor Möbius coefficients. -/
theorem rawApproximant_eq_moebius (H : ℕ) :
    rawApproximant H = -(∑ d ∈ (primorial H).divisors,
      (ArithmeticFunction.moebius d : ℝ) • qResidue d) := by
  unfold rawApproximant sieveVector
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [sieveCoefficient_eq _ 1 d
    (Nat.mem_divisors.mpr ⟨one_dvd _, primorial_ne_zero H⟩)]
  simp

/-- Exact complete energy of the correction; the mixed term is retained. -/
theorem coprimeApprox_norm_sq (L : ℕ) :
    ‖coprimeApprox L‖ ^ 2 =
      ‖sieveVector L 1‖ ^ 2 +
      2 * (Nat.totient L : ℝ) * inner ℝ (sieveVector L 1) (qResidue L) +
      (Nat.totient L : ℝ) ^ 2 * ‖qResidue L‖ ^ 2 := by
  rw [coprimeApprox, norm_add_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring


/-- Compatibility with the finite CRT projection, before taking any limit. -/
theorem coprimeApprox_mod (L n : ℕ) :
    qSequence (coprimeApprox L) (n % L) = qSequence (coprimeApprox L) n := by
  have hs (k : ℕ) : qSequence (coprimeApprox L) k =
      -(∑ d ∈ L.divisors, sieveCoefficient L 1 d * residueFraction d k) +
        (Nat.totient L : ℝ) * residueFraction L k := by
    unfold coprimeApprox sieveVector
    change qSequenceLinear (_ + _ • _) k = _
    simp only [map_add, map_neg, map_sum, map_smul, Pi.add_apply,
      Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change -(∑ d ∈ L.divisors, sieveCoefficient L 1 d * qSequence (qResidue d) k) +
      (Nat.totient L : ℝ) * qSequence (qResidue L) k = _
    simp only [qSequence_qResidue]
  rw [hs, hs]
  have he : (∑ d ∈ L.divisors, sieveCoefficient L 1 d * residueFraction d (n % L)) =
      ∑ d ∈ L.divisors, sieveCoefficient L 1 d * residueFraction d n := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [residueFraction, Nat.mod_mod_of_dvd n (Nat.dvd_of_mem_divisors hd)]
    rfl
  rw [he]
  simp only [residueFraction, Nat.mod_mod]

theorem coprimeApprox_count_mod (L n : ℕ) (hL : 0 < L) :
    qSequence (coprimeApprox L) n = sieveCount L 1 (n % L) := by
  rw [← coprimeApprox_mod L n, coprimeApprox_sequence L (n % L) hL,
    Nat.div_eq_of_lt (Nat.mod_lt n hL)]
  simp

end RiemannResearch.RH.QCRTCoprimeApproximation
