/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Commutator centering and horizontal phase-Gram bootstrap

Source: the research continuation of the user-provided
`Prime_Phases_Agenda_Proof_Attempts.tex`, recorded in
`RH/GrowingPhaseGramBootstrapAudit20261005.md`.

The exact scalar-centering identity halves the norm budget of each
positive-order commutator when its centered-moment norm premise holds.
The actual even cosh series gives absolute convergence, an explicit finite
truncation bound, and deterministic norm absorption and invertibility.

For Euclidean positive operators, the centered-moment premise is proved from
Mathlib's Rayleigh characterization in HorizontalEuclideanMoments.lean and
specialized to every actual zero copy in ActualZeroPhaseMoments.lean.
This abstract module retains its explicit norm premise. The exact actual-zero commutator
identity, uniform Landau estimate, and zero-density providers are separate
formalization obligations. The audit note cites Ford--Zaharescu Lemma 1
and Chourasiya--Simonic Corollary 1 for those paper-level analytic inputs.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.HorizontalPhaseBootstrap
variable {A : Type*} [NormedRing A]
def commutator (D M : A) : A := D * M - M * D
def iterComm (D : A) : ℕ → A → A
  | 0, M => M
  | n + 1, M => commutator D (iterComm D n M)
theorem commutator_norm_le (D M : A) :
    ‖commutator D M‖ ≤ (2 * ‖D‖) * ‖M‖ := by
  calc
    _ ≤ ‖D * M‖ + ‖M * D‖ := norm_sub_le _ _
    _ ≤ ‖D‖ * ‖M‖ + ‖M‖ * ‖D‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring
theorem iterComm_norm_le (D M : A) (w : ℝ) (hw : 2 * ‖D‖ ≤ w) (n : ℕ) :
    ‖iterComm D n M‖ ≤ w ^ n * ‖M‖ := by
  have hw0 : 0 ≤ w := le_trans (by positivity) hw
  induction n with
  | zero => simp [iterComm]
  | succ n ih =>
    calc
      _ ≤ (2 * ‖D‖) * ‖iterComm D n M‖ := commutator_norm_le _ _
      _ ≤ w * (w ^ n * ‖M‖) :=
        mul_le_mul hw ih (norm_nonneg _) hw0
      _ = _ := by rw [pow_succ]; ring
variable [NormedAlgebra ℝ A]

theorem commutator_sub_scalar (D M : A) (c : ℝ) :
    commutator D (M - c • (1 : A)) = commutator D M := by
  simp only [commutator, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  abel
theorem iterComm_sub_scalar (D M : A) (c : ℝ) (n : ℕ) :
    iterComm D (n + 1) (M - c • (1 : A)) = iterComm D (n + 1) M := by
  induction n with
  | zero => simpa [iterComm] using commutator_sub_scalar D M c
  | succ n ih =>
    change commutator D (iterComm D (n + 1) (M - c • (1 : A))) =
      commutator D (iterComm D (n + 1) M)
    rw [ih]
theorem iterComm_norm_le_half (D M : A) (w b : ℝ)
    (hw : 2 * ‖D‖ ≤ w) (hM : ‖M - (b / 2) • (1 : A)‖ ≤ b / 2) (n : ℕ) :
    ‖iterComm D (n + 1) M‖ ≤ w ^ (n + 1) * b / 2 := by
  have hw0 : 0 ≤ w := le_trans (by positivity) hw
  rw [← iterComm_sub_scalar D M (b / 2) n]
  calc
    _ ≤ w ^ (n + 1) * ‖M - (b / 2) • (1 : A)‖ := iterComm_norm_le _ _ w hw _
    _ ≤ w ^ (n + 1) * (b / 2) := mul_le_mul_of_nonneg_left hM (pow_nonneg hw0 _)
    _ = _ := by ring

/-- Positive-order version of the exact scalar-centering improvement. -/
theorem iterComm_norm_le_half_pos (D M : A) (w b : ℝ)
    (hw : 2 * ‖D‖ ≤ w) (hM : ‖M - (b / 2) • (1 : A)‖ ≤ b / 2)
    (n : ℕ) (hn : 0 < n) :
    ‖iterComm D n M‖ ≤ w ^ n * b / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact iterComm_norm_le_half D M w b hw hM k

/-- The actual even commutator term, omitting only the zeroth-order term. -/
noncomputable def evenTerm (D : A) (M : ℕ → A) (k : ℕ) : A :=
  ((Nat.factorial (2 * (k + 1)) : ℝ)⁻¹) •
    iterComm D (2 * (k + 1)) (M (k + 1))

theorem evenTerm_norm_le (D : A) (M : ℕ → A) (w δ g : ℝ)
    (hw : 2 * ‖D‖ ≤ w)
    (hM : ∀ k, ‖M (k + 1) - (δ ^ (2 * (k + 1)) * g / 2) • (1 : A)‖ ≤
      δ ^ (2 * (k + 1)) * g / 2) (k : ℕ) :
    ‖evenTerm D M k‖ ≤
      (g / 2) * ((δ * w) ^ (2 * (k + 1)) / (Nat.factorial (2 * (k + 1)) : ℝ)) := by
  have hf : (0 : ℝ) ≤ (Nat.factorial (2 * (k + 1)) : ℝ)⁻¹ := by positivity
  have hb := iterComm_norm_le_half_pos D (M (k + 1)) w
    (δ ^ (2 * (k + 1)) * g) hw (hM k) (2 * (k + 1)) (by omega)
  rw [evenTerm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hf]
  calc
    _ ≤ (Nat.factorial (2 * (k + 1)) : ℝ)⁻¹ *
        (w ^ (2 * (k + 1)) * (δ ^ (2 * (k + 1)) * g) / 2) :=
      mul_le_mul_of_nonneg_left hb hf
    _ = _ := by rw [mul_pow]; ring

theorem cosh_tail_summable (q : ℝ) :
    Summable (fun k : ℕ => q ^ (2 * (k + 1)) / (Nat.factorial (2 * (k + 1)) : ℝ)) :=
  (summable_nat_add_iff 1).mpr (Real.hasSum_cosh q).summable

theorem cosh_tail_tsum (q : ℝ) :
    (∑' k : ℕ, q ^ (2 * (k + 1)) / (Nat.factorial (2 * (k + 1)) : ℝ)) =
      Real.cosh q - 1 := by
  have h := (Real.hasSum_cosh q).summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at h
  rw [(Real.hasSum_cosh q).tsum_eq] at h
  linarith

variable [CompleteSpace A]

/-- The full even correction is absolutely summable and has the improved half
factor. The centered-moment norm premise is explicit; this theorem does not
supply an actual-zeta zero-density or Landau provider. -/
theorem evenCorrection_summable_and_norm_le (D : A) (M : ℕ → A) (w δ g : ℝ)
    (hw : 2 * ‖D‖ ≤ w)
    (hM : ∀ k, ‖M (k + 1) - (δ ^ (2 * (k + 1)) * g / 2) • (1 : A)‖ ≤
      δ ^ (2 * (k + 1)) * g / 2) :
    Summable (fun k => ‖evenTerm D M k‖) ∧
      Summable (evenTerm D M) ∧
      ‖∑' k, evenTerm D M k‖ ≤ (g / 2) * (Real.cosh (δ * w) - 1) := by
  let majorant : ℕ → ℝ := fun k =>
    (g / 2) * ((δ * w) ^ (2 * (k + 1)) / (Nat.factorial (2 * (k + 1)) : ℝ))
  have hs : Summable majorant := (cosh_tail_summable (δ * w)).mul_left (g / 2)
  have hb : ∀ k, ‖evenTerm D M k‖ ≤ majorant k := evenTerm_norm_le D M w δ g hw hM
  have hn : Summable (fun k => ‖evenTerm D M k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  have ht : Summable (evenTerm D M) := Summable.of_norm_bounded hs hb
  refine ⟨hn, ht, ?_⟩
  calc
    _ ≤ ∑' k, ‖evenTerm D M k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, majorant k := Summable.tsum_le_tsum hb hn hs
    _ = _ := by
      change (∑' k, (g / 2) *
        ((δ * w) ^ (2 * (k + 1)) / (Nat.factorial (2 * (k + 1)) : ℝ))) = _
      rw [tsum_mul_left, cosh_tail_tsum]



/-- Explicit finite-head truncation bound for the complete even correction.
Both the full series and every retained endpoint of the head are present. -/
theorem evenCorrection_truncation_norm_le (D : A) (M : ℕ → A) (w δ g : ℝ)
    (hw : 2 * ‖D‖ ≤ w)
    (hM : ∀ k, ‖M (k + 1) - (δ ^ (2 * (k + 1)) * g / 2) • (1 : A)‖ ≤
      δ ^ (2 * (k + 1)) * g / 2) (J : ℕ) :
    ‖(∑' k, evenTerm D M k) - ∑ k ∈ Finset.range J, evenTerm D M k‖ ≤
      (g / 2) * (Real.cosh (δ * w) - 1) -
        ∑ k ∈ Finset.range J,
          (g / 2) * ((δ * w) ^ (2 * (k + 1)) /
            (Nat.factorial (2 * (k + 1)) : ℝ)) := by
  let majorant : ℕ → ℝ := fun k =>
    (g / 2) * ((δ * w) ^ (2 * (k + 1)) / (Nat.factorial (2 * (k + 1)) : ℝ))
  have hs : Summable majorant := (cosh_tail_summable (δ * w)).mul_left (g / 2)
  have hb : ∀ k, ‖evenTerm D M k‖ ≤ majorant k := evenTerm_norm_le D M w δ g hw hM
  obtain ⟨hn, ht, _⟩ := evenCorrection_summable_and_norm_le D M w δ g hw hM
  have hnJ : Summable (fun k => ‖evenTerm D M (k + J)‖) :=
    (summable_nat_add_iff J).mpr hn
  have hsJ : Summable (fun k => majorant (k + J)) :=
    (summable_nat_add_iff J).mpr hs
  have he := ht.sum_add_tsum_nat_add J
  have hm := hs.sum_add_tsum_nat_add J
  have htotal : (∑' k, majorant k) = (g / 2) * (Real.cosh (δ * w) - 1) := by
    dsimp [majorant]
    rw [tsum_mul_left, cosh_tail_tsum]
  rw [htotal] at hm
  calc
    _ = ‖∑' k, evenTerm D M (k + J)‖ := by
      rw [← he, add_sub_cancel_left]
    _ ≤ ∑' k, ‖evenTerm D M (k + J)‖ := norm_tsum_le_tsum_norm hnJ
    _ ≤ ∑' k, majorant (k + J) :=
      Summable.tsum_le_tsum (fun k => hb (k + J)) hnJ hsJ
    _ = _ := by
      change (∑' k, majorant (k + J)) =
        (g / 2) * (Real.cosh (δ * w) - 1) - ∑ k ∈ Finset.range J, majorant k
      linarith

/-- Absorb the Gram norm on the right without presuming its boundedness. -/
theorem absorb {z α β ε : ℝ} (hε : ε < 1)
    (h : z ≤ α + β + ε * (1 + z)) :
    z ≤ (α + β + ε) / (1 - ε) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - ε)).2
  nlinarith

section NormBootstrap
variable {E : Type*} [NormedAddCommGroup E]

/-- Deterministic bootstrap in the actual norm. All analytic estimates are
explicit premises. For operators use their operator norm, not a default
entrywise matrix norm. -/
theorem norm_sub_bootstrap (G H I : E) (α β ε : ℝ)
    (hI : ‖I‖ ≤ 1) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hH : ‖H - I‖ ≤ α) (hGH : ‖G - H‖ ≤ β + ε * ‖G‖) :
    ‖G - I‖ ≤ (α + β + ε) / (1 - ε) := by
  have hnG : ‖G‖ ≤ ‖G - I‖ + 1 := by
    calc
      _ = ‖(G - I) + I‖ := by rw [sub_add_cancel]
      _ ≤ ‖G - I‖ + ‖I‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hI
  apply absorb hε
  calc
    _ = ‖(G - H) + (H - I)‖ := by congr 1; abel
    _ ≤ ‖G - H‖ + ‖H - I‖ := norm_add_le _ _
    _ ≤ (β + ε * ‖G‖) + α := add_le_add hGH hH
    _ ≤ (β + ε * (‖G - I‖ + 1)) + α := by gcongr
    _ = _ := by ring

theorem norm_self_le_of_bootstrap (G H I : E) (α β ε : ℝ)
    (hI : ‖I‖ ≤ 1) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hH : ‖H - I‖ ≤ α) (hGH : ‖G - H‖ ≤ β + ε * ‖G‖) :
    ‖G‖ ≤ (1 + α + β) / (1 - ε) := by
  have hd := norm_sub_bootstrap G H I α β ε hI hε0 hε hH hGH
  calc
    _ = ‖(G - I) + I‖ := by rw [sub_add_cancel]
    _ ≤ ‖G - I‖ + ‖I‖ := norm_add_le _ _
    _ ≤ (α + β + ε) / (1 - ε) + 1 := add_le_add hd hI
    _ = _ := by
      have hz : 1 - ε ≠ 0 := by linarith
      field_simp [hz]
      ring

theorem norm_sub_lt_one_of_bootstrap (G H I : E) (α β ε : ℝ)
    (hI : ‖I‖ ≤ 1) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hH : ‖H - I‖ ≤ α) (hGH : ‖G - H‖ ≤ β + ε * ‖G‖)
    (hsmall : α + β + 2 * ε < 1) : ‖G - I‖ < 1 := by
  apply lt_of_le_of_lt (norm_sub_bootstrap G H I α β ε hI hε0 hε hH hGH)
  apply (div_lt_one (by linarith : 0 < 1 - ε)).2
  linarith

end NormBootstrap


/-- The nonnegative cosh correction, proved from its actual even series. -/
theorem cosh_sub_one_nonneg (q : ℝ) : 0 ≤ Real.cosh q - 1 := by
  rw [← cosh_tail_tsum]
  apply tsum_nonneg
  intro k
  apply div_nonneg
  · rw [pow_mul]
    positivity
  · positivity

section Assembly
variable [NormOneClass A]

/-- Assemble the exact correction identity, including the bad-copy remainder,
with the improved commutator series and the self-consistent Gram estimate. -/
theorem norm_sub_one_bound_of_evenCorrection
    (D : A) (M : ℕ → A) (G H B : A) (w δ α β : ℝ)
    (hw : 2 * ‖D‖ ≤ w)
    (hM : ∀ k, ‖M (k + 1) -
      (δ ^ (2 * (k + 1)) * ‖G‖ / 2) • (1 : A)‖ ≤
      δ ^ (2 * (k + 1)) * ‖G‖ / 2)
    (hH : ‖H - 1‖ ≤ α) (hB : ‖B‖ ≤ β)
    (hidentity : H - G = (∑' k, evenTerm D M k) + B)
    (hε : (Real.cosh (δ * w) - 1) / 2 < 1) :
    ‖G - 1‖ ≤
      (α + β + (Real.cosh (δ * w) - 1) / 2) /
        (1 - (Real.cosh (δ * w) - 1) / 2) := by
  have hc := (evenCorrection_summable_and_norm_le D M w δ ‖G‖ hw hM).2.2
  have hε0 : 0 ≤ (Real.cosh (δ * w) - 1) / 2 :=
    div_nonneg (cosh_sub_one_nonneg _) (by norm_num)
  apply norm_sub_bootstrap G H 1 α β ((Real.cosh (δ * w) - 1) / 2)
    (by simp) hε0 hε hH
  rw [norm_sub_rev, hidentity]
  calc
    _ ≤ ‖∑' k, evenTerm D M k‖ + ‖B‖ := norm_add_le _ _
    _ ≤ (‖G‖ / 2) * (Real.cosh (δ * w) - 1) + β := add_le_add hc hB
    _ = _ := by ring

/-- A strictly positive frame gap yields invertibility in a Banach algebra.
Actual-zeta estimates and the moment norm bound are still explicit premises. -/
theorem isUnit_of_evenCorrection
    (D : A) (M : ℕ → A) (G H B : A) (w δ α β : ℝ)
    (hw : 2 * ‖D‖ ≤ w)
    (hM : ∀ k, ‖M (k + 1) -
      (δ ^ (2 * (k + 1)) * ‖G‖ / 2) • (1 : A)‖ ≤
      δ ^ (2 * (k + 1)) * ‖G‖ / 2)
    (hH : ‖H - 1‖ ≤ α) (hB : ‖B‖ ≤ β)
    (hidentity : H - G = (∑' k, evenTerm D M k) + B)
    (hsmall : α + β + Real.cosh (δ * w) < 2) : IsUnit G := by
  have hc := norm_sub_one_bound_of_evenCorrection D M G H B w δ α β hw hM hH hB
    hidentity
  have hα : 0 ≤ α := le_trans (norm_nonneg _) hH
  have hβ : 0 ≤ β := le_trans (norm_nonneg _) hB
  have hε : (Real.cosh (δ * w) - 1) / 2 < 1 := by linarith
  have hn : ‖G - 1‖ < 1 := by
    apply lt_of_le_of_lt (hc hε)
    apply (div_lt_one (by linarith : 0 < 1 - (Real.cosh (δ * w) - 1) / 2)).2
    linarith
  have hu := isUnit_one_sub_of_norm_lt_one (x := (1 : A) - G) (by simpa [norm_sub_rev] using hn)
  convert hu using 1
  abel
end Assembly

end RiemannResearch.Analysis.HorizontalPhaseBootstrap
