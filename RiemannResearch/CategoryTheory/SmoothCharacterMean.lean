import RiemannResearch.CategoryTheory.ObservedModeFibre

/-! # The physical joint moment of the revealed prime valuations

The head moment averages the character of the actual smooth part over every
positive site of the inverse-square distribution. The Hilbert projection
preserves the scalar mean and its smooth-site formula factors the full moment.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.SmoothCharacterMean
open RiemannResearch.CategoryTheory.ObservedModeFibre
open RiemannResearch.CategoryTheory.PrimeValuationCovariance
open RiemannResearch.CategoryTheory.DivisibilityCharacterGram
open RiemannResearch.RH.ZetaTwoHilbert

/-- Extend the smooth part to the unused coordinate zero, which has Q mass zero. -/
def smoothNat (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => (smoothSite b ⟨n+1, Nat.succ_pos _⟩ : ℕ)

def tailMoment {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∏' p : Nat.Primes, if p.val ≤ b then 1 else
    (1 - 1/(p : ℂ)^2)/(1 - χ p/(p : ℂ)^2)

def headMean {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' n : ℕ, (positiveQWeight n : ℂ) * χ ((smoothNat b n : ℕ) : ZMod q)

def fullMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' n : ℕ, (positiveQWeight n : ℂ) * χ (n : ZMod q)

private theorem weightedCharSummable {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℕ → ℕ) :
    Summable (fun n => (positiveQWeight n : ℂ) * χ ((s n : ℕ) : ZMod q)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ positiveQWeight_summable
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (positiveQWeight_nonneg n)]
  exact mul_le_of_le_one_right (positiveQWeight_nonneg n) (χ.norm_le_one _)

/-- Pull a real-linear character test through the whole physical Q mean. -/
theorem weighted_component {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℕ → ℕ)
    (c : ℂ) (L : ℂ →L[ℝ] ℝ) :
    (∑' n : ℕ, positiveQWeight n * L (χ ((s n : ℕ) : ZMod q)*c)) =
      L ((∑' n : ℕ, (positiveQWeight n : ℂ)*χ ((s n : ℕ) : ZMod q))*c) := by
  rw [← tsum_mul_right, L.map_tsum ((weightedCharSummable χ s).mul_right c)]
  apply tsum_congr
  intro n
  rw [mul_assoc, ← Complex.real_smul, map_smul, smul_eq_mul]

private theorem inner_one_component (x : QHilbert) (f : ℕ → ℝ)
    (hx : ∀ n, 0 < n → qSequence x n = f n) :
    inner ℝ x qOne = ∑' n, positiveQWeight n * f n := by
  rw [qInner_weighted, qSequence_qOne]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, positiveQWeight, qOneSequence]
  · simp [hx n (Nat.pos_of_ne_zero hn), qOneSequence, hn]

private theorem one_mem_observed (b : ℕ) : qOne ∈ observed b := by
  apply (mem_observed _ _).2
  intro i j _
  simp [qSequence_qOne, qOneSequence, i.pos.ne', j.pos.ne']

/-- Testing the full mean by any real-linear functional gives the smooth
character mean times the exact unrevealed Euler product. -/
theorem full_component_mean {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q)
    (L : ℂ →L[ℝ] ℝ) :
    (∑' n : ℕ, positiveQWeight n * L (χ (n : ZMod q))) =
      L (headMean b χ * tailMoment b χ) := by
  obtain ⟨x,hx⟩ := exists_mode_component 1 χ L
  have hxn (n : ℕ) (hn : 0<n) : qSequence x n = L (χ (n : ZMod q)) := by
    simpa [mode] using hx n hn
  have hproj (n : ℕ) (hn : 0<n) :
      qSequence ((observed b).starProjection x) n = L (χ (smoothNat b n : ZMod q)*tailMoment b χ) := by
    rcases n with _ | n
    · omega
    simpa [smoothNat, tailMoment] using
      observed_mode_at_site b ⟨n+1, Nat.succ_pos _⟩ 1 (by decide) χ L x hx
  have ho := (observed b).sub_starProjection_mem_orthogonal x qOne (one_mem_observed b)
  have he : inner ℝ x qOne = inner ℝ ((observed b).starProjection x) qOne := by
    rw [real_inner_comm, inner_sub_left] at ho
    exact sub_eq_zero.mp ho
  rw [inner_one_component x _ hxn, inner_one_component _ _ hproj] at he
  exact he.trans (weighted_component χ (smoothNat b) (tailMoment b χ) L)

/-- The full inverse-square moment factors into smooth and rough moments. -/
theorem fullMean_eq_head_mul_tail {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q) :
    fullMean χ = headMean b χ * tailMoment b χ := by
  apply Complex.ext
  · have ha := full_component_mean b χ Complex.reCLM
    have hb := weighted_component χ id 1 Complex.reCLM
    simp only [id_eq, mul_one, Complex.reCLM_apply] at ha hb
    exact hb.symm.trans ha
  · have ha := full_component_mean b χ Complex.imCLM
    have hb := weighted_component χ id 1 Complex.imCLM
    simp only [id_eq, mul_one, Complex.imCLM_apply] at ha hb
    exact hb.symm.trans ha

open ValuationCharacterGram

/-- The physical head moment is the finite product of the Euler factors at
the primes already revealed. -/
theorem headMean_eq_finite_product {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q) :
    headMean b χ = ∏ p ∈ revealedPrimeSet b, primeCharacterFactor χ p := by
  apply mul_right_cancel₀ (tailCharacterProduct_ne_zero b χ)
  calc
    headMean b χ * tailCharacterProduct b χ = fullMean χ := (fullMean_eq_head_mul_tail b χ).symm
    _ = tailCharacterProduct 0 χ := qCharacterMean_eq_fullProduct χ
    _ = _ := fullProduct_eq_head_mul_tail b χ

end RiemannResearch.CategoryTheory.SmoothCharacterMean
