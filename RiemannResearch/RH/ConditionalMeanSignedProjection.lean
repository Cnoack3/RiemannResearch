import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.RH.ConditionalMeanTailNonattainment
import RiemannResearch.RH.ConditionalMeanSubpolynomial

/-!
# Signed projection for the actual infinite conditional energy
Source: user-provided Exact CRT Energy Mean Repair handoff (2026-09-18),
Appendix 9, for the projection strategy. The signed series below is the
actual Cesaro pairing; it is not a uniform CRT residue average.
-/
open Filter
open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.Analysis.Cesaro

def conditionalMeanInner (F G : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, conditionalWeight k * cesaro F (k+1) * cesaro G (k+1)

theorem cesaro_add_mul (F G : ℕ → ℝ) (u : ℝ) (t : ℕ) :
    cesaro (fun n => F n + u*G n) t = cesaro F t + u*cesaro G t := by
  simp only [cesaro, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem legal_add_mul (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1)) (u : ℝ) :
    (fun n => F n + u*G n) ∈ legalSeedSpan (Set.Ici 1) := by
  exact (legalSeedSpan (Set.Ici 1)).add_mem hF
    ((legalSeedSpan (Set.Ici 1)).smul_mem u hG)

theorem conditionalMeanInner_summable (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1)) :
    Summable (fun k : ℕ => conditionalWeight k * cesaro F (k+1) * cesaro G (k+1)) := by
  have hp : ∀ a ∈ Set.Ici (1 : ℕ), 0 < a := by intro a ha; exact ha
  have hsF := legal_conditionalMeanSquare_summable _ hp hF
  have hsG := legal_conditionalMeanSquare_summable _ hp hG
  have hsS := legal_conditionalMeanSquare_summable _ hp (legal_add_mul F G hF hG 1)
  apply (((hsS.sub hsF).sub hsG).mul_left (1/2 : ℝ)).congr
  intro k
  simp only [cesaro_add_mul]
  ring

theorem conditionalMeanInner_self (F : ℕ → ℝ) :
    conditionalMeanInner F F = conditionalMeanSquare F := by
  apply tsum_congr
  intro k
  ring

theorem conditionalMeanInner_comm (F G : ℕ → ℝ) :
    conditionalMeanInner F G = conditionalMeanInner G F := by
  apply tsum_congr
  intro k
  ring

/-- Every mixed term remains signed inside the exact infinite identity. -/
theorem conditionalMeanSquare_add_mul (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1)) (u : ℝ) :
    conditionalMeanSquare (fun n => F n + u*G n) =
      conditionalMeanSquare F + 2*u*conditionalMeanInner F G +
        u^2*conditionalMeanSquare G := by
  have hp : ∀ a ∈ Set.Ici (1 : ℕ), 0 < a := by intro a ha; exact ha
  have hsF := legal_conditionalMeanSquare_summable _ hp hF
  have hsG := legal_conditionalMeanSquare_summable _ hp hG
  have hsI := conditionalMeanInner_summable F G hF hG
  unfold conditionalMeanSquare conditionalMeanInner
  calc
    _ = ∑' k : ℕ, (conditionalWeight k*(cesaro F (k+1))^2 +
        (2*u)*(conditionalWeight k*cesaro F (k+1)*cesaro G (k+1)) +
        u^2*(conditionalWeight k*(cesaro G (k+1))^2)) := by
      apply tsum_congr
      intro k
      rw [cesaro_add_mul]
      ring
    _ = _ := by
      rw [(hsF.add (hsI.mul_left (2*u))).tsum_add (hsG.mul_left (u^2)),
        hsF.tsum_add (hsI.mul_left (2*u))]
      simp only [tsum_mul_left]

/-- Completion of the complete signed energy, with its exact remainder. -/
theorem conditionalMeanSquare_complete_square (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hg : conditionalMeanSquare G ≠ 0) (u : ℝ) :
    conditionalMeanSquare (fun n => F n + u*G n) =
      conditionalMeanSquare F - (conditionalMeanInner F G)^2/conditionalMeanSquare G +
        conditionalMeanSquare G*(u+conditionalMeanInner F G/conditionalMeanSquare G)^2 := by
  rw [conditionalMeanSquare_add_mul F G hF hG u]
  field_simp
  ring

theorem conditionalMeanSquare_optimal_scalar (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hg : conditionalMeanSquare G ≠ 0) :
    conditionalMeanSquare
      (fun n => F n + (-conditionalMeanInner F G/conditionalMeanSquare G)*G n) =
      conditionalMeanSquare F - (conditionalMeanInner F G)^2/conditionalMeanSquare G := by
  rw [conditionalMeanSquare_complete_square F G hF hG hg]
  ring

theorem conditionalMeanInner_sq_le (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hg : 0 < conditionalMeanSquare G) :
    (conditionalMeanInner F G)^2 ≤ conditionalMeanSquare F*conditionalMeanSquare G := by
  have hn := conditionalMeanSquare_nonneg
    (fun n => F n + (-conditionalMeanInner F G/conditionalMeanSquare G)*G n)
  rw [conditionalMeanSquare_optimal_scalar F G hF hG (ne_of_gt hg)] at hn
  exact (div_le_iff₀ hg).mp (by linarith)

/-- The exact head constraint survives any legal direction with zero head. -/
theorem add_mul_mem_conditionalHeadClass (Y : ℕ) (F G : ℕ → ℝ)
    (hF : F ∈ conditionalHeadClass Y)
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hzero : ∀ n, 0 < n → n ≤ Y → G n = 0) (u : ℝ) :
    (fun n => F n+u*G n) ∈ conditionalHeadClass Y := by
  refine ⟨legal_add_mul F G hF.1 hG u, ?_⟩
  intro n hn hnY
  change F n + u*G n = 1
  rw [hF.2 n hn hnY, hzero n hn hnY]
  ring

/-- A concrete upper bound on the actual unrestricted head optimum. -/
theorem conditionalHeadMinimum_le_signed_projection (Y : ℕ) (F G : ℕ → ℝ)
    (hF : F ∈ conditionalHeadClass Y)
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hzero : ∀ n, 0 < n → n ≤ Y → G n = 0)
    (hg : conditionalMeanSquare G ≠ 0) :
    conditionalHeadMinimum Y ≤
      conditionalMeanSquare F - (conditionalMeanInner F G)^2/conditionalMeanSquare G := by
  have hm := conditionalHeadMinimum_le Y
    (add_mul_mem_conditionalHeadClass Y F G hF hG hzero
      (-conditionalMeanInner F G/conditionalMeanSquare G))
  rwa [conditionalMeanSquare_optimal_scalar F G hF.1 hG hg] at hm

/-- A lower head-mass floor limits any proposed correlation gain. -/
theorem signed_projection_gain_le_excess (Y : ℕ) (F G : ℕ → ℝ)
    (hF : F ∈ conditionalHeadClass Y)
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hzero : ∀ n, 0 < n → n ≤ Y → G n = 0)
    (hg : conditionalMeanSquare G ≠ 0) :
    (conditionalMeanInner F G)^2/conditionalMeanSquare G ≤
      conditionalMeanSquare F - (Y : ℝ)/((Y : ℝ)+2) := by
  have hmin := conditionalHeadMinimum_le_signed_projection Y F G hF hG hzero hg
  have hmass := conditionalHeadMinimum_ge_head_mass Y
  linarith


/-- Bilinearity of the actual signed infinite pairing. -/
theorem conditionalMeanInner_add_mul_right (F G H : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1)) (u : ℝ) :
    conditionalMeanInner F (fun n => G n+u*H n) =
      conditionalMeanInner F G+u*conditionalMeanInner F H := by
  have hsG := conditionalMeanInner_summable F G hF hG
  have hsH := conditionalMeanInner_summable F H hF hH
  unfold conditionalMeanInner
  calc
    _ = ∑' k : ℕ, (conditionalWeight k*cesaro F (k+1)*cesaro G (k+1) +
        u*(conditionalWeight k*cesaro F (k+1)*cesaro H (k+1))) := by
      apply tsum_congr
      intro k
      rw [cesaro_add_mul]
      ring
    _ = _ := by rw [hsG.tsum_add (hsH.mul_left u), tsum_mul_left]

theorem conditionalMeanInner_add_mul_left (F G H : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1)) (u : ℝ) :
    conditionalMeanInner (fun n => F n+u*G n) H =
      conditionalMeanInner F H+u*conditionalMeanInner G H := by
  rw [conditionalMeanInner_comm, conditionalMeanInner_add_mul_right H F G hH hF hG]
  rw [conditionalMeanInner_comm H F, conditionalMeanInner_comm H G]

/-- A zero-energy direction has zero signed correlation. No inverse is used. -/
theorem conditionalMeanInner_eq_zero_of_energy_zero (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hg : conditionalMeanSquare G = 0) : conditionalMeanInner F G = 0 := by
  by_contra hi
  have hn := conditionalMeanSquare_nonneg
    (fun n => F n + (-(conditionalMeanSquare F+1)/(2*conditionalMeanInner F G))*G n)
  rw [conditionalMeanSquare_add_mul F G hF hG, hg] at hn
  have he : conditionalMeanSquare F+
      2*(-(conditionalMeanSquare F+1)/(2*conditionalMeanInner F G))*conditionalMeanInner F G+
      (-(conditionalMeanSquare F+1)/(2*conditionalMeanInner F G))^2*0 = -1 := by
    field_simp
    ring
  rw [he] at hn
  norm_num at hn

/-- The complete two-direction Gram equality retains the covariance term. -/
theorem conditionalMeanSquare_two_directions (F G H : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1)) (a b : ℝ) :
    conditionalMeanSquare (fun n => F n+a*G n+b*H n) =
      conditionalMeanSquare F+2*a*conditionalMeanInner F G+
        2*b*conditionalMeanInner F H+a^2*conditionalMeanSquare G+
        2*a*b*conditionalMeanInner G H+b^2*conditionalMeanSquare H := by
  rw [conditionalMeanSquare_add_mul (fun n => F n+a*G n) H
    (legal_add_mul F G hF hG a) hH b,
    conditionalMeanSquare_add_mul F G hF hG a,
    conditionalMeanInner_add_mul_left F G H hF hG hH a]
  ring

/-- Screening is performed in the actual weighted Cesaro geometry. -/
def screenedDirection (G H : ℕ → ℝ) (n : ℕ) : ℝ :=
  H n+(-conditionalMeanInner G H/conditionalMeanSquare G)*G n

theorem screenedDirection_legal (G H : ℕ → ℝ)
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1)) :
    screenedDirection G H ∈ legalSeedSpan (Set.Ici 1) :=
  legal_add_mul H G hH hG _

theorem screenedDirection_energy (G H : ℕ → ℝ)
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1))
    (hg : conditionalMeanSquare G ≠ 0) :
    conditionalMeanSquare (screenedDirection G H) =
      conditionalMeanSquare H-(conditionalMeanInner G H)^2/conditionalMeanSquare G := by
  unfold screenedDirection
  rw [conditionalMeanInner_comm G H]
  exact conditionalMeanSquare_optimal_scalar H G hH hG hg

theorem screenedDirection_source (F G H : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanInner F (screenedDirection G H) =
      conditionalMeanInner F H-
        conditionalMeanInner G H*conditionalMeanInner F G/conditionalMeanSquare G := by
  unfold screenedDirection
  rw [conditionalMeanInner_add_mul_right F H G hF hH hG]
  ring

theorem screenedDirection_orthogonal (G H : ℕ → ℝ)
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1))
    (hg : conditionalMeanSquare G ≠ 0) :
    conditionalMeanInner G (screenedDirection G H) = 0 := by
  rw [screenedDirection_source G G H hG hG hH, conditionalMeanInner_self]
  field_simp
  ring

/-- The singular Schur branch has zero residual source, not an omitted division. -/
theorem screenedDirection_singular_source (F G H : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1))
    (hg : conditionalMeanSquare G ≠ 0)
    (hs : conditionalMeanSquare H-
      (conditionalMeanInner G H)^2/conditionalMeanSquare G = 0) :
    conditionalMeanInner F H-
      conditionalMeanInner G H*conditionalMeanInner F G/conditionalMeanSquare G = 0 := by
  rw [← screenedDirection_source F G H hF hG hH]
  apply conditionalMeanInner_eq_zero_of_energy_zero F (screenedDirection G H) hF
    (screenedDirection_legal G H hG hH)
  rwa [screenedDirection_energy G H hG hH hg]

/-- Full Schur gain from the two actual signed directions, including screening. -/
theorem conditionalMeanSquare_schur_optimum (F G H : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hH : H ∈ legalSeedSpan (Set.Ici 1))
    (hg : conditionalMeanSquare G ≠ 0) :
    conditionalMeanSquare (fun n =>
      (F n+(-conditionalMeanInner F G/conditionalMeanSquare G)*G n)+
      (-conditionalMeanInner F (screenedDirection G H)/
        conditionalMeanSquare (screenedDirection G H))*screenedDirection G H n) =
      conditionalMeanSquare F-(conditionalMeanInner F G)^2/conditionalMeanSquare G-
        (conditionalMeanInner F (screenedDirection G H))^2/
          conditionalMeanSquare (screenedDirection G H) := by
  have hV := screenedDirection_legal G H hG hH
  by_cases hs : conditionalMeanSquare (screenedDirection G H) = 0
  · have hsrc := conditionalMeanInner_eq_zero_of_energy_zero F
      (screenedDirection G H) hF hV hs
    simp only [hs,hsrc,neg_zero,zero_div,zero_mul,add_zero,zero_pow (by decide : 2 ≠ 0),
      sub_zero]
    exact conditionalMeanSquare_optimal_scalar F G hF hG hg
  have horth := screenedDirection_orthogonal G H hG hH hg
  have hsrc : conditionalMeanInner
      (fun n => F n+(-conditionalMeanInner F G/conditionalMeanSquare G)*G n)
      (screenedDirection G H) = conditionalMeanInner F (screenedDirection G H) := by
    rw [conditionalMeanInner_add_mul_left F G (screenedDirection G H) hF hG hV,
      horth, mul_zero, add_zero]
  conv_lhs =>
    arg 1
    ext n
    rw [← hsrc]
  rw [conditionalMeanSquare_optimal_scalar _ _ (legal_add_mul F G hF hG _) hV hs,
    hsrc, conditionalMeanSquare_optimal_scalar F G hF hG hg]


/-- Conditional RH endpoint: the remaining hypothesis bounds the actual signed
projection remainder on a cofinal family. It is not discharged here. -/
theorem riemannHypothesis_of_signed_projection_subpolynomial
    (F G : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hF : ∀ j, F j ∈ conditionalHeadClass (Y j))
    (hG : ∀ j, G j ∈ legalSeedSpan (Set.Ici 1))
    (hzero : ∀ j n, 0 < n → n ≤ Y j → G j n = 0)
    (hg : ∀ j, conditionalMeanSquare (G j) ≠ 0)
    (hY : Filter.Tendsto Y Filter.atTop Filter.atTop)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ j : ℕ in Filter.atTop,
        conditionalMeanSquare (F j)-
          (conditionalMeanInner (F j) (G j))^2/conditionalMeanSquare (G j) ≤
            C*(Y j : ℝ)^ε) : RiemannHypothesis := by
  let K : ℕ → ℕ → ℝ := fun j n => F j n+
    (-conditionalMeanInner (F j) (G j)/conditionalMeanSquare (G j))*G j n
  have hK : ∀ j, K j ∈ conditionalHeadClass (Y j) :=
    fun j => add_mul_mem_conditionalHeadClass (Y j) (F j) (G j)
      (hF j) (hG j) (hzero j) _
  apply riemannHypothesis_of_subpolynomial_conditionalMean_heads
    (Set.Ici 1) (by intro a ha; exact ha) K Y
    (fun j => (hK j).1) (fun j => (hK j).2) hY
  intro ε hε
  obtain ⟨C,hC,hCbound⟩ := hbound ε hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hCbound] with j hj
  change conditionalMeanSquare (fun n => F j n+
    (-conditionalMeanInner (F j) (G j)/conditionalMeanSquare (G j))*G j n) ≤ _
  rwa [conditionalMeanSquare_optimal_scalar (F j) (G j) (hF j).1 (hG j) (hg j)]


/-- The complete two-direction signed Schur remainder is an RH-sufficient
arithmetic target. Singular screened directions are included by the proved
zero-source rule. This bound remains an explicit hypothesis. -/
theorem riemannHypothesis_of_signed_schur_subpolynomial
    (F G H : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hF : ∀ j, F j ∈ conditionalHeadClass (Y j))
    (hG : ∀ j, G j ∈ legalSeedSpan (Set.Ici 1))
    (hH : ∀ j, H j ∈ legalSeedSpan (Set.Ici 1))
    (hGzero : ∀ j n, 0 < n → n ≤ Y j → G j n = 0)
    (hHzero : ∀ j n, 0 < n → n ≤ Y j → H j n = 0)
    (hg : ∀ j, conditionalMeanSquare (G j) ≠ 0)
    (hY : Tendsto Y atTop atTop)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop,
        conditionalMeanSquare (F j)-
          (conditionalMeanInner (F j) (G j))^2/conditionalMeanSquare (G j)-
          (conditionalMeanInner (F j) (screenedDirection (G j) (H j)))^2/
            conditionalMeanSquare (screenedDirection (G j) (H j)) ≤ C*(Y j : ℝ)^ε) :
    RiemannHypothesis := by
  let V : ℕ → ℕ → ℝ := fun j => screenedDirection (G j) (H j)
  let K : ℕ → ℕ → ℝ := fun j n =>
    (F j n+(-conditionalMeanInner (F j) (G j)/conditionalMeanSquare (G j))*G j n)+
      (-conditionalMeanInner (F j) (V j)/conditionalMeanSquare (V j))*V j n
  have hV : ∀ j, V j ∈ legalSeedSpan (Set.Ici 1) :=
    fun j => screenedDirection_legal (G j) (H j) (hG j) (hH j)
  have hVzero : ∀ j n, 0 < n → n ≤ Y j → V j n = 0 := by
    intro j n hn hnY
    dsimp [V,screenedDirection]
    rw [hGzero j n hn hnY,hHzero j n hn hnY]
    ring
  have hK : ∀ j, K j ∈ conditionalHeadClass (Y j) := by
    intro j
    exact add_mul_mem_conditionalHeadClass (Y j) _
      (V j) (add_mul_mem_conditionalHeadClass (Y j) (F j) (G j)
        (hF j) (hG j) (hGzero j) _) (hV j) (hVzero j) _
  apply riemannHypothesis_of_subpolynomial_conditionalMean_heads
    (Set.Ici 1) (by intro a ha; exact ha) K Y
    (fun j => (hK j).1) (fun j => (hK j).2) hY
  intro ε hε
  obtain ⟨C,hC,hCbound⟩ := hbound ε hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hCbound] with j hj
  change conditionalMeanSquare (fun n =>
    (F j n+(-conditionalMeanInner (F j) (G j)/conditionalMeanSquare (G j))*G j n)+
      (-conditionalMeanInner (F j) (screenedDirection (G j) (H j))/
        conditionalMeanSquare (screenedDirection (G j) (H j)))*
          screenedDirection (G j) (H j) n) ≤ _
  rwa [conditionalMeanSquare_schur_optimum (F j) (G j) (H j) (hF j).1 (hG j) (hH j) (hg j)]

/-! Source: CRTProjectionContinuation20260918.md, Section 4, for the
locality argument. These statements concern the actual signed energy and
allow every finite legal correction preserving the indicated prefix. -/

/-- Exact localization: equal positive heads cancel from the energy difference. -/
theorem conditionalMeanSquare_gain_eq_tail_difference
    (F G : ℕ → ℝ) (M : ℕ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hhead : ∀ n, 0 < n → n ≤ M → F n = G n) :
    conditionalMeanSquare F - conditionalMeanSquare G =
      conditionalMeanTailSquare M F - conditionalMeanTailSquare M G := by
  have hcesaro (t : ℕ) (ht : t ≤ M) : cesaro F t = cesaro G t := by
    unfold cesaro
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnt⟩ := Finset.mem_Icc.mp hn
    exact hhead n (by omega) (hnt.trans ht)
  have hsF := (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hF).sum_add_tsum_nat_add M
  have hsG := (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hG).sum_add_tsum_nat_add M
  have he : (∑ k ∈ Finset.range M,
      conditionalWeight k * (cesaro F (k+1))^2) =
      ∑ k ∈ Finset.range M, conditionalWeight k * (cesaro G (k+1))^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcesaro (k+1)
      (by have := Finset.mem_range.mp hk; omega)]
  change _ + conditionalMeanTailSquare M F = conditionalMeanSquare F at hsF
  change _ + conditionalMeanTailSquare M G = conditionalMeanSquare G at hsG
  rw [he] at hsF
  linarith

/-- An arbitrary legal correction preserving the prefix can remove no more
than the original tail energy, regardless of its coefficients or conductor. -/
theorem conditionalMeanSquare_gain_le_original_tail
    (F G : ℕ → ℝ) (M : ℕ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hhead : ∀ n, 0 < n → n ≤ M → F n = G n) :
    conditionalMeanSquare F - conditionalMeanSquare G ≤ conditionalMeanTailSquare M F := by
  rw [conditionalMeanSquare_gain_eq_tail_difference F G M hF hG hhead]
  exact sub_le_self _ (conditionalMeanTailSquare_nonneg M G)

/-- The exact signed optimal scalar gain obeys the same locality bound. -/
theorem delayed_scalar_gain_le_original_tail
    (F R : ℕ → ℝ) (M : ℕ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hR : R ∈ legalSeedSpan (Set.Ici 1))
    (hzero : ∀ n, 0 < n → n ≤ M → R n = 0)
    (hg : conditionalMeanSquare R ≠ 0) :
    (conditionalMeanInner F R)^2 / conditionalMeanSquare R ≤
      conditionalMeanTailSquare M F := by
  have h := conditionalMeanSquare_gain_le_original_tail F
    (fun n => F n+(-conditionalMeanInner F R/conditionalMeanSquare R)*R n) M
    hF (legal_add_mul F R hF hR _)
    (by intro n hn hnM; simp only [hzero n hn hnM, mul_zero, add_zero])
  rw [conditionalMeanSquare_optimal_scalar F R hF hR hg] at h
  linarith

end RiemannResearch.RH.Pareto
