import RiemannResearch.Analysis.ActualInghamLittlewoodAssembly
import Mathlib.Tactic

/-!
# Quantitative assembly of the classical Littlewood window

Chourasiya and Simonič, <https://arxiv.org/html/2507.15184v2>, equation (32).
Both heights are free. The cutoff is comparable to the upper height and
the lower height can be fixed before passing to global counts.
-/

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier

private theorem enlarged_power_log {T t A : ℝ} (hL : 1 ≤ Real.log T)
    (hT : 1 ≤ T) (hTt : T ≤ t) (ht : t ≤ 2 * T) (hA : A ∈ Icc (0 : ℝ) 1) :
    t^A * (Real.log t)^(1+A) ≤ 8*(T^A * (Real.log T)^(1+A)) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := hT0.trans_le hTt
  have hlogt : Real.log t ≤ 2*Real.log T := by
    have hl := Real.log_le_log ht0 ht
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hT0.ne'] at hl
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have h1 : t^A ≤ 2*T^A := by
    calc
      _ ≤ (2*T)^A := Real.rpow_le_rpow ht0.le ht hA.1
      _ = (2:ℝ)^A*T^A := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hA.2)
        (Real.rpow_nonneg hT0.le _)
  have h2 : (Real.log t)^(1+A) ≤ 4*(Real.log T)^(1+A) := by
    calc
      _ ≤ (2*Real.log T)^(1+A) := Real.rpow_le_rpow (Real.log_nonneg (hT.trans hTt)) hlogt
        (by linarith [hA.1])
      _ = (2:ℝ)^(1+A)*(Real.log T)^(1+A) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (show 1+A ≤ 2 by linarith [hA.2])
        norm_num at h ⊢
        exact h) (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (2*T^A)*(4*(Real.log T)^(1+A)) :=
      mul_le_mul h1 h2 (Real.rpow_nonneg (Real.log_nonneg (hT.trans hTt)) _) (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1200000 in
/-- Counts from the actual left moments and compatible horizontal arguments.
The two analytic estimates occur explicitly as independent hypotheses. -/
theorem littlewood_count_of_comparable_moment_and_argument
    {CM CA : ℝ} (hCM : 0 < CM) (hCA : 0 < CA)
    (hmoment : ∀ {X : ℕ}, 2 ≤ X → ∀ {t h a : ℝ}, 2 ≤ t → (X:ℝ) ≤ t →
      t ≤ 3*(X:ℝ) → 2 ≤ h → h ≤ t → a ∈ Icc (1/2 : ℝ) 1 →
      let β := 1 + 1/Real.log (X:ℝ)
      let θ := (a-1/2)/(β-1/2)
      (∫ u in h..t, ‖mollifiedError X ((a:ℂ)+(u:ℂ)*I)‖^(4/(3-θ))) ≤
        CM*t^(3*(1-θ)/(3-θ))*(Real.log t)^((6-4*θ)/(3-θ)))
    (hargs : ∀ {X : ℕ}, 72 ≤ X → ∀ {h t a : ℝ}, 3 ≤ h → h ≤ t → 1/2 ≤ a → a ≤ 3/2 →
      (∀ z ∈ RectangleBorder ((a:ℂ)+(h:ℂ)*I) (((3/2:ℝ):ℂ)+(t:ℂ)*I), zetaDetector X z ≠ 0) →
      ∀ B U : ℝ → ℂ, Continuous B → Continuous U →
        (RectangleIntegral' (fun z => (z-((a:ℂ)+(h:ℂ)*I))*logDeriv (zetaDetector X) z)
          ((a:ℂ)+(h:ℂ)*I) (((3/2 : ℝ):ℂ)+(t:ℂ)*I)).re =
          logRectangleBoundary (zetaDetector X) (fun u => (B u).im) (fun u => (U u).im)
            a (3/2) h t / (2*Real.pi) →
        (∫ u in a..(3/2), (U u).im)-(∫ u in a..(3/2), (B u).im) ≤
          CA*(1+Real.log (t+2)+Real.log ((X:ℝ)+1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 72 ≤ X → ∀ {H T σ : ℝ}, 4 ≤ H → H ≤ T →
      (X:ℝ) ≤ T → T ≤ 2*(X:ℝ) → 1 ≤ Real.log T → 1/2+2/(Real.log T) ≤ σ → σ ≤ 1 →
      ∃ a ∈ Ioo (σ-2/(Real.log T)) (σ-1/(Real.log T)),
        let β := 1 + 1/Real.log (X:ℝ)
        let θ := (a-1/2)/(β-1/2)
        let A := 3*(1-θ)/(3-θ)
        rightInclusiveCount T σ - rightInclusiveCount H σ ≤
          C*(Real.log T)*(T^A*(Real.log T)^(1+A) + Real.log T) := by
  refine ⟨8*CM+7*CA+216, by positivity, ?_⟩
  intro X hX H T σ hH hHT hXT hTX hL hσ hσ1
  let L := Real.log T
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have he : 0 < 1/L := by positivity
  have he1 : 1/L ≤ 1 := (div_le_one hLp).mpr hL
  have hT : 4 ≤ T := hH.trans hHT
  have hXa : (72:ℝ) ≤ X := by exact_mod_cast hX
  have heH : 1/L < H := by linarith only [he1,hH]
  have hab : σ-1/L < 3/2 := by linarith only [hσ1,he]
  obtain ⟨a,ha,h,hh,t,ht,hb,B,U,hB,hU,_,_,hn,hcount⟩ :=
    exists_actual_littlewood_moment_count (by omega : 37 ≤ X) hab (by linarith only [he] : σ-1/L<σ)
      hHT he heH
  have ha' : a ∈ Ioo (σ-2/L) (σ-1/L) := by
    rw [show σ-2/L = σ-1/L-1/L by ring]
    exact ha
  refine ⟨a,ha',?_⟩
  let β := 1 + 1/Real.log (X:ℝ)
  let θ := (a-1/2)/(β-1/2)
  let A := 3*(1-θ)/(3-θ)
  let M := ∫ u in h..t, ‖mollifiedError X ((a:ℂ)+(u:ℂ)*I)‖^(4/(3-θ))
  let G := (∫ u in a..(3/2), (U u).im)-(∫ u in a..(3/2), (B u).im)
  let R := (t-h)*(-Real.log (1-36/(X:ℝ)))
  let S := T^A*L^(1+A)
  change rightInclusiveCount T σ - rightInclusiveCount H σ ≤ (8*CM+7*CA+216)*L*(S+L)
  have ha0 : 1/2 ≤ a := by change 1/2+2/L ≤ σ at hσ; linarith only [ha'.1,hσ]
  have ha1 : a ≤ 1 := by linarith only [ha'.2,he,hσ1]
  have hlX := Real.log_pos (show (1 : ℝ) < X by linarith only [hXa])
  have hβ : 1 < β := by dsimp [β]; linarith only [one_div_pos.mpr hlX]
  have hd : 0 < β-1/2 := by linarith only [hβ]
  have hθ : θ ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ha0) hd.le
    · exact (div_le_one hd).mpr (by linarith only [ha1,hβ])
  have hden : 0 < 3-θ := by linarith only [hθ.2]
  have hA : A ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hθ.2)) hden.le
    · exact (div_le_one hden).mpr (by linarith only [hθ.1])
  have hp : 4/(3-θ) ∈ Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hden).mpr (by linarith only [hθ.1]),
      (div_le_iff₀ hden).mpr (by linarith only [hθ.2])⟩
  have hpow : (6-4*θ)/(3-θ)=1+A := by dsimp [A]; field_simp; ring
  have htH : 3 ≤ h := by linarith only [hh.1,he1,hH]
  have hhT : h ≤ t := hh.2.le.trans (hHT.trans ht.1.le)
  have htX : t ≤ 3*(X:ℝ) := by linarith only [ht.2,he1,hTX,hXa]
  have ht2 : t ≤ 2*T := by linarith only [ht.2,he1,hT]
  have hm : M ≤ 8*CM*S := by
    have h := hmoment (by omega : 2 ≤ X) (by linarith only [ht.1,hT] : 2 ≤ t)
      (hXT.trans ht.1.le) htX (by linarith only [htH] : 2 ≤ h) hhT ⟨ha0,ha1⟩
    change M ≤ CM*t^A*(Real.log t)^((6-4*θ)/(3-θ)) at h
    rw [hpow, mul_assoc] at h
    have h' := mul_le_mul_of_nonneg_left
      (enlarged_power_log hL (by linarith only [hT]) ht.1.le ht2 hA) hCM.le
    dsimp only [S,L]; linarith only [h,h']
  have hlg {v : ℝ} (hv : 0 < v) (hv2 : v ≤ 2*T) : Real.log v ≤ 2*L := by
    have hh := Real.log_le_log hv hv2
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith only [hT] : T ≠ 0)] at hh
    dsimp [L]; linarith only [hh,hL,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hg : G ≤ 7*CA*L := by
    have h := hargs hX htH hhT ha0 (by linarith only [ha1]) hb B U hB hU hn
    have h1 := hlg (v:=t+2) (by linarith only [ht.1,hT]) (by linarith only [ht.2,hT,he1])
    have h2 := hlg (v:=(X:ℝ)+1) (by positivity) (by linarith only [hXT,hT])
    change G ≤ _ at h
    calc
      G ≤ _ := h
      _ ≤ CA*(7*L) := mul_le_mul_of_nonneg_left
        (by change 1 ≤ L at hL; linarith only [h1,h2,hL]) hCA.le
      _ = _ := by ring
  have hr : R ≤ 216*L := by
    have hd0 : 0 < (X:ℝ)-36 := by linarith only [hXa]
    have hraw := mul_le_mul_of_nonneg_left (rightLogBudget_le_rational (by omega : 37≤X))
      (sub_nonneg.mpr hhT)
    have hfrac : (t-h)*(36/((X:ℝ)-36)) ≤ 216 := by
      rw [← mul_div_assoc]; apply (div_le_iff₀ hd0).mpr; linarith only [hXa,htX,htH]
    change R ≤ _ at hraw
    change 1 ≤ L at hL
    linarith only [hraw,hfrac,hL]
  have hS : 0 ≤ S := mul_nonneg (Real.rpow_nonneg (by linarith only [hT]) _)
    (Real.rpow_nonneg hLp.le _)
  have hsa : 0 < σ-a := by linarith only [ha'.2,he]
  have hgap : 0 < 2*Real.pi*(σ-a) := mul_pos (by positivity) hsa
  have hone : 1 ≤ L*(2*Real.pi*(σ-a)) := by
    have h0 : 1/L ≤ σ-a := by linarith only [ha'.2]
    have h1 := (div_le_iff₀ hLp).mp h0
    nlinarith only [h1, mul_nonneg (show 0 ≤ 2*Real.pi-1 by linarith only [Real.pi_gt_three])
      (mul_nonneg hLp.le hsa.le)]
  have hcount' := hcount _ hp
  change _ ≤ (M+G+R)/(2*Real.pi*(σ-a)) at hcount'
  refine hcount'.trans ((div_le_iff₀ hgap).mpr ?_)
  let C := 8*CM+7*CA+216
  have hbound : M+G+R ≤ C*(S+L) := by
    dsimp [C]
    nlinarith only [hm,hg,hr,hS,mul_nonneg hCM.le hLp.le,mul_nonneg hCA.le hS]
  have hP : 0 ≤ C*(S+L) := by dsimp [C]; positivity
  calc
    M+G+R ≤ C*(S+L) := hbound
    _ ≤ C*(S+L)*(L*(2*Real.pi*(σ-a))) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hP
    _ = _ := by dsimp [C]; ring

end RiemannResearch.Analysis.ActualZeroOrdinate
