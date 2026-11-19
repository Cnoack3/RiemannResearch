/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285DataCache

/-! # Verifying the monomial arrays from the degree-285 Laguerre weights

The table records factorials, odd double factorials and the original signed
weights. Its complete range is checked in the kernel. Each coefficient then
uses only table lookups, exact integer divisions and the original finite sum.
-/

namespace RiemannResearch.Analysis.LamzouriGapKernel285.CoefficientTable
open LamzouriGapKernel

set_option maxHeartbeats 0
set_option maxRecDepth 200000

private abbrev Row := ℕ × ℕ × ℤ

private def row (j : ℕ) : Row :=
  (j.factorial, oddProduct j, RiemannResearch.Analysis.LamzouriGapKernel285.laguerreCoefficients.getD j 0)

private def dataAt (j : ℕ) : Row :=
  if j < 143 then
    if j < 71 then
      if j < 35 then
        if j < 17 then
          if j < 8 then
            if j < 4 then
              if j = 0 then (eval% row 0) else if j = 1 then (eval% row 1) else if j = 2 then (eval% row 2) else (eval% row 3)
            else
              if j = 4 then (eval% row 4) else if j = 5 then (eval% row 5) else if j = 6 then (eval% row 6) else (eval% row 7)
          else
            if j < 12 then
              if j = 8 then (eval% row 8) else if j = 9 then (eval% row 9) else if j = 10 then (eval% row 10) else (eval% row 11)
            else
              if j < 14 then
                if j = 12 then (eval% row 12) else (eval% row 13)
              else
                if j = 14 then (eval% row 14) else if j = 15 then (eval% row 15) else (eval% row 16)
        else
          if j < 26 then
            if j < 21 then
              if j = 17 then (eval% row 17) else if j = 18 then (eval% row 18) else if j = 19 then (eval% row 19) else (eval% row 20)
            else
              if j < 23 then
                if j = 21 then (eval% row 21) else (eval% row 22)
              else
                if j = 23 then (eval% row 23) else if j = 24 then (eval% row 24) else (eval% row 25)
          else
            if j < 30 then
              if j = 26 then (eval% row 26) else if j = 27 then (eval% row 27) else if j = 28 then (eval% row 28) else (eval% row 29)
            else
              if j < 32 then
                if j = 30 then (eval% row 30) else (eval% row 31)
              else
                if j = 32 then (eval% row 32) else if j = 33 then (eval% row 33) else (eval% row 34)
      else
        if j < 53 then
          if j < 44 then
            if j < 39 then
              if j = 35 then (eval% row 35) else if j = 36 then (eval% row 36) else if j = 37 then (eval% row 37) else (eval% row 38)
            else
              if j < 41 then
                if j = 39 then (eval% row 39) else (eval% row 40)
              else
                if j = 41 then (eval% row 41) else if j = 42 then (eval% row 42) else (eval% row 43)
          else
            if j < 48 then
              if j = 44 then (eval% row 44) else if j = 45 then (eval% row 45) else if j = 46 then (eval% row 46) else (eval% row 47)
            else
              if j < 50 then
                if j = 48 then (eval% row 48) else (eval% row 49)
              else
                if j = 50 then (eval% row 50) else if j = 51 then (eval% row 51) else (eval% row 52)
        else
          if j < 62 then
            if j < 57 then
              if j = 53 then (eval% row 53) else if j = 54 then (eval% row 54) else if j = 55 then (eval% row 55) else (eval% row 56)
            else
              if j < 59 then
                if j = 57 then (eval% row 57) else (eval% row 58)
              else
                if j = 59 then (eval% row 59) else if j = 60 then (eval% row 60) else (eval% row 61)
          else
            if j < 66 then
              if j = 62 then (eval% row 62) else if j = 63 then (eval% row 63) else if j = 64 then (eval% row 64) else (eval% row 65)
            else
              if j < 68 then
                if j = 66 then (eval% row 66) else (eval% row 67)
              else
                if j = 68 then (eval% row 68) else if j = 69 then (eval% row 69) else (eval% row 70)
    else
      if j < 107 then
        if j < 89 then
          if j < 80 then
            if j < 75 then
              if j = 71 then (eval% row 71) else if j = 72 then (eval% row 72) else if j = 73 then (eval% row 73) else (eval% row 74)
            else
              if j < 77 then
                if j = 75 then (eval% row 75) else (eval% row 76)
              else
                if j = 77 then (eval% row 77) else if j = 78 then (eval% row 78) else (eval% row 79)
          else
            if j < 84 then
              if j = 80 then (eval% row 80) else if j = 81 then (eval% row 81) else if j = 82 then (eval% row 82) else (eval% row 83)
            else
              if j < 86 then
                if j = 84 then (eval% row 84) else (eval% row 85)
              else
                if j = 86 then (eval% row 86) else if j = 87 then (eval% row 87) else (eval% row 88)
        else
          if j < 98 then
            if j < 93 then
              if j = 89 then (eval% row 89) else if j = 90 then (eval% row 90) else if j = 91 then (eval% row 91) else (eval% row 92)
            else
              if j < 95 then
                if j = 93 then (eval% row 93) else (eval% row 94)
              else
                if j = 95 then (eval% row 95) else if j = 96 then (eval% row 96) else (eval% row 97)
          else
            if j < 102 then
              if j = 98 then (eval% row 98) else if j = 99 then (eval% row 99) else if j = 100 then (eval% row 100) else (eval% row 101)
            else
              if j < 104 then
                if j = 102 then (eval% row 102) else (eval% row 103)
              else
                if j = 104 then (eval% row 104) else if j = 105 then (eval% row 105) else (eval% row 106)
      else
        if j < 125 then
          if j < 116 then
            if j < 111 then
              if j = 107 then (eval% row 107) else if j = 108 then (eval% row 108) else if j = 109 then (eval% row 109) else (eval% row 110)
            else
              if j < 113 then
                if j = 111 then (eval% row 111) else (eval% row 112)
              else
                if j = 113 then (eval% row 113) else if j = 114 then (eval% row 114) else (eval% row 115)
          else
            if j < 120 then
              if j = 116 then (eval% row 116) else if j = 117 then (eval% row 117) else if j = 118 then (eval% row 118) else (eval% row 119)
            else
              if j < 122 then
                if j = 120 then (eval% row 120) else (eval% row 121)
              else
                if j = 122 then (eval% row 122) else if j = 123 then (eval% row 123) else (eval% row 124)
        else
          if j < 134 then
            if j < 129 then
              if j = 125 then (eval% row 125) else if j = 126 then (eval% row 126) else if j = 127 then (eval% row 127) else (eval% row 128)
            else
              if j < 131 then
                if j = 129 then (eval% row 129) else (eval% row 130)
              else
                if j = 131 then (eval% row 131) else if j = 132 then (eval% row 132) else (eval% row 133)
          else
            if j < 138 then
              if j = 134 then (eval% row 134) else if j = 135 then (eval% row 135) else if j = 136 then (eval% row 136) else (eval% row 137)
            else
              if j < 140 then
                if j = 138 then (eval% row 138) else (eval% row 139)
              else
                if j = 140 then (eval% row 140) else if j = 141 then (eval% row 141) else (eval% row 142)
  else
    if j < 214 then
      if j < 178 then
        if j < 160 then
          if j < 151 then
            if j < 147 then
              if j = 143 then (eval% row 143) else if j = 144 then (eval% row 144) else if j = 145 then (eval% row 145) else (eval% row 146)
            else
              if j = 147 then (eval% row 147) else if j = 148 then (eval% row 148) else if j = 149 then (eval% row 149) else (eval% row 150)
          else
            if j < 155 then
              if j = 151 then (eval% row 151) else if j = 152 then (eval% row 152) else if j = 153 then (eval% row 153) else (eval% row 154)
            else
              if j < 157 then
                if j = 155 then (eval% row 155) else (eval% row 156)
              else
                if j = 157 then (eval% row 157) else if j = 158 then (eval% row 158) else (eval% row 159)
        else
          if j < 169 then
            if j < 164 then
              if j = 160 then (eval% row 160) else if j = 161 then (eval% row 161) else if j = 162 then (eval% row 162) else (eval% row 163)
            else
              if j < 166 then
                if j = 164 then (eval% row 164) else (eval% row 165)
              else
                if j = 166 then (eval% row 166) else if j = 167 then (eval% row 167) else (eval% row 168)
          else
            if j < 173 then
              if j = 169 then (eval% row 169) else if j = 170 then (eval% row 170) else if j = 171 then (eval% row 171) else (eval% row 172)
            else
              if j < 175 then
                if j = 173 then (eval% row 173) else (eval% row 174)
              else
                if j = 175 then (eval% row 175) else if j = 176 then (eval% row 176) else (eval% row 177)
      else
        if j < 196 then
          if j < 187 then
            if j < 182 then
              if j = 178 then (eval% row 178) else if j = 179 then (eval% row 179) else if j = 180 then (eval% row 180) else (eval% row 181)
            else
              if j < 184 then
                if j = 182 then (eval% row 182) else (eval% row 183)
              else
                if j = 184 then (eval% row 184) else if j = 185 then (eval% row 185) else (eval% row 186)
          else
            if j < 191 then
              if j = 187 then (eval% row 187) else if j = 188 then (eval% row 188) else if j = 189 then (eval% row 189) else (eval% row 190)
            else
              if j < 193 then
                if j = 191 then (eval% row 191) else (eval% row 192)
              else
                if j = 193 then (eval% row 193) else if j = 194 then (eval% row 194) else (eval% row 195)
        else
          if j < 205 then
            if j < 200 then
              if j = 196 then (eval% row 196) else if j = 197 then (eval% row 197) else if j = 198 then (eval% row 198) else (eval% row 199)
            else
              if j < 202 then
                if j = 200 then (eval% row 200) else (eval% row 201)
              else
                if j = 202 then (eval% row 202) else if j = 203 then (eval% row 203) else (eval% row 204)
          else
            if j < 209 then
              if j = 205 then (eval% row 205) else if j = 206 then (eval% row 206) else if j = 207 then (eval% row 207) else (eval% row 208)
            else
              if j < 211 then
                if j = 209 then (eval% row 209) else (eval% row 210)
              else
                if j = 211 then (eval% row 211) else if j = 212 then (eval% row 212) else (eval% row 213)
    else
      if j < 250 then
        if j < 232 then
          if j < 223 then
            if j < 218 then
              if j = 214 then (eval% row 214) else if j = 215 then (eval% row 215) else if j = 216 then (eval% row 216) else (eval% row 217)
            else
              if j < 220 then
                if j = 218 then (eval% row 218) else (eval% row 219)
              else
                if j = 220 then (eval% row 220) else if j = 221 then (eval% row 221) else (eval% row 222)
          else
            if j < 227 then
              if j = 223 then (eval% row 223) else if j = 224 then (eval% row 224) else if j = 225 then (eval% row 225) else (eval% row 226)
            else
              if j < 229 then
                if j = 227 then (eval% row 227) else (eval% row 228)
              else
                if j = 229 then (eval% row 229) else if j = 230 then (eval% row 230) else (eval% row 231)
        else
          if j < 241 then
            if j < 236 then
              if j = 232 then (eval% row 232) else if j = 233 then (eval% row 233) else if j = 234 then (eval% row 234) else (eval% row 235)
            else
              if j < 238 then
                if j = 236 then (eval% row 236) else (eval% row 237)
              else
                if j = 238 then (eval% row 238) else if j = 239 then (eval% row 239) else (eval% row 240)
          else
            if j < 245 then
              if j = 241 then (eval% row 241) else if j = 242 then (eval% row 242) else if j = 243 then (eval% row 243) else (eval% row 244)
            else
              if j < 247 then
                if j = 245 then (eval% row 245) else (eval% row 246)
              else
                if j = 247 then (eval% row 247) else if j = 248 then (eval% row 248) else (eval% row 249)
      else
        if j < 268 then
          if j < 259 then
            if j < 254 then
              if j = 250 then (eval% row 250) else if j = 251 then (eval% row 251) else if j = 252 then (eval% row 252) else (eval% row 253)
            else
              if j < 256 then
                if j = 254 then (eval% row 254) else (eval% row 255)
              else
                if j = 256 then (eval% row 256) else if j = 257 then (eval% row 257) else (eval% row 258)
          else
            if j < 263 then
              if j = 259 then (eval% row 259) else if j = 260 then (eval% row 260) else if j = 261 then (eval% row 261) else (eval% row 262)
            else
              if j < 265 then
                if j = 263 then (eval% row 263) else (eval% row 264)
              else
                if j = 265 then (eval% row 265) else if j = 266 then (eval% row 266) else (eval% row 267)
        else
          if j < 277 then
            if j < 272 then
              if j = 268 then (eval% row 268) else if j = 269 then (eval% row 269) else if j = 270 then (eval% row 270) else (eval% row 271)
            else
              if j < 274 then
                if j = 272 then (eval% row 272) else (eval% row 273)
              else
                if j = 274 then (eval% row 274) else if j = 275 then (eval% row 275) else (eval% row 276)
          else
            if j < 281 then
              if j = 277 then (eval% row 277) else if j = 278 then (eval% row 278) else if j = 279 then (eval% row 279) else (eval% row 280)
            else
              if j < 283 then
                if j = 281 then (eval% row 281) else (eval% row 282)
              else
                if j = 283 then (eval% row 283) else if j = 284 then (eval% row 284) else (eval% row 285)

private theorem dataAt_ok (j : ℕ) (hj : j < 286) : dataAt j = row j := by
  have h : (List.range 286).all (fun k => decide (dataAt k = row k)) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp h) j (List.mem_range.mpr hj))

private def entry (k j : ℕ) : ℤ :=
  let common := 2^(285-j) * ((dataAt 285).1 / (dataAt j).1)
  let choose := (dataAt j).1 / ((dataAt k).1 * (dataAt (j-k)).1)
  let odd := (dataAt j).2.1 / (dataAt k).2.1
  (-4 : ℤ)^k * ((common * choose * odd : ℕ) : ℤ)

private theorem entry_spec {k j : ℕ} (hkj : k ≤ j) (hj : j < 286) :
    entry k j = monomialCoefficient 285 j k := by
  simp only [entry, monomialCoefficient, dataAt_ok 285 (by decide), dataAt_ok j hj,
    dataAt_ok k (by omega), dataAt_ok (j-k) (by omega), row]

def fastCoefficient (f : Bool) (k : ℕ) : ℤ :=
  ((List.range (285-k+1)).map fun h =>
    let j := k+h
    let e : ℤ := if f then (-1)^j else 1
    e * (dataAt j).2.2 * entry k j).sum

private def originalCoefficient (f : Bool) (k : ℕ) : ℤ :=
  ((List.range (285-k+1)).map fun h =>
    let j := k+h
    let e : ℤ := if f then (-1)^j else 1
    e * RiemannResearch.Analysis.LamzouriGapKernel285.laguerreCoefficients.getD j 0 * monomialCoefficient 285 j k).sum

private theorem coefficient_eq {k : ℕ} (hk : k < 286) (f : Bool) :
    originalCoefficient f k = fastCoefficient f k := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro h hh
  have hlt := List.mem_range.mp hh
  have hj : k + h < 286 := by omega
  dsimp only
  rw [entry_spec (by omega) hj, dataAt_ok _ hj]
  rfl

private theorem expand_eq (f : Bool) :
    (List.range 286).map (originalCoefficient f) = (List.range 286).map (fastCoefficient f) := by
  apply List.map_congr_left
  intro k hk
  exact coefficient_eq (List.mem_range.mp hk) f

theorem p_source : inputPolynomial = (List.range 286).map (fastCoefficient false) := by
  exact (show inputPolynomial = (List.range 286).map (originalCoefficient false) from rfl).trans
    (expand_eq false)

theorem q_source : fourierPolynomial = (List.range 286).map (fastCoefficient true) := by
  exact (show fourierPolynomial = (List.range 286).map (originalCoefficient true) from rfl).trans
    (expand_eq true)


def cut (i : ℕ) : ℕ := [0, 18, 38, 59, 82, 110, 143, 184, 286].getD i 286

def indices (i : ℕ) : List ℕ :=
  (List.range (cut (i+1) - cut i)).map (cut i + ·)

def expected (f : Bool) (i : ℕ) : List ℤ :=
  ((if f then frequencyData else physicalData).drop (cut i)).take (cut (i+1) - cut i)

def agrees (f : Bool) (i : ℕ) : Prop :=
  (indices i).map (fastCoefficient f) = expected f i

instance (f : Bool) (i : ℕ) : Decidable (agrees f i) := by unfold agrees; infer_instance

theorem assemble (f : Bool) (h₀ : agrees f 0) (h₁ : agrees f 1) (h₂ : agrees f 2)
    (h₃ : agrees f 3) (h₄ : agrees f 4) (h₅ : agrees f 5) (h₆ : agrees f 6) (h₇ : agrees f 7) :
    (List.range 286).map (fastCoefficient f) = if f then frequencyData else physicalData := by
  have h : List.range 286 = indices 0 ++ indices 1 ++ indices 2 ++ indices 3 ++ indices 4 ++
      indices 5 ++ indices 6 ++ indices 7 := by decide +kernel
  rw [h]
  simp only [List.map_append]
  unfold agrees at h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rw [h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇]
  cases f <;> decide +kernel

end RiemannResearch.Analysis.LamzouriGapKernel285.CoefficientTable
