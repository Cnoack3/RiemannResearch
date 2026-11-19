/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierStages

namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence

set_option maxRecDepth 120000
set_option maxHeartbeats 0
private def r181 : List ℤ := eval% propose 180 (checkpoint 5)
private def r182 : List ℤ := eval% propose 181 r181
private def r183 : List ℤ := eval% propose 182 r182
private def r184 : List ℤ := eval% propose 183 r183
private def r185 : List ℤ := eval% propose 184 r184
private def r186 : List ℤ := eval% propose 185 r185
private def r187 : List ℤ := eval% propose 186 r186
private def r188 : List ℤ := eval% propose 187 r187
private def r189 : List ℤ := eval% propose 188 r188
private def r190 : List ℤ := eval% propose 189 r189
private def r191 : List ℤ := eval% propose 190 r190
private def r192 : List ℤ := eval% propose 191 r191
private def r193 : List ℤ := eval% propose 192 r192
private def r194 : List ℤ := eval% propose 193 r193
private def r195 : List ℤ := eval% propose 194 r194
private def r196 : List ℤ := eval% propose 195 r195
private def r197 : List ℤ := eval% propose 196 r196
private def r198 : List ℤ := eval% propose 197 r197
private def r199 : List ℤ := eval% propose 198 r198
private def r200 : List ℤ := eval% propose 199 r199
private def r201 : List ℤ := eval% propose 200 r200
private def r202 : List ℤ := eval% propose 201 r201
private def r203 : List ℤ := eval% propose 202 r202
private def r204 : List ℤ := eval% propose 203 r203
private def r205 : List ℤ := eval% propose 204 r204
private def r206 : List ℤ := eval% propose 205 r205
private def r207 : List ℤ := eval% propose 206 r206
private def r208 : List ℤ := eval% propose 207 r207
private def r209 : List ℤ := eval% propose 208 r208
private def r210 : List ℤ := eval% propose 209 r209
private def r211 : List ℤ := eval% propose 210 r210
private def r212 : List ℤ := eval% propose 211 r211
private def r213 : List ℤ := eval% propose 212 r212
private def r214 : List ℤ := eval% propose 213 r213
private def r215 : List ℤ := eval% propose 214 r214

private def next180 := oneStep 180 (checkpoint 5) r181 (by decide +kernel)
private def next181 := oneStep 181 r181 r182 (by decide +kernel)
private def next182 := oneStep 182 r182 r183 (by decide +kernel)
private def next183 := oneStep 183 r183 r184 (by decide +kernel)
private def next184 := oneStep 184 r184 r185 (by decide +kernel)
private def next185 := oneStep 185 r185 r186 (by decide +kernel)
private def next186 := oneStep 186 r186 r187 (by decide +kernel)
private def next187 := oneStep 187 r187 r188 (by decide +kernel)
private def next188 := oneStep 188 r188 r189 (by decide +kernel)
private def next189 := oneStep 189 r189 r190 (by decide +kernel)
private def next190 := oneStep 190 r190 r191 (by decide +kernel)
private def next191 := oneStep 191 r191 r192 (by decide +kernel)
private def next192 := oneStep 192 r192 r193 (by decide +kernel)
private def next193 := oneStep 193 r193 r194 (by decide +kernel)
private def next194 := oneStep 194 r194 r195 (by decide +kernel)
private def next195 := oneStep 195 r195 r196 (by decide +kernel)
private def next196 := oneStep 196 r196 r197 (by decide +kernel)
private def next197 := oneStep 197 r197 r198 (by decide +kernel)
private def next198 := oneStep 198 r198 r199 (by decide +kernel)
private def next199 := oneStep 199 r199 r200 (by decide +kernel)
private def next200 := oneStep 200 r200 r201 (by decide +kernel)
private def next201 := oneStep 201 r201 r202 (by decide +kernel)
private def next202 := oneStep 202 r202 r203 (by decide +kernel)
private def next203 := oneStep 203 r203 r204 (by decide +kernel)
private def next204 := oneStep 204 r204 r205 (by decide +kernel)
private def next205 := oneStep 205 r205 r206 (by decide +kernel)
private def next206 := oneStep 206 r206 r207 (by decide +kernel)
private def next207 := oneStep 207 r207 r208 (by decide +kernel)
private def next208 := oneStep 208 r208 r209 (by decide +kernel)
private def next209 := oneStep 209 r209 r210 (by decide +kernel)
private def next210 := oneStep 210 r210 r211 (by decide +kernel)
private def next211 := oneStep 211 r211 r212 (by decide +kernel)
private def next212 := oneStep 212 r212 r213 (by decide +kernel)
private def next213 := oneStep 213 r213 r214 (by decide +kernel)
private def next214 := oneStep 214 r214 r215 (by decide +kernel)
private def next215 := oneStep 215 r215 (checkpoint 6) (by decide +kernel)

theorem checked5 : Step 5 := by
  intro h
  have h181 := next180 h
  have h182 := next181 h181
  have h183 := next182 h182
  have h184 := next183 h183
  have h185 := next184 h184
  have h186 := next185 h185
  have h187 := next186 h186
  have h188 := next187 h187
  have h189 := next188 h188
  have h190 := next189 h189
  have h191 := next190 h190
  have h192 := next191 h191
  have h193 := next192 h192
  have h194 := next193 h193
  have h195 := next194 h194
  have h196 := next195 h195
  have h197 := next196 h196
  have h198 := next197 h197
  have h199 := next198 h198
  have h200 := next199 h199
  have h201 := next200 h200
  have h202 := next201 h201
  have h203 := next202 h202
  have h204 := next203 h203
  have h205 := next204 h204
  have h206 := next205 h205
  have h207 := next206 h206
  have h208 := next207 h207
  have h209 := next208 h208
  have h210 := next209 h209
  have h211 := next210 h210
  have h212 := next211 h211
  have h213 := next212 h212
  have h214 := next213 h213
  have h215 := next214 h214
  have h216 := next215 h215
  exact h216

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
