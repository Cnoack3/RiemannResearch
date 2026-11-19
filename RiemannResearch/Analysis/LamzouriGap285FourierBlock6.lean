/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierStages

namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence

set_option maxRecDepth 120000
set_option maxHeartbeats 0
private def r217 : List ℤ := eval% propose 216 (checkpoint 6)
private def r218 : List ℤ := eval% propose 217 r217
private def r219 : List ℤ := eval% propose 218 r218
private def r220 : List ℤ := eval% propose 219 r219
private def r221 : List ℤ := eval% propose 220 r220
private def r222 : List ℤ := eval% propose 221 r221
private def r223 : List ℤ := eval% propose 222 r222
private def r224 : List ℤ := eval% propose 223 r223
private def r225 : List ℤ := eval% propose 224 r224
private def r226 : List ℤ := eval% propose 225 r225
private def r227 : List ℤ := eval% propose 226 r226
private def r228 : List ℤ := eval% propose 227 r227
private def r229 : List ℤ := eval% propose 228 r228
private def r230 : List ℤ := eval% propose 229 r229
private def r231 : List ℤ := eval% propose 230 r230
private def r232 : List ℤ := eval% propose 231 r231
private def r233 : List ℤ := eval% propose 232 r232
private def r234 : List ℤ := eval% propose 233 r233
private def r235 : List ℤ := eval% propose 234 r234
private def r236 : List ℤ := eval% propose 235 r235
private def r237 : List ℤ := eval% propose 236 r236
private def r238 : List ℤ := eval% propose 237 r237
private def r239 : List ℤ := eval% propose 238 r238
private def r240 : List ℤ := eval% propose 239 r239
private def r241 : List ℤ := eval% propose 240 r240
private def r242 : List ℤ := eval% propose 241 r241
private def r243 : List ℤ := eval% propose 242 r242
private def r244 : List ℤ := eval% propose 243 r243
private def r245 : List ℤ := eval% propose 244 r244
private def r246 : List ℤ := eval% propose 245 r245
private def r247 : List ℤ := eval% propose 246 r246
private def r248 : List ℤ := eval% propose 247 r247
private def r249 : List ℤ := eval% propose 248 r248
private def r250 : List ℤ := eval% propose 249 r249
private def r251 : List ℤ := eval% propose 250 r250

private def next216 := oneStep 216 (checkpoint 6) r217 (by decide +kernel)
private def next217 := oneStep 217 r217 r218 (by decide +kernel)
private def next218 := oneStep 218 r218 r219 (by decide +kernel)
private def next219 := oneStep 219 r219 r220 (by decide +kernel)
private def next220 := oneStep 220 r220 r221 (by decide +kernel)
private def next221 := oneStep 221 r221 r222 (by decide +kernel)
private def next222 := oneStep 222 r222 r223 (by decide +kernel)
private def next223 := oneStep 223 r223 r224 (by decide +kernel)
private def next224 := oneStep 224 r224 r225 (by decide +kernel)
private def next225 := oneStep 225 r225 r226 (by decide +kernel)
private def next226 := oneStep 226 r226 r227 (by decide +kernel)
private def next227 := oneStep 227 r227 r228 (by decide +kernel)
private def next228 := oneStep 228 r228 r229 (by decide +kernel)
private def next229 := oneStep 229 r229 r230 (by decide +kernel)
private def next230 := oneStep 230 r230 r231 (by decide +kernel)
private def next231 := oneStep 231 r231 r232 (by decide +kernel)
private def next232 := oneStep 232 r232 r233 (by decide +kernel)
private def next233 := oneStep 233 r233 r234 (by decide +kernel)
private def next234 := oneStep 234 r234 r235 (by decide +kernel)
private def next235 := oneStep 235 r235 r236 (by decide +kernel)
private def next236 := oneStep 236 r236 r237 (by decide +kernel)
private def next237 := oneStep 237 r237 r238 (by decide +kernel)
private def next238 := oneStep 238 r238 r239 (by decide +kernel)
private def next239 := oneStep 239 r239 r240 (by decide +kernel)
private def next240 := oneStep 240 r240 r241 (by decide +kernel)
private def next241 := oneStep 241 r241 r242 (by decide +kernel)
private def next242 := oneStep 242 r242 r243 (by decide +kernel)
private def next243 := oneStep 243 r243 r244 (by decide +kernel)
private def next244 := oneStep 244 r244 r245 (by decide +kernel)
private def next245 := oneStep 245 r245 r246 (by decide +kernel)
private def next246 := oneStep 246 r246 r247 (by decide +kernel)
private def next247 := oneStep 247 r247 r248 (by decide +kernel)
private def next248 := oneStep 248 r248 r249 (by decide +kernel)
private def next249 := oneStep 249 r249 r250 (by decide +kernel)
private def next250 := oneStep 250 r250 r251 (by decide +kernel)
private def next251 := oneStep 251 r251 (checkpoint 7) (by decide +kernel)

theorem checked6 : Step 6 := by
  intro h
  have h217 := next216 h
  have h218 := next217 h217
  have h219 := next218 h218
  have h220 := next219 h219
  have h221 := next220 h220
  have h222 := next221 h221
  have h223 := next222 h222
  have h224 := next223 h223
  have h225 := next224 h224
  have h226 := next225 h225
  have h227 := next226 h226
  have h228 := next227 h227
  have h229 := next228 h228
  have h230 := next229 h229
  have h231 := next230 h230
  have h232 := next231 h231
  have h233 := next232 h232
  have h234 := next233 h233
  have h235 := next234 h234
  have h236 := next235 h235
  have h237 := next236 h236
  have h238 := next237 h237
  have h239 := next238 h238
  have h240 := next239 h239
  have h241 := next240 h240
  have h242 := next241 h241
  have h243 := next242 h242
  have h244 := next243 h243
  have h245 := next244 h244
  have h246 := next245 h245
  have h247 := next246 h246
  have h248 := next247 h247
  have h249 := next248 h248
  have h250 := next249 h249
  have h251 := next250 h250
  have h252 := next251 h251
  exact h252

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
