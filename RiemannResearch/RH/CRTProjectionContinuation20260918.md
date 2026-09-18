# Signed projection gains, a dyadic obstruction, and the remaining CRT bound

Christian Noack — RiemannResearch — September 18, 2026

This mathematical continuation starts from `RH_Exact_CRT_Energy_Mean_Repair_2026-09-18(1).md`. The strongest new obstruction is unconditional: **exact-head witnesses assembled solely from dyadic square-wave pulses have energy at least a positive constant times the head length.** The full correction dictionary is larger. Its subpolynomial optimum, and consequently RH, remain unproved. The accompanying Lean verification ledger determines which statements below have been kernel checked; statements explicitly marked supplementary are written mathematics only.

## 1. Actual energy and signed projection

For positive integers, write
\[
q_t=\frac2{(t+1)(t+2)},\qquad x_F(t)=\frac1t\sum_{n=1}^tF(n),\qquad
E(F)=\sum_{t\ge1}q_tx_F(t)^2.
\]
The exact signed correlation is
\[
\langle F,R\rangle_C=\sum_{t\ge1}q_tx_F(t)x_R(t).
\]
For a nonzero direction in this norm, set \(h=\langle F,R\rangle_C\) and \(g=E(R)>0\). Then
\[
E(F+uR)=E(F)+2uh+u^2g
=E(F)-\frac{h^2}{g}+g\left(u+\frac hg\right)^2.
\]
The gain is exactly \(h^2/g\). For two directions with energies \(a,b\), mutual correlation \(c\), and residual correlations \(h,k\), suppose \(a>0\) and \(d=b-c^2/a>0\). Completing the two squares gives the exact gain
\[
\boxed{\frac{h^2}{a}+\frac{(k-ch/a)^2}{b-c^2/a}.}
\]
The mutual correlation is retained in both numerator and denominator. These identities determine an optimum once the actual correlations are known; they do not give a growing lower bound on that optimum.

## 2. The dyadic pulse dictionary has a linear obstruction

Let
\[
H_A(n)=2\{n/(2A)\}-\{n/A\}.
\]
Its finite linear span is the one-seed space obtained by all positive integer dilations of the residue modulo two. Here “dyadic” refers to the pulse shape; the scale \(A\) is any positive integer.

Fix
\[
s=1+\frac{2\pi i}{\log2},\qquad b_s(t)=t^{-s},\qquad
a_s(t)=t\bigl[b_s(t)-2b_s(t+1)+b_s(t+2)\bigr].
\]
For bounded real \(F\), define the complex linear sensor
\[
\Lambda_s(F)=\sum_{t\ge1}a_s(t)x_F(t).
\]
Summation by parts, including its vanishing terminal term, gives
\[
\Lambda_s(F)=\sum_{n\ge1}F(n)\bigl[b_s(n)-b_s(n+1)\bigr].
\]
Both series converge absolutely. Summing over the on-blocks of \(H_A\) gives
\[
\Lambda_s(H_A)=A^{-s}\sum_{j\ge1}\bigl[(2j-1)^{-s}-(2j)^{-s}\bigr]=0.
\]
The last equality does not assume any zeta zero. Indeed, since \(2^{1-s}=1\), the first \(N\) paired terms equal \(\sum_{N<n\le2N}n^{-s}\). Its integral over \([N,2N]\) is zero, and the sum-minus-integral error tends to zero. Thus every finite pulse sum is annihilated.

If \(F(n)=1\) for \(1\le n\le Y\), the exact prefix mass is
\[
K_s(Y)=\sum_{t=1}^Ya_s(t)
=1-(Y+1)b_s(Y+1)+Yb_s(Y+2),
\qquad |K_s(Y)-1|\le\frac{1+|s|}{Y+1}.
\]
Define the actual dual tail
\[
D_s(Y)=\sum_{t>Y}\frac{|a_s(t)|^2}{q_t}>0.
\]
The integral formula for a second difference gives
\[
|a_s(t)|\le|s(s+1)|t^{-2},\qquad
D_s(Y)\le\frac{3|s(s+1)|^2}{Y}.
\]
For a pulse sum, exact head-tail cancellation followed by weighted Cauchy–Schwarz yields
\[
\boxed{E(F)\ge\frac{Y}{Y+2}+\frac{|K_s(Y)|^2}{D_s(Y)}.}
\]
In particular, once \(Y+1\ge2(1+|s|)\),
\[
\boxed{E(F)\ge\frac{Y}{Y+2}+\frac{Y}{12|s(s+1)|^2}.}
\]
This rules out subpolynomial energy for exact-head witnesses lying entirely in the pulse span. The verified Lean theorem derives the polynomial, hence linear, lower bound from the existing exact Cesàro–Mellin pairing and dual-tail bounds. The explicit threshold and the additional head-mass term displayed here are supplementary refinements unless separately recorded in its verification ledger.

**Scope for corrections.** If \(F\) is an unrestricted legal witness and \(R\) is a pulse correction, then \(\Lambda_s(F+R)=\Lambda_s(F)\), which need not be zero. The correct bound is
\[
\boxed{E(F+R)\ge\frac{Y}{Y+2}
+\frac{|\Lambda_s(F)-K_s(Y)|^2}{D_s(Y)}}
\]
when \(F+R\) has the exact head. Thus the pulse-only obstruction does not invalidate arbitrary legal witnesses corrected by pulses. It identifies a sensor that those corrections cannot change.

## 3. Triadic directions remove the artificial common zero

Define the triadic pulse
\[
T_A=3g_{3A}-g_A.
\]
It vanishes before \(A\), has mean one, and obeys the exact compatibility identity
\[
\boxed{2T_{2A}-T_A=3H_{3A}-H_A.}
\]
For \(A>Y\), with \(D=Y+1\) and the handoff's complete correction dictionary,
\[
\boxed{T_A-2H_D=3\Psi_{Y,3A}-\Psi_{Y,A}.}
\]
Consequently the triadic direction is available inside the genuine mean-zero, exact-head correction space.

The two pulse sensors are exactly
\[
\Lambda_z(H_A)=A^{-z}(1-2^{1-z})\zeta(z),\qquad
\Lambda_z(T_A)=A^{-z}(1-3^{1-z})\zeta(z),
\]
for \(\Re z>1/2\), away from \(z=1\). The products have removable values \((\log2)/A\) and \((\log3)/A\) there. The two artificial factors have no common zero other than one: a second common zero would imply a nontrivial integer relation between \(\log2\) and \(\log3\), contradicting unique factorization. Away from the pole at one, their common zeros are therefore exactly the actual zeta zeros; at one the completed pulse transforms are nonzero. This common-zero theorem is already present in the project.

Supplementary exact repair of one sensor: at the above dyadic resonance, assume \(\zeta(s)\ne0\). Put \(R_1=T_A-2H_D\), \(R_2=T_{3A}-2H_D\), and \(z=\delta/\Lambda_s(R_1)\). Since \(\operatorname{Im}(3^{-s})\ne0\), the real coefficients
\[
v=\frac{\operatorname{Im}z}{\operatorname{Im}(3^{-s})},\qquad
u=\operatorname{Re}z-v\operatorname{Re}(3^{-s})
\]
satisfy \(\Lambda_s(uR_1+vR_2)=\delta\). This adjusts one artificial sensor exactly. Its energy is still the full signed two-direction quadratic; neither a small energy cost nor simultaneous control of all sensors follows.

## 4. Far pulses have little gain on a fixed mean-zero residual

**Supplementary mathematics; this proof uses only the elementary pulse bound.**

For a fixed periodic \(F\), write
\[
x_F(t)=m+B_F(t)/t,\qquad \beta=\sup_t|B_F(t)|<\infty.
\]
Set \(J_A=\sum_tq_tx_{H_A}(t)\). Because \(0\le x_{H_A}\le1\) and it vanishes before \(A\),
\[
0\le J_A\le\frac2{A+1},\qquad
\langle F,H_A\rangle_C=mJ_A+r_A,
\quad r_A=\sum_{t\ge A}q_t\frac{B_F(t)}t x_{H_A}(t),
\]
with
\[
|r_A|\le\frac{\beta J_A}{A}\le\frac{2\beta}{A(A+1)}.
\]
This is an exact signed decomposition before estimating the isolated remainder.

On \(2A\le t\le3A-1\), the cumulative pulse count is exactly \(A\), so \(x_{H_A}(t)\ge1/3\). Summing just this block gives
\[
E(H_A)\ge\frac19\left(\frac2{2A+1}-\frac2{3A+1}\right)
\ge\frac1{54A}.
\]
Therefore, if \(m=0\), the optimal one-pulse gain satisfies
\[
\boxed{\frac{\langle F,H_A\rangle_C^2}{E(H_A)}
\le\frac{216\beta^2}{A(A+1)^2}.}
\]
There is also a bound independent of the number of delayed directions. Any finite-energy correction \(R\) vanishing before \(A\) leaves the conditional means unchanged for \(t<A\). For \(A\ge2\) and mean-zero \(F\),
\[
\boxed{E(F)-E(F+R)\le\sum_{t\ge A}q_tx_F(t)^2
\le\frac{2\beta^2}{3(A-1)^3}.}
\]
The last estimate uses \(q_t\le2/t^2\) and the integral comparison for \(\sum_{t\ge A}t^{-4}\). Thus arbitrarily many very distant pulses cannot recover more than the residual's existing tail energy. These are fixed-witness results: no uniform bound on \(\beta_Y\) for the growing arithmetic residual has been proved.

## 5. The remaining arithmetic target

Mean repair and exact projection do not supply the missing estimate
\[
\forall\varepsilon>0\quad
\inf_{c\text{ finite}}E\left(F_Y+\sum_{d>Y}c_d\Psi_{Y,d}\right)
\le C_\varepsilon Y^\varepsilon
\]
eventually or along a cofinal sequence. All finite signed correlations and the ordered CRT weights must remain present. The dyadic obstruction justifies adding genuinely different directions, including triadic ones; removing artificial common zeros alone does not establish the required signed Schur gain.

For the canonical one-anchor witness, the invariant seen by dyadic corrections is explicitly
\[
\Lambda_s(G_Y)=\zeta(s)\left[
\sum_{d\le Y}\frac{\mu(d)}{d^s}-(Y+1)^{1-s}\sum_{d\le Y}\frac{\mu(d)}d
\right].
\]
The original mean cancellation does not change this value. Subpolynomial energy after dyadic-only corrections would require this quantity to approach one at rate \(O_{s,\varepsilon}(Y^{-1/2+\varepsilon})\). That cancellation is not supplied by the mean-repair argument. The unrestricted dictionary can change these artificial sensor values, but its uniform arithmetic energy bound remains the genuine open step.

## 6. Formal verification coverage

This continuation adds 46 proved theorem declarations across three modules.
Standalone verification returned `exit_code: 0` and `verified: true` for
each coherent candidate. Principal axiom audits returned only
`propext`, `Classical.choice`, and `Quot.sound`. No custom RH axiom or
proof placeholder is introduced.

- **ConditionalMeanSignedProjection.lean (24 theorems):** actual signed
  infinite correlation and its summability, bilinearity, complete scalar
  square identity, head-preserving scalar improvement, screened energy and
  source, zero source for a zero-energy direction, and the exact full
  two-direction Schur gain. The Schur theorem includes the singular screened
  branch: the screened energy and source are both zero, so its extra gain
  is zero. Both scalar and Schur subpolynomial endpoints conclude mathlib's
  `RiemannHypothesis` only from the explicitly supplied open growth bound.
- **CRTDelayedProjection.lean (8 theorems):** strictly positive pulse
  energy; actual mean-zero witnesses arbitrarily close to the complete
  scalar projection gain; an explicit delayed two-pulse witness with fixed
  optimal coefficient; and legal, head-vanishing triadic pulses together
  with their exact correction-dictionary and dyadic/triadic compatibility
  identities.
- **ConditionalSeedFactorObstruction.lean (14 theorems):** seed-factor
  annihilation of the actual Mellin and Cesàro pairings, its quantitative
  polynomial obstruction, a fixed nonreal dyadic resonance with real part
  one, a positive linear lower-bound constant, membership of every
  delayed pulse in the dyadic seed span, and
  `not_subpolynomial_dyadic_heads`.

The handoff's original 54 declarations remain available. They are not counted
as new results here. The present count includes conditional implications;
their theorem types do not discharge their domain-specific hypotheses.

**Supplementary written mathematics:** the explicit threshold and additional
head-mass term in Section 2, the affine invariant formulation and anchored
Möbius formula, the two-real-coefficient sensor repair in Section 3, and the
far-pulse decay estimates in Section 4 have not been newly formalized here.
The ternary pulse's stated mean one is elementary written mathematics; the
new verified endpoints for it are the legality, zero head, and exact finite
identities listed above.

**Remaining mathematical obligation:** prove subpolynomial control of the
actual full correction optimum, or supply a sufficiently large signed
residual-specific Schur gain. A uniform lower bound on a formal quadratic,
absence of artificial dyadic resonances, or an axiom audit does not supply
that bound. RH is not proved by this continuation.

The project exports all three modules and records these established results
and conditional reductions in the theorem catalog. Final affected-module
checkpoint validation and publication are reported separately by the
coordinating run; consult the commit history for the published revision.
