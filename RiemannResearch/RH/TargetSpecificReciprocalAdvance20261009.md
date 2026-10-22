# Target-specific squarefree reciprocal rows and permanent compression obstruction

Research continuation, 9 October 2026 UTC (8 October locally).
Starting published head: `9df57d2bcdac5275175ccd9918c3a28f799f36cc`.

## Scope and result

The recovered prompt is §7 of `CriticalZeroMeanOneAdvance20261008.md`,
continued through the actual signed-correction target in
`RadicalDualAdvance20261008.md`. Mathematics was developed first, reviewed
independently, and checked symbolically with Wolfram before Lean verification.

The established structural results are:

- A first-moment cap applying to **every** vector in a squarefree-stage
  orthogonal complement is at least `1/3`, at every integer stage.
  The corresponding compressed-square cap is at least `1/9`.
  Thus enlarging head-recovery certificates cannot force these universal
  caps to zero, even if RH is true.
- Reciprocal differences need vanish only at squarefree base sites.
  Combined with radical jump invariance they force the exact linear form
  `x(n)=n*x(1)`; inverse-square summability forces `x=0`.
- For the actual target projection residuals, squarefree closure is exactly
  equivalent to all fixed squarefree reciprocal base differences tending
  to zero. A cofinal consumer requires no division by the moving error.
- Finite stability controls both coordinate and jump errors by a finite
  bound on those squarefree base differences.

These results do not prove the required arithmetic row decay, the existing
positive signed-correction decay, or RH.

## Lean coverage

`Analysis/RadicalDifferenceTotality.lean` adds the base-only linear
rigidity theorem, its decay and summability consequences, and
`finite_rigidity_of_squarefree_quotient_bound`.

`RH/ZetaTwoRadicalRowCriterion.lean` proves the actual stage-span inclusion,
radical invariance of the actual residual and its strong limit, base-only
zero detection, and the exact closure criterion
`mem_closure_iff_squarefree_reciprocal_differences`.
The cofinal theorem has exactly the infinitely quantified base-decay input,
not a finite list of measurements.

`RH/ZetaTwoReciprocalObstruction.lean` constructs the literal four-site dual
in the existing QHilbert realization, proves its norm, reciprocal energy,
target orthogonality, and orthogonality to every actual squarefree stage.
It proves the first- and second-moment cap obstructions and keeps the exact
signed reciprocal pairing through the full orthogonal projection.

`RH/ZetaTwoParetoTransfer.lean` specializes the cofinal base-row consumer
to the existing Mellin RH implication.

Twenty-five new public structural declarations passed coherent source-body
checks (job_iEpPjxjlvpogGQNEASeJr4KihIlClKAN, exit 0); every displayed axiom
audit used only standard foundations. The twenty-sixth declaration is the
RH consumer assembled in ZetaTwoParetoTransfer. Native affected-module
validation is the publication checkpoint gate. Axiom audits allow only `propext`,
`Classical.choice`, and `Quot.sound`. No computation output is a proof input.
The analytic Bagchi converse, gradient-energy assembly, high-power-row estimate,
and physical trigamma error-certificate assembly below are paper results;
they are not counted as newly kernel-verified applications here.

## 1. Why a universal reciprocal cap cannot vanish

Put `Z=ζ(2)`, `Q(k)=1/(Z k²)`, `D x(k)=x(k)/k`,
and let `V_n` be the actual cumulative squarefree stage. The stage index
`n` contains conductors through `n+1`. Let
`K_n=P_(V_n⊥) D|_(V_n⊥)`.

The four-site vector `f4=(1,-4,-9,16)` has exactly

\[
\|f_4\|_Q^2=30/Z,\qquad
\langle f_4,Df_4\rangle_Q=10/Z,\qquad
\langle f_4,1\rangle_Q=0.
\]

For a squarefree conductor `d`, its full pairing is
\[
Z\langle f_4,g_d\rangle_Q
=g_d(4)-g_d(3)-g_d(2)+g_d(1)
=\mathbf1_{d\mid2}-\mathbf1_{d\mid4}=0.
\]
Thus `f4∈V_n⊥` for **every** `n`, and the full screening identity is
\[
\langle f_4,K_n f_4\rangle_Q=10/Z.
\]
Testing any universal first-moment cap gives `τ_n≥1/3`.
Cauchy--Schwarz gives the complete compressed-square lower bound
\[
\|K_n f_4\|_Q^2\ge\frac19\|f_4\|_Q^2,
\]
so a universal second-moment cap is at least `1/9`.

The actual residual `r_n=1-P_(V_n)1` is orthogonal to `f4`.
Consequently this obstruction does not imply that its moment is bounded
away from zero. Its reciprocal image still has an exact signed pairing:
\[
\langle f_4,K_n r_n\rangle_Q=\langle f_4,D r_n\rangle_Q,\qquad
|\langle f_4,D r_n\rangle_Q|^2
\le\frac{30}{Z}\|K_n r_n\|_Q^2.
\]
Target-specific cancellation is therefore indispensable. A cap restricted
to a subspace known only after assuming target closure cannot discharge RH.

### Sharper two-dual paper obstruction, with complete remainder

For `f9=(4,-9,-64,81)` at sites `2,3,8,9`,
the exact raw matrices already in `ZetaTwoDualBlock.lean` are
\[
G=\begin{pmatrix}30&5\\5&158\end{pmatrix},\qquad
H=\begin{pmatrix}10&1\\1&22\end{pmatrix}.
\]
The same residue-jump proof puts both duals in every `V_n⊥`.
Wolfram independently checked
\[
\det(H-\lambda G)=4715\lambda^2-2230\lambda+219.
\]
Hence the paper bound is
\[
\|K_n\|\ge\lambda_+
=\frac{1115+4\sqrt{13165}}{4715}>\frac13.
\]
The rational witness `46f4-f9` gives
\[
Z\|46f_4-f_9\|^2=63178,\quad
Z\langle46f_4-f_9,D(46f_4-f_9)\rangle=21090,
\quad \|K_n\|\ge10545/31589.
\]
These sharper all-stage operator specializations are paper proofs; the
new bundled Lean obstruction uses the single literal dual.

Write `F=span(f4,f9)`, `e_n=‖r_n‖_Q²`, and
`b_i=Z⟨f_i,D r_n⟩_Q`. The exact target decomposition is
\[
e_n m_2(n)=
\frac{158b_4^2-10b_4b_9+30b_9^2}{4715Z}
+\|P_{(V_n\oplus F)^\perp}D r_n\|_Q^2.
\]
The negative cross term and the complete positive remainder are retained.
A finite dual estimate does not control that entire remainder.

## 2. Paper proof of the target-specific route


Paper development, 9 October 2026. These results concern the actual physical
inverse-square space, not a finite numerical surrogate. Its formal coverage is specified above.

Put `Z = zeta(2)`, `Q(n)=1/(Z n^2)` for `n>=1`, and extend sequences by zero
at site zero. Let `D x(n)=x(n)/n` and `B_a(x)=D x(a)-D x(a-1)`. Write
`M={x : Delta x(n)=Delta x(rad n) for every n>=2}`. Every squarefree legal
atom, every actual target residual, and their strong limits lie in `M`.

### Algebraic rigidity from squarefree base sites only

**Theorem.** If `x(0)=0`, `x` obeys the radical jump relation, and
`B_a(x)=0` for every squarefree `a>=2`, then

\[
x(n)=n x(1) \quad(n\ge0).
\]

Proof by strong induction. The cases zero and one are immediate. If
`n>=2` is squarefree, `B_n=0` gives
`x(n)=n x(n-1)/(n-1)=n x(1)`. Otherwise `a=rad n<n` (the radical is
squarefree and divides `n`). The previously established formulas at `a`
and `a-1` give `Delta x(a)=x(1)`, and radical invariance gives
`x(n)=x(n-1)+x(1)=n x(1)`.

If additionally `x(n)/n -> 0`, or `sum |x(n)/n|^2<infinity`, then
`x(1)=0` and `x=0`. Thus reciprocal constraints at nonsquarefree sites are
unnecessary in the common-kernel theorem.

### Actual projection residual criteria

Let `r_N=1-P_{C_N}1`, with cumulative squarefree legal spaces tending to
`C`. Standard Hilbert projection convergence gives `r_N -> r_infty`
strongly, `r_infty in M`, `||r_N||<=1`, and
`e_N=||r_N||^2=<r_N,1>`. The approximation criterion yields

\[
\mathrm{RH}\iff \forall\ a\ge2\text{ squarefree},\ B_a(r_N)\to0.
\]

Indeed each base functional is continuous, so the right side sets all
base functionals of `r_infty` to zero, and the rigidity theorem kills it.
The reverse direction follows from norm convergence to zero.

For the existing full signed radical row
`L_m(x)=Delta(Dx)(m)-Delta(Dx)(rad m)`, the exact recovery identity gives,
for fixed squarefree `a>=2` and `m=a^j`,

\[
L_{a^j}(r_N)+B_a(r_N)
 =\frac{\Delta r_N(a)-r_N(a^j)/a^j}{a^j-1}.
\]

The full norm coordinate bounds imply

\[
\left|L_{a^j}(r_N)+B_a(r_N)\right|
\le\frac{2a\sqrt Z}{a^j-1},
\]

uniformly in `N`. Hence for **any** integer sequence `j_N -> infinity`,
RH is also equivalent to `L_{a^{j_N}}(r_N)->0` for every fixed squarefree
base `a`. This tests one moving row per base and never divides by the
growing sparse dual-vector norm.

### A bounded unweighted gradient energy

Define

\[
\mathcal E_{\mathrm{sf}}(x)=\frac1Z
 \sum_{\substack{a\ge2\\a\ \mathrm{squarefree}}}
 \left|\frac{x(a)}a-\frac{x(a-1)}{a-1}\right|^2.
\]

The full difference operator on `ell^2` has norm at most two, so
`0<=E_sf(x)<=4||x||_Q^2`. Its square root is a continuous seminorm.
Rigidity proves `E_sf(x)=0` and `x in M` imply `x=0`. Strong convergence of
the actual residuals therefore gives the exact consumer

\[
\mathrm{RH}\iff\mathcal E_{\mathrm{sf}}(r_N)\longrightarrow0.
\]

No unconditional decay of these actual energies is established here.

### Quantitative finite-head certificate with the complete tail

Assume `x in M`, `||x||_Q=R`, `J>=2`, and

\[
\varepsilon=\max_{\substack{2\le a\le J\\a\ \mathrm{squarefree}}}
|B_a(x)|.
\]

Simultaneous strong induction, writing `c=x(1)`, gives

\[
|x(n)-nc|\le n(n-1)\varepsilon,\qquad
|\Delta x(n)-c|\le2(n-1)\varepsilon
\quad(1\le n\le J).
\]

At a squarefree `n`, the exact identity is
`Delta(x-nc)(n)=(x(n-1)-(n-1)c)/(n-1)+n B_n(x)`.
At a nonsquarefree `n`, the jump error is copied from `rad n<n`.
These identities supply both inductive inequalities without discarding
the arithmetic wrap term.

Averaging normalized coordinates and applying finite Cauchy gives

\[
|c|\le \sqrt{Z/J}\,R+\frac{J-1}{2}\varepsilon.
\]

For an actual projection residual `x=r_N`, `R=sqrt(e_N)` and
`e_N=<r_N,1>`. Splitting this exact pairing at `J` gives

\[
e_N\le A_J\sqrt{e_N}+B_J\varepsilon_N(J),
\]

where `H_J=sum_{n=1}^J 1/n` and

\[
A_J=\frac{H_J}{\sqrt{ZJ}}
 +\sqrt{\frac1Z\sum_{n>J}\frac1{n^2}},
\qquad
B_J=\frac{\frac{J-3}{2}H_J+J}{Z}.
\]

The tail is complete: it is equally
`sqrt(polygamma(1,J+1)/Z)`. The convenient upper bound
`A_J <= (H_J+1)/sqrt(ZJ)` follows from the full integral bound for the
positive inverse-square tail. Consequently

\[
\sqrt{e_N}\le
\frac{A_J+\sqrt{A_J^2+4B_J\varepsilon_N(J)}}2.
\]

For fixed `J`, all fixed base row decay makes `epsilon_N(J)->0`; then
`limsup_N e_N <= A_J^2`, and `J->infinity` proves zero defect.
For a quantitative moving-head provider it suffices that `J_N->infinity`
and `J_N log(J_N) epsilon_N(J_N)->0`. This is a sufficient provider to
seek, not an established arithmetic estimate.

### Exact obstruction to a uniform energy coercivity estimate

The energy criterion must retain the actual projection sequence and its
strong limit. There is no constant `C` with
`||x||_Q^2 <= C E_sf(x)` for all `x in M`.

For a prime `p`, set `x_p=p g_p` and
`y_p(n)=x_p(n)/n=(n mod p)/n`. For `2<=n<p`, `Delta y_p(n)=0`.
At `n=kp`,

\[
|\Delta y_p(kp)|=\frac{p-1}{kp-1}\le\frac1k.
\]

At a nonmultiple `n=kp+r>=p+1`, `1<=r<p`,

\[
\Delta y_p(n)=\frac{kp}{n(n-1)}\le\frac1{n-1}.
\]

Thus the full difference energy, including all tail sites, bounds the
squarefree energy by

\[
\mathcal E_{\mathrm{sf}}(x_p)
\le1+\frac1{Z(p-1)}.
\]

Meanwhile the complete norm contains `p-1` head terms equal to `1/Z`,
so `||x_p||_Q^2 >= (p-1)/Z`. The normalized legal atom
`u_p=x_p/||x_p||_Q` therefore satisfies

\[
\|u_p\|_Q=1,\qquad
\mathcal E_{\mathrm{sf}}(u_p)
\le\frac Z{p-1}+\frac1{(p-1)^2}\longrightarrow0.
\]

This exact unconditional obstruction prevents replacing the arithmetic
provider by a uniform spectral-gap claim.


## 3. Relation to finite optimizer coefficients

For a finite legal approximant `F=Σ_d c_d g_d` and `a≥2`,
\[
B_a(g_d)=\frac{\lfloor a/d\rfloor-a\mathbf1_{d\mid a}}{a(a-1)}.
\]
This is exactly zero for `d>a`. Since `B_a(1)=-1/[a(a-1)]`,
\[
B_a(1-F)=
\frac{-1-\sum_{d\le a}c_d\lfloor a/d\rfloor
+a\sum_{d\mid a,\ d\ge2}c_d}{a(a-1)}.
\]
At squarefree `a`, the coefficient of `c_a` is `1/a`.
Thus the base-row criterion is a triangular formulation of the existing
fixed-coefficient cancellation problem, rather than a proof of that
cancellation. Its useful additional content is exact base-only rigidity,
finite stability, and the obstruction to replacing arithmetic with a
uniform spectral-gap estimate.

## 4. Literature correction and next provider

Bagchi, arXiv:math/0607733, Remark 4 (PDF p.6) identifies squarefree support
of his damped Möbius approximants. Remark 8 (PDF p.9) explicitly states
RH equivalence to squarefree target closure for the exact Pareto model
`g_d(k)={k/d}`, weight `1/[k(k+1)]`. Real coefficients suffice by taking
real parts. No ordinary period-mean constraint is imposed.

The two physical norms obey the full comparison
\[
\|x\|_P^2\le Z\|x\|_Q^2\le2\|x\|_P^2.
\]
Therefore the same squarefree approximants converge in either norm.
The converse is established in the literature; the missing formal
dependency is its kernel-checked analytic provider. Squarefree target
membership is not squarefree totality of the entire ambient Hilbert space.

The concrete arithmetic provider remains one of:

1. All fixed squarefree base differences `B_a(r_n)→0`, possibly along one
   common cofinal subsequence.
2. A moving finite-head saving with `J_n→∞` and
   `J_n log(J_n) ε_n(J_n)→0`, for the actual residuals.
3. The existing complete normalized signed provider
   `max(signedCorrection n,0)/error n→0`, possibly cofinally.

No such provider is proved in this continuation. Universal whole-complement
caps tending to zero and uniform gradient coercivity are excluded above.
The exact finite error certificate retains the full trigamma tail.

## Sources and symbolic checks

- B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
  of the Riemann hypothesis*, https://arxiv.org/pdf/math/0607733, Remarks 4
  and 8. Supports the published squarefree closure equivalence and its
  approximation framework, not the new structural proofs.
- NIST DLMF 5.15.1, https://dlmf.nist.gov/5.15#E1. Supports the classical
  trigamma tail formula `Σ_(k>J) k^-2=ψ^(1)(J+1)`.
- Wolfram Language checked the exact generalized-eigenvalue polynomial,
  rational two-dual Rayleigh quotient, full inverse-square tail sum, and
  harmonic-number coefficient simplification. These are independent
  symbolic checks, not imported axioms or asymptotic evidence.
