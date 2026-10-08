# Critical-zero obstruction and algebraic mean-one optimization

Research continuation, 8 October 2026 UTC (7 October locally).
Repository inspected: `Cnoack3/RiemannResearch`, published commit
`f8a32a9be492c5378de205141402a34bb694afd3`.

## Outcome and verification boundary

The current suggested GitHub prompt asks for an actual strict cofinal source
budget, or actual optimizer-tail product saving, and separately the analytic
RH-to-centered-approximation converse. None of those providers is proved here.
The finite head repair, complete source realization, and unconditional
coefficient-one moment bound are already present and must not be rediscovered
as missing hypotheses.

This continuation supplies complete paper arguments for:

1. An unconditional critical-zero obstruction: the recently proposed
   stretched-scale optimizer-tail saving is impossible, at every physical stage.
2. A sharper unconditional finite tail estimate, with `M^2/N` replacing `M^3/N`.
3. An exact mean-one optimizer whose logarithmic rank-two terms cancel, reducing
   the squarefree zero-defect question to an algebraic-core scalar approaching
   `4*pi`.
4. Unconditional logarithmic source cancellation at rate `o(L^(-1/2))`, while
   keeping the remaining zero-defect obligation explicit.
5. A collective lacunary-prime gain bound retaining all mutual correlations.

`RiemannResearch/LinearAlgebra/RankTwoResidualMean.lean` contains eight finite algebraic theorems:
matrix-derived residual moments, exact mean-one cancellation and square
completion, signed error numerator, and exact correction-square gap. All eight
pass a coherent isolated Lean check with exit code zero. Every axiom report
contains only `propext`, `Classical.choice`, and `Quot.sound`. Actual core
identification, the analytic critical-zero application, the asymptotic
cancellation, and the limiting RH criterion remain paper arguments rather
than newly formalized Lean results. No `sorry`, `admit`, or added axioms are
used in the source. Normal project-import validation is handled by the
repository checkpoint.

## 1. Physical definitions and the target being corrected

Let
\[
 \rho_j=\frac1{j(j+1)},\quad g_d(j)=\frac{j\bmod d}{d},\quad
 V_N=\operatorname{span}\{g_2,\ldots,g_N\},\quad
 v=(14,-12,-12,0,\ldots).
\]
Write `Q_N` for restriction to sites `1,...,N`, and put
\[
 p_N=P_{V_N}v,\qquad r_N=v-p_N,\qquad
 d_N=\|r_N\|^2,\qquad S_N=\|(I-Q_N)p_N\|^2.
\]
All norms include the complete physical tail; `||v||^2=134`.
The spaces are nested, so
\[
 \|p_N-p_M\|^2=d_M-d_N\quad(M\le N).
\]

The last paper, `RH_Actual_Arithmetic_Advances_2026-10-07.pdf`, proposed as
a sufficient provider a cofinal saving
\[
 N e^{-a h(N)}S_N\longrightarrow0,\qquad
 h(N)=\frac{(\log N)^{3/5}}{(\log\log N)^{1/5}},\quad 0<a<\eta,
\]
where `eta=(5/(3*(53.99)^3))^(1/5)` is the Mertens-envelope coefficient.
Section 2 below proves instead divergence to infinity for every such `a`.
This corrects that proposed provider, not the existing valid conditional RH
consumer for the *actual* product of trial energy and optimizer tail.

Repository indexing is distinct: `finiteSpace n` contains `g_2,...,g_(n+1)`.
Thus spectral stage `4m` uses `finiteSpace (4m+3)=V_(4m+4)` and physical
head cutoff `4m+4`. The paper quantity `S_(4m+4)` is therefore the literal
optimizer tail represented by the repository spectrum at stage `4m`.

## 2. A critical zero excludes the stretched-tail provider

### 2.1 A quantitative boundary obstruction

Associate to a sequence `f` its step function `f(floor x)` on `x>=1`, extended
by zero on `(0,1)`. This is an exact isometry into `L^2(dx/x^2)`, since
the mass of `[j,j+1)` is `1/(j(j+1))`.
For `0<Re(s)<1`, its absolutely convergent atom Mellin transform is
\[
 \mathcal M g_d(s)=\int_1^\infty g_d(\lfloor x\rfloor)x^{-s-1}\,dx
 =\frac{\zeta(s)}s(d^{-1}-d^{-s}).
\]
Indeed `g_d(floor x)={x/d}-{x}/d`; the standard fractional-part Mellin
identity gives the formula. This also follows from the actual corrected
atom Mellin signature already formalized in the repository.

Fix any zero `rho=1/2+i t` of zeta on the critical line. Its existence is
unconditional by Hardy's theorem; no assertion about other zeros is used.
Every finite legal approximant has Mellin value zero there, whereas
\[
 V(\rho):=\mathcal M v(\rho)
 =\frac{14-26\,2^{-\rho}+12\,4^{-\rho}}\rho
 =\frac{2(7-6\,2^{-\rho})(1-2^{-\rho})}\rho\ne0.
\]
Since `|2^(-rho)|=1/sqrt(2)`, a fully explicit lower bound is
\[
 |V(\rho)|\ge
 \frac{2(7-3\sqrt2)(1-1/\sqrt2)}{|\rho|}>0.
\]

The finite legal lift in the preceding paper gives
`||p_N||_infinity <= 4 N^(3/2) sqrt(134)`. For any real `R>=4`, the exact
Mellin decomposition, retaining the entire remaining tail, is
\[
 V(\rho)=\int_1^R r_N(\lfloor x\rfloor)x^{-\rho-1}\,dx
          -\int_R^\infty p_N(\lfloor x\rfloor)x^{-\rho-1}\,dx.
\]
Cauchy--Schwarz on the first term and the displayed supremum on the second
give
\[
 |V(\rho)|\le\sqrt{d_N\log R}
                 +8\sqrt{134}\,N^{3/2}R^{-1/2}.
\]
Taking `R=N^4` proves
\[
 d_N\ge\frac{[\,|V(\rho)|-8\sqrt{134}/\sqrt N\,]_+^2}{4\log N},
 \qquad d_N\ge\frac{c}{\log N}\quad\hbox{eventually},\quad c>0.
\]
The harmless refinement `R=N^3 (log N)^2` also proves
\[
 \liminf d_N\log N\ge |V(\rho)|^2/3.
\]
Boundary Mellin evaluation is *not* assumed continuous on the ambient Hilbert
space: its truncated dual norm is exactly `sqrt(log R)`. This is why this
argument gives a logarithmic lower bound rather than a positive norm defect.

### 2.2 Exact trial identity at every stage

Let `u_M` be the canonical compact corrected trial at a fourfold conductor `M`,
with complete energy `U_M=||u_M||^2` and reciprocal charge `q_M`. The existing
complete floor expansion is
\[
 u_M(j)=\sum_{d\le M}a_d\lfloor j/d\rfloor
           -M q_M\lfloor j/M\rfloor,
\]
\[
 a_d=14\mu(d)-26\mathbf1_{2\mid d}\mu(d/2)
                  +12\mathbf1_{4\mid d}\mu(d/4),\qquad |a_d|\le52.
\]
The full divisor identity is
`sum_(d<=j) a_d floor(j/d)=v(j)`.

For each `N>=8`, choose `M=4 floor(N/4)`. Then `u_M` is legal in `V_N`,
`N-M<=3`, and `N<2M`. Consequently it agrees exactly with `v` below `M`, and
for `M<=j<=N` the complete head discrepancy is
\[
 v(j)-u_M(j)=\sum_{M<d\le j}a_d+M q_M.
\]
There are at most four such sites, and at most three omitted coefficients,
so
\[
 \|Q_N(v-u_M)\|\le2(156/M+|q_M|).
\]

Full projection orthogonality gives the exact signed identity
\[
 d_N=H_N+L_N,
\quad H_N=\langle Q_Nr_N,Q_N(v-u_M)\rangle,
\quad L_N=\langle(I-Q_N)p_N,(I-Q_N)u_M\rangle.
\]
Both complete tails and the signed head term are retained.
Since `||r_N||<=sqrt(134)`, the head term obeys
`|H_N|<=2 sqrt(134)(156/M+|q_M|)`.

### 2.3 Consequence of the unconditional Mertens provider

The published Mertens bound [2], together with the repository's complete
logarithmic Mertens-to-energy transfer and the exact three-family compact
trial decomposition, gives for every `0<b<eta`
\[
 |q_M|=O_b(e^{-b h(M)}),\qquad U_M=O_b(M e^{-b h(M)}).
\]
To see the rate loss explicitly, absorb the external logarithmic factor
using any smaller exponential coefficient, apply the uniform tail Mertens
bound in `canonicalMobius_energy_of_uniform_mertens_log`, and absorb its
factor `1+log(1/epsilon)` using a further arbitrarily small rate loss.
The fixed dilations do not change the attainable open coefficient interval.
These analytic rate consequences are paper proofs, not new Lean providers.

Because `h(N)/log log N -> infinity`, the head term is `o(1/log N)`.
The boundary obstruction therefore implies `L_N>=c/(2 log N)` eventually.
Complete-tail Cauchy--Schwarz gives
\[
 U_M S_N\ge L_N^2\ge\frac{c^2}{4\log^2N}.
\]
Fix `0<a<b'<b<eta`. Since `M/N->1` and `h(M)/h(N)->1`, eventually
`U_M<=C_b N exp(-b' h(N))`. Hence
\[
 \boxed{N e^{-a h(N)}S_N\ge
  \frac{c^2}{4C_b}\frac{e^{(b'-a)h(N)}}{\log^2N}
  \longrightarrow+\infty.}
\]
This holds at every sufficiently large physical stage, excluding every
cofinal subsequence proposed for that stretched upper envelope.
In particular `N S_N -> infinity` unconditionally. The earlier bounded
cofinal conductor-tail certificate is therefore impossible as well.

The actual product `U_M S_N` is not refuted: its lower floor here is only
of order `1/log^2 N`, which tends to zero. The existing strict product-fraction
and strict complete-source feedback providers remain meaningful open targets.

## 3. Sharper unconditional finite tails

A finite legal `f in V_M` has a finite Fourier expansion at distinct rational
frequencies of reduced denominator at most `M`, including frequency zero.
Their circular separation is at least `M^(-2)`. Let
`A_M(f)` be its ordinary periodic mean-square, equal to the squared Fourier
coefficient sum.

The two-sided dual large sieve [3] gives, for every integer block length `K>=1`,
\[
 (K-1-M^2)A_M(f)\le\sum_{j=t+1}^{t+K}|f(j)|^2
                \le(K-1+M^2)A_M(f).
\]
With `K=2M^2+1`, comparison to the full physical norm yields
\[
 A_M(f)\le(4M^2+6+2/M^2)\|f\|^2\le6M^2\|f\|^2\quad(M\ge2).
\]
For the tail prefix `B_k=sum_(j=N+1)^(N+k)|f(j)|^2`, exact discrete Abel
summation retains the finite endpoint:
\[
 \sum_{k=1}^K\rho_{N+k}|f(N+k)|^2
 =B_K\rho_{N+K}+\sum_{k=1}^{K-1}B_k(\rho_{N+k}-\rho_{N+k+1}).
\]
The endpoint tends to zero. The upper block inequality and the elementary
telescoping weight sum give
\[
 \|(I-Q_N)f\|^2\le A_M(f)
 \left(\frac1{N+1}+\frac{M^2-1}{(N+1)(N+2)}\right).
\]
For `N>=M^2`, apply this to `p_M`, then use the exact nested-projection
difference before the triangle inequality:
\[
 \sqrt{S_N}\le\sqrt{d_M-d_N}+
                         \sqrt{1608M^2/(N+1)},
\]
\[
 \boxed{S_N\le2(d_M-d_N)+3216M^2/(N+1).}
\]
This improves the preceding paper's `4288M^3/(N+1)` term and permits any
multiscale exponent below `1/2`, rather than below `1/3`. It does not supply
the strict actual product budget. This section is a paper proof using the
classical large sieve, not a Lean formalization of that analytic theorem.

## 4. Exact optimization at ordinary mean one

For squarefree `L>2`, let
\[
 W_L=\operatorname{span}\{g_d:d\mid L,\ d>1\},\qquad
 H_d=\sum_{a\mid d}\mu(d/a)(a g_a).
\]
Use the complete Gram identity established in the preceding paper:
\[
 \Gamma_L=\pi F_L+\tfrac12(\lambda\varphi^T+\varphi\lambda^T),
 \quad\lambda_d=\Lambda(d),\quad\varphi_d=\phi(d).
\]
Here `F_L` is real algebraic, symmetric, invertible with exactly one negative
eigenvalue; `Gamma_L` is positive definite. These actual arithmetic identities
are paper results; current generic Lean reductions do not establish them.
For packet coefficients `c`, ordinary mean is `varphi^T c/2` and target
pairing is `lambda^T c`.

Put
\[
 A=\lambda^TF^{-1}\lambda,\quad B=\lambda^TF^{-1}\varphi,
 \quad C=\varphi^TF^{-1}\varphi,\quad D=2\pi+B,
\]
\[
 \alpha=-A,\qquad\gamma=-C,\qquad T=\alpha\gamma-D^2.
\]
For the actual unconstrained optimizer, projection energy `Q=1-E` and
ordinary residual mean `m` satisfy the exact equations
\[
 \pi Fc=m\lambda-\tfrac Q2\varphi,\qquad
 DQ=2Am,\qquad 2Dm-CQ=4\pi.
\]
The determinant lemma and the core inertia give `D^2-AC<0`, so
\[
 Q=\frac{4\pi\alpha}{T},\qquad m=-\frac{2\pi D}{T},\qquad
 \alpha,\gamma>0,\qquad T>4\pi\alpha.
\]
Positivity of `F` on `varphi`-orthogonal vectors proves `C<0`: for
`w=F^(-1)varphi`, `C=0` would contradict positivity, while `C>0` and the
orthogonal decomposition along `w` would make `F` positive definite.

Impose ordinary mean one, `varphi^T c=2`. The full physical error is then
\[
 1-2\lambda^Tc+c^T\Gamma c=1+\pi c^TFc.
\]
Both logarithmic rank-two terms cancel exactly. The constrained optimizer is
\[
 \boxed{c^0=\frac{2F^{-1}\varphi}{C}},\qquad
 \boxed{E_L^0=1+\frac{4\pi}{C}=1-\frac{4\pi}{\gamma_L}}.
\]
The coefficients are algebraic. For every admissible `c`, put `z=c-c^0`.
Then `varphi^T z=0`, and the full square completion is
\[
 \|1-F_c\|^2=E_L^0+\pi z^TFz.
\]
It proves unique optimality, with no logarithmic term or quadratic remainder
discarded. At a common-period site every legal approximant vanishes, so
`E_L^0>0` and `gamma_L>4*pi`.

The precise mean penalty is
\[
 \boxed{E_L^0-E_L=\frac{4\pi D_L^2}{\gamma_LT_L}
                        =\frac{Q_LD_L^2}{\alpha_L\gamma_L}.}
\]
As an exact check, at `L=6` one has `C=-8 sqrt(3)` and
`c^0=(2/3,1/2,1/6)` in packet order `(2,3,6)`. Thus the actual constrained
approximant is `g_2+g_3+g_6`, with error
\[
 E_6^0=1-\frac\pi{2\sqrt3}=0.093100317882891\ldots.
\]
This is an identity in the physical measure, distinct from the auxiliary
uniform-period optimizer that was shown to fail in the preceding paper.

## 5. The constraint is asymptotically free

For any legal conductor `L`, let
\[
 a_L=\frac{2L}{L-1}g_L.
\]
Its period mean is one, and `||g_L||^2<=2/L` gives
`||a_L||^2<=8L/(L-1)^2 ->0`.
For fixed `M|L`, the legal function `F_M+m_M a_L` has mean one. Therefore
\[
 \sqrt{E_L^0}\le\sqrt{E_M}
                +|m_M|\frac{\sqrt{8L}}{L-1}.
\]
Along an increasing unbounded divisor chain, first take `L` to infinity,
then take `M` to infinity. The constrained spaces are nested, and
`E_L^0>=E_L`, so their limiting errors agree and `E_L^0-E_L ->0`.
For an exhaustive squarefree chain, Bagchi's exact squarefree criterion [1]
therefore gives the paper equivalence
\[
 \boxed{\mathrm{RH}\iff\gamma_L=-\varphi_L^TF_L^{-1}\varphi_L
                                       \longrightarrow4\pi.}
\]
This limit is still open. The paper uses the known RH-to-squarefree
approximation converse; the repository does not yet formalize that converse.
No generic Lean matrix theorem is presented as discharging it.

### An unconditional signed logarithmic cancellation

The ordinary mean functional restricted to `W_L` has squared norm
\[
 h_L=\tfrac14\varphi^T\Gamma^{-1}\varphi
                    =\frac{\pi\gamma_L}{T_L}
                    =\frac{\gamma_LQ_L}{4\alpha_L}.
\]
Testing it on `a_L` yields
\[
 h_L\ge\frac{(L-1)^2}{8L},\qquad
 \alpha_L\le\frac{2\gamma_LQ_LL}{(L-1)^2}=O(1/L).
\]
On a nested chain, `Q_L` stays above any fixed initial nonzero projection
energy, and `gamma_L` stays bounded above. The mean-penalty identity and
`E_L^0-E_L ->0` therefore imply `D_L^2/alpha_L ->0`. Consequently
\[
 \boxed{\lambda_L^TF_L^{-1}\varphi_L+2\pi=o(L^{-1/2}).}
\]
This is unconditional along any increasing unbounded divisor chain. It
does not prove `gamma_L ->4*pi`; it proves that the full logarithmic coupling
in the actual residual formula becomes negligible.

### Exact algebraic block update

For nested cores `F'=[[F,J],[J^T,F_new]]`, inertia gives the positive Schur
complement `S=F_new-J^T F^(-1)J`. With
\[
 U=\lambda_{\rm new}-J^TF^{-1}\lambda,
 \qquad V=\varphi_{\rm new}-J^TF^{-1}\varphi,
\]
the complete update is
\[
 A'=A+U^TS^{-1}U,\quad B'=B+U^TS^{-1}V,\quad C'=C+V^TS^{-1}V.
\]
Thus `gamma` decreases and
\[
 \gamma-\gamma'=V^TS^{-1}V,\qquad
 E^0-E^{0\prime}=4\pi(1/\gamma'-1/\gamma).
\]
Writing `penalty=E^0-E`, the actual physical gain is exactly
\[
 E-E'=4\pi(1/\gamma'-1/\gamma)-\mathrm{penalty}
                                      +\mathrm{penalty}'.
\]
The signed correction telescopes and tends to zero. The remaining arithmetic
target is saturation `gamma_infinity=4*pi`, not just positivity of each drop.

## 6. A valid collective-prime estimate

For `2<=a<=b`, use `0<=g_d(j)<=min(j/d,1)` and split physical sites into
`j<a`, `a<=j<b`, and `j>=b`. The three contributions to `<g_a,g_b>` are at
most `1/b`, `(H_b-H_a)/b<=log(b/a)/b`, and `1/b`, respectively. Thus
\[
 0\le\sqrt{ab}\langle g_a,g_b\rangle
             \le(2+\log(b/a))\sqrt{a/b}.
\]
For a finite family `d_(i+1)>=K d_i`, `K>1`, put `r=K^(-1/2)` and
\[
 B_K=2+\frac{4r}{1-r}+\frac{2\log K\,r}{(1-r)^2}.
\]
The function `(2+log t)/sqrt(t)` decreases on `t>=1`. Every absolute row
sum of the normalized complete Gram is therefore bounded by `B_K`.
The inequality `2|x_i x_j|<=x_i^2+x_j^2` gives
\[
 \left\|\sum_i x_i\sqrt{d_i}g_{d_i}\right\|^2\le B_K\sum_i x_i^2.
\]
Projection contraction preserves this bound after screening against any old
space `W`. Let `h_i=(I-P_W)sqrt(d_i)g_(d_i)` and
`eta_i=<r_old,h_i>`. The explicit legal trial
`P_W target + B_K^(-1) sum_i eta_i h_i` has the exact error
\[
 E_{\rm old}-\frac2{B_K}\sum_i\eta_i^2
                       +\frac1{B_K^2}\eta^TS\eta,
\]
where `S` is the full screened Gram. Hence
\[
 \boxed{\text{joint gain}\ge B_K^{-1}
                  \sum_i d_i|\langle r_{\rm old},g_{d_i}\rangle|^2.}
\]
For finitely many fresh lacunary primes, this can be combined with the
preceding paper's fixed-stage signed source estimate to give
\[
 \text{joint gain}\ge\frac1{B_K}\sum_i
 \frac{[\,|m_L|\log p_i-|C_L^{\rm src}|-\zeta(2)R_L/p_i\,]_+^2}{p_i}.
\]
The notation `C_L^src` distinguishes the centered harmonic source constant
from the algebraic inverse-core scalar `C` above. All prime interactions are
retained through `S`; individually optimized gains are not simply added.
At geometric scales this lower-bound series converges, so it does not prove
the moving-stage normalized cumulative divergence target.

## 7. Corrected next GitHub prompt

Continue from the fresh published repository head; read `AGENTS.md` and this
continuation first. Do not try to prove `N exp(-a h(N)) S_N ->0` for
`0<a<eta`: the critical-zero argument above excludes it unconditionally.

1. The eight finite algebraic declarations are now kernel checked. Formalize
   the actual core identity/inertia and the mean-one repair closure
   before claiming an actual Lean core criterion. Keep the known paper
   RH-to-squarefree converse separate from its missing formal provider.
2. Formalize the critical-line truncated Mellin lower bound with its full
   tail and the exact compact target numerator. Assemble the all-stage trial
   bridge and the external-rate transfer with explicit analytic assumptions.
3. Investigate the pure algebraic Schur drops
   `V^T S^(-1)V`: prove saturation of `gamma` at `4*pi`, or a concrete strict
   feedback estimate using the complete source. Positivity alone does not
   prove saturation.
4. For actual product saving, estimate `U_N` itself together with the signed
   pairing and complete optimizer tail. Its coarse Mertens upper envelope
   cannot substitute for the actual norm in a prospective vanishing product.
5. Preserve the negative correction squares and all endpoint terms in any
   compensated cumulative gain argument. Distinguish saturation of the
   absolutely summable two-coefficient increments from divergence of the
   normalized full squarefree block gains.

## Sources and computational checks

[1] B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis*, especially Remarks 4 and 8.
https://arxiv.org/pdf/math/0607733 . Supports the actual squarefree closure
equivalence, not the new inverse-core calculations.

[2] E. S. Lee and N. Leong, *New explicit bounds for Mertens function and the
reciprocal of the Riemann zeta function*, version 5, 9 September 2026,
Theorem 1.1, equation (12). https://arxiv.org/html/2208.06141v5 . Supports
the unconditional Mertens envelope; full physical energy transfer is an
additional repository/paper argument displayed above.

[3] H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory II*,
author draft, Exercise 19.1.1.10, printed page 157, PDF page 168.
https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf .
Supports the two-sided dual large-sieve inequality.

[4] A. Dixit, R. Kumar, B. Maji and A. Zaharescu,
*Zeros of combinations of the Riemann Xi-function and the confluent
hypergeometric function on bounded vertical shifts*.
https://arxiv.org/abs/1712.08435 . Its introduction records Hardy's
unconditional existence theorem. Only existence of one critical zero is used.

Wolfram independently checked the two scalar solutions, complete Abel weight
sum, and exact `L=6` mean-one example. Those checks support finite algebra;
they are not proofs of the new asymptotic results or interval certificates.
