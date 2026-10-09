# Increasing-conductor recovery: exact certificate and obstruction

Research date: 9 October 2026. Starting published head: `2cf37c4e8ea9efcdfad8b8ae7b088104624ca839`.

Verification status: the coherent source check `job_50VwwUU9eARGB3ItCz6_0QaogtOG6qqv` completed successfully (exit code 0), checking all 44 new public declarations together. The transitive axiom audit and repository publication gate are recorded below.

The actual inverse-square optimizer residual is `r_n=qOne-P_(V_n)qOne`, its error is `e_n=||r_n||^2`, its full screened reciprocal image is `s_n=D r_n-P_(V_n)(D r_n)`, and its normalized second moment is `m_2(n)=||s_n||^2/e_n`. Stage `n` contains the squarefree conductors through `n+1`. Write `Z=zeta(2)`.

## Main conclusions

The whole-complement conductor-five signed-recovery construction has an exact complete-tail matrix formulation for any finite conductor set whose recovery equations are solvable. It cannot yield universal bounds tending to zero: a permanent radical dual gives the stronger all-stage first-moment floor `1337/3979` and compressed-square floor `(1337/3979)^2`. Full independent head recovery is already impossible at four sites.

A separate target-specific resolvent inequality is unconditional for every stage `n` and every integer `M>=1`:

\[
e_n\le\frac{H_M}{Z}\left(\sqrt{m_2(n)}+\frac1M\right).
\]

It supplies a quantitative recovery certificate with the complete infinite tail, but supplies no arithmetic decay of `m_2(n)`. The precise missing input remains cancellation for the actual moving optimizer coefficients.

## 1. Exact arbitrary-conductor signed recovery

Let `S` be any finite set of squarefree conductors at least two, let
`g_d(k)=(k mod d)/d`, and assume `x` is orthogonal to these actual atoms.
The full signed normal equations are

\[
\sum_{k\ge1}\frac{g_d(k)x(k)}{k^2}=0\qquad(d\in S).
\]

Choose a head of length `h>=1` and recovery coefficients `lambda_(i,d)` that satisfy

\[
\sum_{d\in S}\lambda_{i,d}g_d(j)=-j^2\mathbf1_{i=j}
\quad(1\le i,j\le h).
\]

These finite linear equations are required for a full-head certificate; their
solvability is not assumed for arbitrary squarefree sets. Define the periodic
signed rows `w_i(k)=sum_d lambda_(i,d)g_d(k)`. Then, exactly,

\[
x(i)=\sum_{k>h}\frac{w_i(k)x(k)}{k^2}.
\]

For `1/(h+1)<tau<1/h`, put

\[
T_\tau=\sum_{k>h}(\tau-1/k)\frac{x(k)^2}{k^2},\quad
J_\tau=\sum_{i=1}^{h}\frac{1/i-\tau}{i^2}x(i)^2.
\]

The complete energy identity is

\[
Z(\tau\|x\|^2-\langle x,Dx\rangle)=T_\tau-J_\tau.
\]

The signed complete recovery Gram matrix is

\[
G_{ij}(\tau)=\sum_{k>h}
\frac{w_i(k)w_j(k)}{k^2(\tau-1/k)}.
\]

Every series here converges: the recovery rows are bounded and periodic,
the tail gap is strictly positive, and the physical coordinate series are
controlled by the full inverse-square norm. Put
`Q=diag((1/i-tau)/i^2)`. Infinite weighted Cauchy proves that
`sqrt(Q) G sqrt(Q) <= Lambda I` implies `J_tau <= Lambda T_tau`.
The off-diagonal entries retain their signs. If `Lambda<=1`, the universal
first-moment cap is `tau`; the existing positive-form screening assembly
then supplies the universal compressed-square cap `tau^2`.

Let `L=lcm(S)` and let `k_a` be the least integer at least `K=h+1` in
residue class `a mod L`. The exact complete-tail identity is

\[
G_{ij}(\tau)=\frac1L\sum_{a=0}^{L-1}w_i(a)w_j(a)
\left[\psi(k_a/L)-\psi((k_a-1/\tau)/L)\right].
\]

It follows from the exact partial fraction
`1/[k^2(tau-1/k)]=1/(k-1/tau)-1/k` and the classical digamma series.
Likewise each complete inverse-square progression has mass
`L^-2 psi_1(k_a/L)`. Thus polygamma identities fully evaluate the tail;
they do not bound the moving recovery coefficients or imply cancellation.

### A rank obstruction before any asymptotic estimate

Every squarefree atom satisfies

\[
g_d(4)-g_d(3)-g_d(2)+g_d(1)=0.
\]

Indeed its exact backward difference is `1/d-1_(d divides k)`, and
`d divides 4` iff `d divides 2` for squarefree `d`. Therefore the first
four columns of the residue evaluation matrix have a permanent linear
dependence. A full-head recovery system for all independent coordinates
cannot exist once `h>=4`: the desired first row with values
`(-1,0,0,0)` contradicts that dependence. Enlarging the conductor set
does not remove it. Recovery can still be designed for constrained
coordinates or a smaller head, but its universal cap has the spectral
floor proved below.

This is an all-conductor obstruction, not evidence from a finite number
of optimizer stages.

## 2. Stronger permanent obstruction and exact correction decomposition

Let `f_4` be the existing literal vector `(1,-4,-9,16)` at sites `1,2,3,4`.
Let `f_8` be `(1,-4,-49,64)` at sites `1,2,7,8`. Then

\[
Z\langle f_8,x\rangle=\Delta x(8)-\Delta x(2).
\]

Because squarefree `d` has `d divides 8` iff `d divides 2`, `f_8` is
orthogonal to every squarefree residue atom and to the constant target.
The exact physical matrices are

\[
G=\begin{pmatrix}30&5\\5&118\end{pmatrix},\qquad
H=\begin{pmatrix}10&3\\3&18\end{pmatrix}.
\]

For `w=16 f_4+f_8`, both signed cross interactions are retained:

\[
Z\|w\|^2=30\cdot16^2+2\cdot5\cdot16+118=7958,
\]
\[
Z\langle w,Dw\rangle=10\cdot16^2+2\cdot3\cdot16+18=2674.
\]

At every integer stage, `w` is in `V_n^perp`; full screening preserves
`<w,P_(V_n^perp)Dw>=<w,Dw>`. Consequently every universal first-moment
cap is at least `1337/3979>1/3`, and every universal compressed-square
cap is at least `(1337/3979)^2=1787569/15832441>1/9`.
No sequence of these universal caps, including any cofinal stage
sequence, can tend to zero. This remains true if RH holds.

The two-dual generalized characteristic polynomial is
`3515 lambda^2-1690 lambda+171`; its upper root
`(845+8 sqrt(1765))/3515` is a slightly sharper paper-level floor.
The checked Lean declarations use the simple exact rational witness above.

The actual target residual is perpendicular to both duals. Thus the
universal floors do not constitute a lower bound on its own moment.
Its reciprocal image need not be perpendicular to these duals. Define
`b_i=Z<f_i,D r_n>=Z<f_i,s_n>`, and

\[
\alpha=(118b_4-5b_8)/3515,\qquad
\beta=(30b_8-5b_4)/3515.
\]

The exact target identity is

\[
e_n m_2(n)=\varepsilon_n+\delta_n-\sigma_n
=\frac{118b_4^2-10b_4b_8+30b_8^2}{3515 Z}
 +\|s_n-\alpha f_4-\beta f_8\|^2.
\]

Here `epsilon=quarticFloor`, `delta=weightedMismatch`, and
`sigma=screening` are the actual repository quantities. Both optimizer
correction squares, the negative cross term, and the complete remaining
norm square are retained. A finite dual certificate does not control
that entire remainder.

For any finite legal approximant `F=sum c_d g_d`, the raw signed rows are

\[
Z\langle f_4,D(1-F)\rangle=(5-4c_2-c_3)/12,
\]
\[
Z\langle f_8,D(1-F)\rangle
=(27-24c_2-2c_3-c_5-c_6-c_7)/56,
\]

with absent coefficients interpreted as zero. All legal conductors
greater than eight contribute zero directly. Adding larger conductors
changes these rows through the actual optimizer's small-conductor
coefficients; it does not erase the required signed relations.

## 3. Uniform target-specific resolvent recovery

For `t>0`, write

\[
A(t)=\sum_{k\ge1}\frac1{k(1+tk)}=\psi(1+1/t)+\gamma.
\]

Start from the complete signed target identity
`<r_n,1>=||r_n||^2=e_n`. Infinite weighted Cauchy, with the exact
pointwise factorization

\[
\left(\frac{r_n(k)}{Zk^2}\right)^2
=\left[\frac{r_n(k)^2}{Zk^2}(1/k+t)\right]
 \left[\frac{1}{Zk^2(1/k+t)}\right],
\]

gives

\[
e_n^2\le\left(\langle r_n,Dr_n\rangle+t e_n\right)\frac{A(t)}Z.
\]

All three series are summable. The signed pairing is used before
Cauchy; it is not replaced by an absolute-value sum. Orthogonality to
the full screening projection gives

\[
\langle r_n,Dr_n\rangle=\langle r_n,s_n\rangle
\le e_n\sqrt{m_2(n)}.
\]

Every finite actual-stage error is positive by the existing common
factorial-site theorem, so division is justified. Thus

\[
e_n\le\frac{A(t)}Z(\sqrt{m_2(n)}+t)
\qquad(\forall n\ge0,\ \forall t>0).
\]

For every positive integer `M`, the exact finite identity

\[
\sum_{k=1}^{N}\frac{M}{k(k+M)}
=H_M-\sum_{j=1}^{M}\frac1{N+j}
\]

retains its complete terminal remainder. Taking its limit proves
`A(1/M)=H_M`. This yields the formal target statement for every pair
`(n,M)` with `M>=1`; no stage-dependent cancellation hypothesis occurs.

The actual correction formulation is unchanged:

\[
e_n\le\frac{H_M}{Z}
\left(\sqrt{\frac{\varepsilon_n+\delta_n-\sigma_n}{e_n}}+\frac1M\right).
\]

For each fixed `M`, this also gives the paper-level lower certificate

\[
m_2(n)\ge
\max\{Z e_n/H_M-1/M,0\}^2.
\]

If `m_2(kappa_j)->0` on a common cofinal sequence, fix `M` first and
take the limit: the limiting defect is at most `H_M/(ZM)`.
Then `M->infinity` makes this bound zero. This recovers the existing
closure implication with quantitative constants; it does not establish
the required moment decay.

For `q=sqrt(m_2(n))>0` tending to zero, choosing `M=ceil(1/q)` gives
`e_n<=2q[1+log(1+1/q)]/Z`. The rate is a conditional consequence of
small moments, not an unconditional decay estimate.

### Sharpness of the purely geometric inequality

Let `B(t)=sum_(k>=1)(1+tk)^-2=t^-2 psi_1(1+1/t)`,
`alpha=A(t)/B(t)`, and `r_t(k)=alpha k/(1+tk)`.
Then `||r_t||^2=<r_t,1>=A(t)^2/[Z B(t)]`.
Thus `r_t` is the projection residual of the constant onto
`span{1-r_t}`. Since `D r_t=alpha 1-t r_t`, its screened image is
`(alpha-t)r_t`. The exact positive identity
`A(t)-t B(t)=sum 1/[k(1+tk)^2]>0` proves `alpha>t`.
Equality holds in the resolvent inequality. These spaces are not actual
squarefree stages: the example shows that residue-specific arithmetic
is required to improve pure projection geometry.

More precisely, along `t=1/M` with `M->infinity`, the complete formulas
give `A(t)=H_M~log M` and `B(t)=M^2 psi_1(M+1)~M`. Consequently this
example has `e~(log M)^2/(Z M)` and
`q=sqrt(m_2)=(A(t)/B(t))-1/M~(log M)/M`, so

\[
e\sim\frac{q\log(1/q)}Z.
\]

Thus the logarithmic recovery order is sharp for unrestricted projection
geometry. This asymptotic example does not assert sharpness within the
actual squarefree stage family.

## 4. Precisely what remains open

The arbitrary-conductor whole-complement recovery framework cannot
produce vanishing universal caps. Target-specific recovery can still
work, but the actual signed arithmetic provider has not been proved.
One must establish, for example, common cofinal decay of the normalized
positive correction, or the equivalent fixed squarefree reciprocal
base-row decay already tracked in the repository.

Restricting recovery to radical-compatible vectors requires care:
`r_n` is radical-compatible, but `s_n=P_(V_n^perp)D r_n` generally is
not. The existing squared compression argument uses a first-moment cap
on both vectors. Assuming the same restriction for `s_n` without proving
its permanent-dual row cancellations would hide the open dependency.

There is a safe target-only assembly. At stages `n>=4`, put
`a_n=<r_n,D r_n>` and let `beta=10745/28906` be the established universal
first-moment cap. Positive-form Cauchy on the complete signed pairing
`<s_n,D r_n>=||s_n||^2`, with the existing cap applied only to `s_n`, gives

\[
m_2(n)\le\beta\frac{a_n}{e_n}.
\]

The target-only assembly is now a checked declaration:
`ZetaTwoTargetFirstMoment.secondMoment_le_firstMoment`.
The actual normal equations and the proved four-site residual identity also
give the unconditional fixed saving
`a_n/e_n <= 39138061/126426000` for every `n>=4`.
This uses compatibility only for the input residual, never for its screened
image. The cofinal normalized first-moment decay needed for closure remains
Open. See `TargetFirstMomentStatus20261009.md` for the exact complete-tail
certificate, Mobius correction identity and coherent Lean verification record.

There is no unconditional moment-decay provider here, and no RH claim.

## 5. Provenance and verification distinctions

- NIST DLMF 5.7.6, https://dlmf.nist.gov/5.7#E6: supports the exact
  digamma interpretation of the complete signed Gram and resolvent masses.
- NIST DLMF 5.15.1, https://dlmf.nist.gov/5.15#E1: supports complete
  inverse-square progression and resolvent-square trigamma sums.
- B. Bagchi, https://arxiv.org/pdf/math/0607733, Remarks 4 and 8:
  establishes the squarefree closure converse at paper level. The missing
  formal analytic provider is separate from the actual arithmetic decay.
- M. Balazard and A. de Roton, https://arxiv.org/pdf/0812.1689:
  gives an RH-conditional approximation rate, not an unconditional provider.
- S. Bettin, J. B. Conrey, and D. W. Farmer,
  https://arxiv.org/pdf/1211.5191: a smoothed Mobius approximation asymptotic
  assumes RH and an additional inverse-zeta-derivative moment estimate.

The new structural arguments were developed independently and reviewed
on paper. Wolfram evaluated the exact raw matrices, rational witness
quotient, characteristic polynomial, and resolvent polygamma series;
these symbolic results are independent checks, never Lean proof inputs.
The arbitrary-conductor digamma evaluation, rank obstruction, lower moment
certificate, general-t sharpness, and coefficient row formulas are paper
results. The 44 public declarations in the two new Lean modules passed the
coherent kernel source check. Repository publication additionally passes
through the affected-module checkpoint gate.

## 6. Lean verification record

| Module | Public theorems | SHA-256 of checked module source |
| --- | ---: | --- |
| `RH/ZetaTwoResolvent.lean` | 18 | `e5de398ca4ce05c8264f921759f9da508eacf3fe02a00366ddfc6550086364cc` |
| `RH/ZetaTwoDualEightObstruction.lean` | 26 | `b98496dd37d5775932ab015bec9151445486f4a05e553956e5a87870ec222c02` |

The complete bodies of both modules were checked together in terminal job
`job_50VwwUU9eARGB3ItCz6_0QaogtOG6qqv`, exit code 0. Its visible audit
output covers all 26 dual-obstruction public declarations. Because the
beginning of that output was truncated, terminal job
`job_L4zNYL0T2H8YdtDZ78kPJVO_bk8hpXq-` rechecked the coherent bodies
and printed the 18 resolvent audits in full; exit code 0, no truncation.
Every public theorem's transitive axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`. There are no project-local axioms,
proof holes, or arithmetic-decay hypotheses hidden in the target estimates.

The universal-cap lower-bound theorems explicitly take a proposed universal
cap as a hypothesis and prove its necessary positive floor. Those hypotheses
are mathematical quantifiers, not new axioms. The actual-stage resolvent
estimate takes only `0<M`; all stage and optimizer facts use repository
definitions. The exact correction theorem includes both `weightedMismatch`
and `screening`, with opposite signs.

Both modules are exported through `RiemannResearch.lean`, and the theorem
catalog records their exact scope. The modules, this report, and the catalog
are submitted together to the serialized validation-and-publication
checkpoint. No actual screened-moment decay or RH theorem is asserted.
