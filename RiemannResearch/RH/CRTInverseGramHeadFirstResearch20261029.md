# CRT inverse-Gram analysis and head-first cancellation toward RH

Prepared for Christian Noack, 29 October 2026. Repository base: 933fb43028951dd503c7ec2a14808f365bad7e72.

**RH remains open.** This continuation addresses every milestone of the attached agenda. It proves exact source identities, removes an old-capacity hypothesis at all post-initial squarefree sites, and formalizes the conditional Gronwall route. It also gives paper proofs that CRT controls every finite inverse but that a uniform normalized spectral gap fails. No arithmetic subpolynomial-growth provider is asserted.

## Actual family and notation

Let $Q(n)=1/(\zeta(2)n^2)$, $g_d(n)=(n\bmod d)/d$, and use the complete norm
$\|F\|_Q^2=\sum_{n\ge1}Q(n)F(n)^2$.
At stage $i$, let $L_i$ be the product of the primes at most $2i+2$, $n=i+2$, and $p=2i+3$.
The old optimizer $F_i$ is the least-norm legal combination with
$F_i(1)=\cdots=F_i(i+1)=1$; $E_i=\|F_i\|_Q^2$.
It is the repository's minimumAt (denseSchedule i) (i+1), distinct from the error-minimizing QSquarefreeAffineHead.optimizer.

Let $T^-$ and $T^+$ be the old and enlarged zero-head tangents, $W=T^+\cap(T^-)^\perp$, and $Z_i$ the enlarged-dictionary old-head optimizer. Write $D=F_i-Z_i\in W$.
Let $k\in T^-$ and $\ell\in W$ be the old and innovation components of the next-coordinate Riesz vector:
$K=\|k\|^2$, $h=\|\ell\|^2$, and $\kappa=K+h$.
Put $a=1-F_i(n)$ and $b=1-Z_i(n)$, so $\langle D,\ell\rangle=b-a$.

For the actual full screened basis $(x_d)$ of $W$, define
$B_{de}=\langle x_d,x_e\rangle$,
$c_d=x_d(n)=\langle\ell,x_d\rangle$, and
$f_d=\langle x_d,F_i\rangle$.
Every added conductor is included. Empty blocks are permitted. All norms and projections use the complete Q law.

## Exact head-first reformulation

At every squarefree next site after the initial stage, $K>0$. Define

$$
x'_d=x_d-\frac{c_d}{K}k,\qquad
B'=B+\frac{cc^\top}{K},\qquad
r=f-\frac aKc.
$$

The adjusted columns are independent. The exact signed transition is

$$
\boxed{
E_{i+1}-E_i=\frac{a^2}{K}
-r^\top\left(B+\frac{cc^\top}{K}\right)^{-1}r.
}
$$

It permits zero innovation capacity and an empty block. It does not divide by $h$.
At the initial step $K_0=0$, retain the existing total-capacity formula.
At nonsquarefree next sites, the existing exact transition is
$E_{i+1}-E_i=-G_i$, where $G_i=\|D\|^2$.

### Proof and full remainder

The map $A(w)=w-\langle\ell,w\rangle k/K$ is injective:
$\langle\ell,k\rangle=0$ makes its inverse the same formula with a plus sign.
Its images of $x_d$ are $x'_d$. Orthogonality to $k$ gives $B'=B+cc^\top/K$.

The old-head-first optimizer is $Y=F_i+(a/K)k$. Its projection onto the adjusted span is

$$
D'=D-\frac b\kappa\ell+
\left(\frac aK-\frac b\kappa\right)k.
$$

Indeed $D'=A(D-(b/\kappa)\ell)$ belongs to that span, and
$\langle D',x'_d\rangle=\langle Y,x'_d\rangle=r_d$.
Expanding the complete norm yields

$$
\|D'\|^2=\frac{a^2}{K}
-\left(\frac{b^2}{\kappa}-\|D\|^2\right)
=\frac{a^2}{K}-(E_{i+1}-E_i).
$$

The inverse-Gram projection formula proves the boxed identity.

For every coefficient vector $v$, square expansion also gives the exact identity

$$
E_{i+1}-E_i=
\frac{a^2}{K}-2r^\top v+v^\top B'v
-\left\|D'-\sum_dv_dx'_d\right\|^2.
$$

This arbitrary-coefficient completion is a paper consequence here; the installed Lean declarations include the exact norm, pairing, Gram and full inverse identities.

The checked row estimate is

$$
r_d^2\le
\left(\frac{a^2}{K}-(E_{i+1}-E_i)\right)
\left(B_{dd}+\frac{c_d^2}{K}\right).
$$

For any positive $M_d\ge B_{dd}+c_d^2/K$ it follows that

$$
E_{i+1}-E_i\le\frac{a^2}{K}-\frac{r_d^2}{M_d}.
$$

Thus a useful *lower* bound on the gain source controls the upper energy increment. An upper bound on the whole inverse is not required by this route.

### Old capacity positivity

For $i>0$, the old Bertrand prime $r$ satisfies $r\ge i+2$, $r\mid L_i$, and $2\mid L_i$.
If $L_i\le i+2$, then $L_i=r=i+2\ge3$, contradicting that the prime $r$ is divisible by 2.
Therefore $L_i>i+2$.
At a squarefree $n=i+2$, one has $n\mid L_i$, and the old tangent vector
$g_n-(L_i/n)g_{L_i}$ evaluates to $-1$ at $n$.
The old evaluation functional is nonzero, so $K_i>0$.
This is proved for the actual family.

## Formalization map

These are the saved declarations submitted to the publication checkpoint. Publication requires successful validation of the saved modules; an earlier isolated snippet is not that gate.

| Module | Principal declarations | Scope |
|---|---|---|
| Analysis/OrthogonalObservationHeadFirst.lean | adjusted_inner, gain_norm, gain_pairing, joint_source_sq_le, signed_transition_le | Exact Hilbert identities and complete-norm inequalities |
| Analysis/FiniteHilbertGramHeadFirst.lean | headShear_injective, headFirstGain_projection, headFirst_inverseGram | Full finite-basis inverse identity |
| RH/QCRTHeadFirstSource.lean | oldCapacity_pos, dense_joint_source_sq_le, dense_headFirst_inverseGram | Actual optimizer specialization; positivity supplied for $i>0$ and squarefree $i+2$ |
| RH/QCRTInnovationPairGap.lean | screened_pair_identity, scaled_pair_gap_bound, pair_coercivity_bound | Actual two-column cancellation and finite coercivity obstruction |
| Analysis/DiscreteGronwall.lean | energy_le_exp_cumulative, relativeLog_tendsto_zero | Finite estimate and conditional asymptotic implication |
| RH/QCRTOptimizerGrowth.lean | riemannHypothesis_of_subpolynomial_stageEnergy, riemannHypothesis_of_stageEnergy_gronwall | Conditional research reductions; substantive arithmetic hypotheses remain Open |

The tensor CRT comparison and primorial spectral asymptotics below remain **paper-level**. The checked two-column estimate is the finite analytic ingredient of the collapse proof; it does not constitute a Lean proof of the entire asymptotic consequence.

## CRT analysis: 1. Setup and the two distinct conclusions

Let L be squarefree, p a prime with p not dividing L, and P=pL. The actual old tangent T is any subspace of the old L-periodic residue span used in the agenda. Set

\[
z_d=g_{pd}-\frac{L}{pd}g_L,\qquad
x_d=(I-P_T)z_d\quad(d\mid L),
\]

and let B be their complete-Q Gram matrix. The actual family in the agenda satisfies these hypotheses. Its proved basis theorem makes B positive definite. Write D=diag(d), S=diag(sqrt(pd)), and Bhat=SBS.

Two conclusions hold simultaneously:

1. CRT gives an explicit positive definite tensor-product lower comparison for B and hence a finite upper bound for B inverse. In normalized coordinates, a particularly simple bound is
   \[
   \widehat B\succeq \frac{1-p^{-2}}{48L}I,
   \qquad
   \|\widehat B^{-1}\|_{\mathrm{op}}\le\frac{48L}{1-p^{-2}}.
   \]
2. There is no stage-independent positive lower bound for Bhat. Close divisors give an explicit small Rayleigh quotient; along primorial stages the least eigenvalue tends to zero. This is a stronger obstruction than the existing raw primorial-anchor angle collapse.

The upper inverse bound costs a factor L, and is consequently far too large to supply the requested subpolynomial energy estimate. Spectral collapse does not rule out useful estimates on the actual sources f and c.

## CRT analysis: 2. Exact comparison between physical Q energy and finite Haar energy

For any P-periodic real sequence v, define

\[
\|v\|_{H_P}^2=\frac1P\sum_{a=1}^P v(a)^2.
\]

Periodic regrouping of the complete nonnegative sum gives

\[
\|v\|_Q^2=\sum_{a=1}^P w_P(a)v(a)^2,
\qquad
w_P(a)=\frac1{\zeta(2)}\sum_{j\ge0}\frac1{(a+jP)^2}.
\]

Since a+jP <= (j+1)P for 1<=a<=P,

\[
w_P(a)\ge\frac1{\zeta(2)P^2}\sum_{j\ge0}(j+1)^{-2}=P^{-2}.
\]

Therefore

\[
\boxed{\|v\|_Q^2\ge P^{-1}\|v\|_{H_P}^2.}
\]

This includes every physical tail. It does not identify Q with Haar measure. The loss P is precisely the price of this global comparison.

## CRT analysis: 3. CRT conditional innovations and their exact Gram matrix

For this section only, extend the harmless notation by g_1=0. Let n be uniform modulo P. Conditional on n modulo L, and hence on n modulo d for d|L, the p possible values of n modulo pd have the form b+d j, 0<=j<p, with j uniform. This follows because L/d is invertible modulo p. Consequently

\[
\mathbb E_{H_P}(g_{pd}\mid n\bmod L)
=\frac1p g_d+\frac{p-1}{2p}.
\]

Thus

\[
h_d=g_{pd}-\frac1p g_d-\frac{p-1}{2p}\mathbf1
\]

is orthogonal in Haar inner product to every L-periodic sequence, not merely to the old tangent.

For arbitrary positive a,b whose periods divide P, one has

\[
\operatorname{Cov}_{H_P}(g_a,g_b)
=\frac{\gcd(a,b)^2-1}{12ab}.
\]

Proof: put g=gcd(a,b), a=gA, b=gB. Conditional on n modulo g, the remaining residues modulo A and B are independent by CRT. The conditional means have their only common variable t=n mod g, and their covariance is Var(t)/(ab)=(g^2-1)/(12ab).

It follows either by expansion or by subtracting the covariance of the conditional expectations that

\[
\langle h_d,h_e\rangle_{H_P}
=\sigma_p\,\frac{\gcd(d,e)^2}{de},
\qquad \sigma_p=\frac{1-p^{-2}}{12}.
\]

Define C_L(d,e)=gcd(d,e)^2/(de). Squarefreeness makes this an exact tensor product:

\[
C_L=\bigotimes_{q\mid L}
\begin{pmatrix}1&q^{-1}\\q^{-1}&1\end{pmatrix}.
\]

Each binary divisor coordinate records whether q divides d. A prime occurring in exactly one of d,e contributes 1/q; a prime occurring in both or neither contributes 1.

## CRT analysis: 4. Lower comparison for the actual screened Gram matrix

For any real coefficient column v indexed by d|L,

\[
\sum_{d\mid L}v_d x_d=\sum_{d\mid L}v_d g_{pd}-u,
\]

where u is L-periodic: both the long-anchor term and its Q projection onto T are L-periodic. Its Haar-orthogonal component off the full space of L-periodic functions is exactly sum v_d h_d. Hence

\[
\begin{aligned}
v^\top Bv
&=\left\|\sum_d v_d x_d\right\|_Q^2\\
&\ge\frac1{pL}\left\|\sum_dv_dx_d\right\|_{H_P}^2\\
&\ge\frac1{pL}\left\|\sum_dv_dh_d\right\|_{H_P}^2\\
&=\frac{\sigma_p}{pL}v^\top C_Lv.
\end{aligned}
\]

Therefore

\[
\boxed{B\succeq\frac{\sigma_p}{pL}C_L,
\qquad B^{-1}\preceq\frac{pL}{\sigma_p}C_L^{-1}.}
\]

Inversion reverses the positive definite matrix order. Alternatively the inverse quadratic-form inequality follows directly from

\[
s^\top B^{-1}s=\sup_v(2s^\top v-v^\top Bv).
\]

Thus the comparison is valid for every source s, including the actual f and c. It is not a replacement of the actual Q projection by a Haar projection.

The exact inverse is

\[
C_L^{-1}=\bigotimes_{q\mid L}\frac1{1-q^{-2}}
\begin{pmatrix}1&-q^{-1}\\-q^{-1}&1\end{pmatrix}.
\]

Writing J_2(L)=L^2 prod_(q|L)(1-q^-2), this also reads

\[
C_L^{-1}(d,e)
=\frac{L^2}{J_2(L)}\mu(d)\mu(e)\frac{\gcd(d,e)^2}{de}.
\]

The eigenvalues of C_L are the products prod_(q|L)(1+epsilon_q/q), epsilon_q in {-1,1}; in particular lambda_min(C_L)=phi(L)/L. The unnormalized bound is

\[
\|B^{-1}\|_{\mathrm{op}}\le\frac{pL^2}{\sigma_p\varphi(L)}.
\]

## CRT analysis: 5. A uniform tensor bound after conductor normalization

Set M_L=D^(1/2) C_L D^(1/2). Then

\[
M_L=\bigotimes_{q\mid L}
M_q,\qquad
M_q=\begin{pmatrix}1&q^{-1/2}\\q^{-1/2}&q\end{pmatrix}.
\]

For delta_q=1/[q(q-1)], put a_q=1-delta_q. The two diagonal entries of M_q-a_q I are delta_q and q-1+delta_q, and its determinant is

\[
\delta_q(q-1+\delta_q)-q^{-1}=\delta_q^2\ge0.
\]

Therefore M_q >= a_q I. For q=2 the lower factor is 1/2. For all remaining primes,

\[
\sum_{q\mid L,\ q\ge3}\delta_q
\le\sum_{n=3}^\infty\frac1{n(n-1)}=\frac12.
\]

The finite inequality prod_j(1-t_j)>=1-sum_j t_j for 0<=t_j<=1 now gives

\[
\prod_{q\mid L}a_q\ge\frac14,
\qquad M_L\succeq\frac14I.
\]

When 2 does not divide L, the argument gives the stronger factor 1/2; the stated 1/4 is uniform and includes L=1.

Because S=sqrt(p) D^(1/2), the preceding actual Gram comparison becomes

\[
\widehat B\succeq\frac{\sigma_p}{L}M_L
\succeq\frac{\sigma_p}{4L}I.
\]

Consequently

\[
\boxed{\|\widehat B^{-1}\|_{\mathrm{op}}
\le\frac{4L}{\sigma_p}=\frac{48L}{1-p^{-2}}.}
\]

The more informative source bound retains the exact tensor inverse:

\[
\widehat s^\top\widehat B^{-1}\widehat s
\le\frac L{\sigma_p}\widehat s^\top M_L^{-1}\widehat s.
\]

The bound is finite and unconditional, but its factor L is exponential in the primorial cutoff. No subpolynomial energy conclusion follows from it.

## CRT analysis: 6. An exact two-column obstruction in the actual Q geometry

Let d<e divide L with e<=2d. Set m=pd, m'=pe, epsilon=(e-d)/d in (0,1], and u_d=sqrt(pd)x_d. The anchor terms cancel exactly:

\[
u_d-\sqrt{e/d}\,u_e
=\sqrt{pd}\,(I-P_T)\left(g_{pd}-\frac edg_{pe}\right).
\]

The agenda's complete conductor-gap theorem, together with contraction of I-P_T, gives

\[
\left\|u_d-\sqrt{e/d}\,u_e\right\|_Q^2
\le\frac\epsilon{\zeta(2)}
\left(\frac{21}{4}+\log\frac1\epsilon\right).
\]

The coefficient vector has Euclidean squared norm 1+e/d=2+epsilon. Hence

\[
\boxed{\lambda_{\min}(\widehat B)
\le\frac{\epsilon}{\zeta(2)(2+\epsilon)}
\left(\frac{21}{4}+\log\frac1\epsilon\right).}
\]

There is no short-anchor error term. This is an actual screened-vector estimate with the complete Q tail included.

## CRT analysis: 7. Close divisors force collapse at primorial stages

Order the tau(L) divisors as 1=d_1<...<d_t=L. Their logarithmic gaps sum to log L, so some consecutive pair satisfies

\[
\log(e/d)\le\eta_L:=\frac{\log L}{\tau(L)-1}.
\]

If eta_L<=log 2, the pair has e<=2d and epsilon<=exp(eta_L)-1. The scalar function

\[
F(t)=\frac{t(21/4+\log(1/t))}{2+t}
\]

is increasing on 0<t<=1: its derivative has positive numerator 2(17/4-log t)-t. Thus a fully explicit finite bound is

\[
\lambda_{\min}(\widehat B)
\le\frac1{\zeta(2)}
F\left(\exp\left(\frac{\log L}{\tau(L)-1}\right)-1\right).
\]

For L the product of the first k primes, tau(L)=2^k. Bertrand's postulate gives q_j<=2^j, so

\[
\log L\le\frac{k(k+1)}2\log2,
\qquad
\eta_L\le\frac{k(k+1)\log2}{2(2^k-1)}\longrightarrow0.
\]

Therefore lambda_min(Bhat) tends to zero along the actual prime-enlargement stages. Quantitatively the displayed estimates give lambda_min(Bhat)=O(k^3 2^-k), and hence ||Bhat inverse|| is at least a constant times 2^k/k^3 for sufficiently large k. No prime number theorem is needed for this statement in k.

The bound also gives an elementary obstruction in the stage scale. Bertrand implies p=q_(k+1)<=2^(k+1), so k>=log_2(p)-1. Since k^3 2^-k is decreasing for sufficiently large k, the estimate above yields
\[
\lambda_{\min}(\widehat B)=O((\log p)^3/p),
\qquad
\|\widehat B^{-1}\|_{\mathrm{op}}=\Omega(p/(\log p)^3).
\]
Thus even an all-stage subpolynomial upper bound for the entire normalized inverse is impossible. This remains a paper-level consequence; it does not rule out much smaller quadratic forms on the actual source vectors.

The corresponding maximum eigenvalue does not collapse to zero: choose the divisor d=L in the CRT lower comparison to obtain Bhat_(L,L)>=sigma_p. Thus the condition numbers also diverge.

## CRT analysis: 8. Consequences and remaining obligation

These results answer the proposed CRT route in two parts. CRT does control the inverse through an explicit exact tensor comparison, but the physical measure comparison costs the primorial factor. A fixed positive normalized spectral gap is impossible for the actual family. The two conclusions are compatible: the available upper inverse bound grows like L, while the lower inverse obstruction grows at least like 2^k/k^3.

Neither statement disproves RH or the exact-head strategy. Inverse growth in an unfavorable coefficient direction need not be seen by the actual moving sources. The decisive remaining estimate must control the coupled quantities f^T B^-1 f, c^T B^-1 c, c^T B^-1 f, or their signed combination, using their common arithmetic origin. No all-stage subpolynomial bound is supplied here.

The exact two-column inequality is formalized in QCRTInnovationPairGap using the existing contraction and conductor-gap theorems. The Haar comparison, CRT covariance factorization, inverse order, and primorial pigeonhole asymptotics remain paper-level lemmas until individually formalized.


## Agenda audit and precise remaining research obligation

Write $J_i=r_i^\top(B_i+c_ic_i^\top/K_i)^{-1}r_i$ at squarefree stages $i>0$.
For $N\ge1$, the exact stage identities give

$$
E_N=E_1+
\sum_{\substack{1\le i<N\\i+2\ {\rm squarefree}}}
\left(\frac{a_i^2}{K_i}-J_i\right)
-\sum_{\substack{1\le i<N\\i+2\ {\rm nonsquarefree}}}G_i.
$$

This summation is a paper consequence of the installed one-stage identity and the existing exact telescope. It retains all favorable negative terms.

A concrete remaining target is to find nonnegative sequences $\alpha_i,\beta_i$ with

$$
\frac{a_i^2}{K_i}-J_i
\le \alpha_iE_i+\beta_i
$$

at every post-initial squarefree step, such that

$$
\sum_{i<N}\alpha_i=o(\log(N+2)),\qquad
\log\left(1+\sum_{i<N}\beta_i\right)=o(\log(N+2)).
$$

The finitely many initial terms can be absorbed into $\beta_0$; nonsquarefree steps have nonpositive increments. The checked generic Gronwall theorem yields

$$
E_N\le\left(E_0+\sum_{i<N}\beta_i\right)
\exp\left(\sum_{i<N}\alpha_i\right).
$$

Its checked actual-family specialization then yields RH **only after all three displayed arithmetic providers have been proved**. This continuation does not prove them.

| Original milestone | Outcome | Remaining obligation |
|---|---|---|
| Joint actual sources | Exact head-first inverse identity; complete-norm row estimate; positive old capacity | Arithmetic lower bounds for the actual gain $J_i$, jointly with $a_i^2/K_i$ |
| Normalization and spectrum | Finite pair obstruction checked; explicit CRT inverse majorant and normalized spectral collapse proved on paper | Formalize tensor comparison and divisor asymptotics; exploit actual sources rather than a false uniform gap |
| Dyadic literal budget | Existing literal-budget consumer remains applicable; no uniform all-$\varepsilon$ bound found | Prove the actual dyadic budget bound, or use the signed alternative |
| Signed cancellation | Full head-first gain retained; Gronwall implication formalized and connected to actual RH consumer | Prove the actual recurrence and two growth estimates |
| Diagnostics and formal completion | Exact symbolic checks; full-Q estimates; empty block, zero innovation capacity and initial exception accounted for | No numerical pattern is promoted to an all-stage proof; RH specialization awaits a provider |

A fixed uniform lower eigenvalue claim for the normalized full block should be removed from the list of plausible targets: the close-divisor proof rules it out. Source-dependent estimates remain possible, because a nearly null coefficient direction also has small pairings with fixed Hilbert vectors. In the actual family those fixed vectors are replaced by moving optimizers; controlling their joint growth is the essential missing arithmetic input.

## Provenance and verification boundaries

The new Hilbert identities are developed from the user's innovation-space agenda and CRT question. The conductor-gap input is the existing QCompensatedResidueGap.compensatedResidue_gap_log_bound. No claim of mathematical priority is made.

The following primary sources were consulted for context, not used as substitutes for a missing actual-family provider:

- Jeffrey S. Ovall, *An analysis of GCD and LCM matrices via the LDL^T-factorization*, Electronic Journal of Linear Algebra 11 (2004), [DOI 10.13001/1081-3810.1121](https://doi.org/10.13001/1081-3810.1121). It supplies context for GCD-matrix factorizations. The particular tensor calculation above is proved explicitly here.
- Werner Ehm, *On certain Gram matrices and their associated series*, [arXiv:2405.06349](https://arxiv.org/abs/2405.06349). Related Nyman–Beurling Gram decompositions do not automatically transfer to this moving discrete Q family.
- François Alouges, Sébastien Darses and Erwan Hillion, *Polynomial approximations in a generalized Nyman–Beurling criterion*, [JTNB 34 (2022), 767–785](https://www.numdam.org/articles/10.5802/jtnb.1227/). Context for separating approximation geometry from coefficient control.

Wolfram Language independently checked the scalar square-completion identity, the $2\times2$ inverse, the local normalized PSD determinant, and the derivative used in the close-divisor bound. These symbolic checks are diagnostics. They do not replace the paper arguments or Lean validation.

The coherent isolated Lean candidate passed as job_cfN03C2JXjyISgKnEPsZjN5yO55u-HRA with exit code 0, verified=true, and reported server elapsed time 177.481 seconds. The audited actual inverse identity, Gronwall limit theorem and conditional RH consumer depended only on propext, Classical.choice and Quot.sound. The final saved-source checkpoint is separately required; its job and publication result are reported with the delivery. An accepted queue request is not verification. No unconditional RH theorem is claimed.

The separately saved module imports and selected axiom checks then passed
job_MmjkIsKN7ftJnmNxUVQb2RTZFfe6IU97: exit code 0, verified=true, server-reported
verification duration 507.698 seconds. Its queue delay was about 0.001 seconds.
The preceding 240-second saved-module attempt timed out after partial successful
compilation; the longer successful check resolved that verification blocker.
Workspace-opening round-trip time and accumulated client polling delay were
not separately recorded. These timings are not represented as pure kernel
proof-checking time. The publication checkpoint remains a distinct final gate.
