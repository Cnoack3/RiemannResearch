# Fixed-head transport of mixed-trial losses and source drift

30 October 2026. Continuation of the user's signed full-squarefree arithmetic
agenda and [the preceding memorandum](SignedDyadicArithmeticResearch20261030.md).

**Status: paper proofs, not newly Lean-verified.** The retained Lean workspace
accepted a retry, but the job timed out. The normalized signed dyadic excess
limit remains open. The finite estimates below apply to the actual unrestricted
optimizer and the exact mixed trials in `QCRTMixedFloorTrial.actualTrials`.
They do not assume that an optimizer is supported on primes.

The main additions are an exact orthogonal transport of the unused loss vectors,
an exact signed block identity, and a quantitative bound for variation of a
fixed-final-head dual source as the period grows. The last bound has no factor
equal to the number of stages. It still requires an arithmetic coefficient
moment when paired with the changing optimizer coefficients.

## 1. Definitions and the actual global certificate

Write

\[
 Q(n)=\frac1{\zeta(2)n^2},\qquad g_d(n)=\frac{n\bmod d}{d},
 \quad L_i=\operatorname{primorial}(2i+2),\quad
 D_i=\{d>1:d\mid L_i\}.
\]

All norms and pairings below use the complete Q Hilbert space. Put
\(U_i=\operatorname{span}\{g_d:d\in D_i\}\), and let \(F_i\) be its actual
minimum-norm vector with values one through \(i+1\). Thus \(E_i=\|F_i\|^2\).
Let \(\widehat F_i\) be the old-dictionary minimum with values one through
\(H_i=i+2\). The complete divisor coefficients are denoted by \(b_{i,d}\)
and \(\widehat b_{i,d}\); coefficients outside a dictionary are zero.

Fix \(N\ge1\), the block \(N\le i<2N\), and final head \(K=2N+1\).
Use \(T_i^h=U_i\cap\ker(\operatorname{head}_h)\). Define

\[
 \Phi_i=\text{the minimum in }U_i\text{ with head }1\text{ through }K,
 \qquad N\le i\le2N.
\]

These minima exist: the repository's exact-head seed for period \(L_i\)
has head one through \(2i+1\ge K\). In particular \(\Phi_{2N}=F_{2N}\).

Use the following physical gain vector \(y_i\):

* If \(i+2\) is squarefree and \(p=2i+3\) is prime, use the exact optimal
  screened mixed vector already defined by `actualTrials`.
* If the head is squarefree and \(p\) is not prime, put \(y_i=0\).
  Here there is no new conductor and \(U_{i+1}=U_i\).
* At a nonsquarefree head put \(y_i=\widehat F_i-F_{i+1}\). This is an
  auxiliary representation of the **exact negative period gain** already used
  by `fullCertificate`, not a change to `actualTrials`. At such a head the old
  constraint is redundant and \(\widehat F_i=F_i\).

Set

\[
 r_i=\widehat F_i-F_{i+1}-y_i,\qquad \ell_i=\|r_i\|^2.
\]

Thus \(r_i=0\) on the last two cases, and \(\ell_i\) is exactly
`fullLoss actualTrials i`. The checked certificate completion gives

\[
 C_i=E_{i+1}-E_i+\ell_i. \tag{1}
\]

The physical residual above equals the full-family `minimumVector` minus
mixed synthesis: both full corrections belong to the span of the screened
added-conductor family and have its prescribed source pairings. The new
minimum is orthogonal to that family, so uniqueness of the Gram solution
identifies the vectors, not just their squared norms.

The already established screening and exact two-dimensional optimization give

\[
 r_i\in U_{i+1}\cap\ker(\operatorname{head}_{H_i}),\qquad
 r_i\perp T_i^{H_i},\qquad r_i\perp y_i,
 \qquad \langle\widehat F_i,r_i\rangle=\|r_i\|^2. \tag{2}
\]

For the last identity, write \(\widehat F_i=F_{i+1}+y_i+r_i\);
the new minimum is orthogonal to its head-null tangent. These assertions are
trivial when \(r_i=0\). No screening or determinant proof is repeated here.

## 2. Both mixed sources and the low residual coefficients

At an active prime stage, write \(G(e,f)=\langle g_e,g_f\rangle\) and
\(\widehat\kappa_i=L_i\langle\widehat F_i,g_{L_i}\rangle\). For every
\(d\mid L_i\), including \(d=1\), define

\[
 \xi_{i,d}=\sum_{e\in D_i}\widehat b_{i,e}G(e,pd)
              -\frac{\widehat\kappa_i}{pd}.
\]

Charge normalization \(\sum_{d\in D_i}b_{i,d}/d=1\) gives the two exact
sources

\[
 \begin{aligned}
 v_i&=\xi_{i,1}
   =\sum_e\widehat b_{i,e}G(e,p)-\widehat\kappa_i/p,\\
 u_i&=\sum_{d\in D_i}b_{i,d}\xi_{i,d}-\xi_{i,1}\\
 &=\sum_e\widehat b_{i,e}
       \left(\sum_{d\in D_i}b_{i,d}G(e,pd)-G(e,p)\right).
 \end{aligned} \tag{3}
\]

Both sums retain every composite squarefree conductor. For example, the
forced coefficients give
\(u_i=-v_i-\sum_{1<d\le i+1}\mu(d)\xi_{i,d}
             +\sum_{d>i+1}b_{i,d}\xi_{i,d}\), with both sums restricted to
\(D_i\). There is no sign assumption on these summands.

Let
\(x_i=\sum_d b_{i,d}g_{pd}-g_p\),
\(z_i=g_p-(L_i/p)g_{L_i}\), and let \(P_i^{H_i}\) project onto
\(T_i^{H_i}\). If the screened Gram entries are \(A_i,B_i,C_i^{\rm Gram}\),
the already proved positive determinant gives

\[
 \alpha_i=\frac{C_i^{\rm Gram}u_i-B_iv_i}{A_iC_i^{\rm Gram}-B_i^2},
 \qquad
 \beta_i=\frac{A_iv_i-B_iu_i}{A_iC_i^{\rm Gram}-B_i^2},
 \quad y_i=\alpha_i x_i+\beta_i z_i-\pi_i,
 \quad \pi_i=P_i^{H_i}(\alpha_i x_i+\beta_i z_i).
\]

This is the exact, unregularized trial. With any full-rank coefficient matrix
\(Z_i\) for the old head-null tangent, the projection coefficients satisfy

\[
 [\pi_i]=Z_i(Z_i^\top G_iZ_i)^{-1}Z_i^\top k_i,
\]

where, for every old conductor \(e\),

\[
 (k_i)_e=\alpha_i\left(\sum_d b_{i,d}G(e,pd)-G(e,p)\right)
       +\beta_i\left(G(e,p)-(L_i/p)G(e,L_i)\right). \tag{4}
\]

The inverse is on a basis of the finite-dimensional tangent, not on a
redundant observation list. If the tangent is zero the projection is zero.
No uniform bound on this inverse is asserted.

Write \(c_{i,d}\) for the complete divisor coefficients of \(r_i\). Since
\(r_i\) has head zero through \(H_i\), coefficient extraction gives
\(\sum_d c_{i,d}/d=0\) and \(c_{i,d}=0\) for \(d\le H_i\).
For \(H_i<d\le K\), all such squarefree conductors are old. Moreover
\(p>K\) and \(L_i>K\), so the raw trial has no coefficient in this band.
Consequently

\[
 c_{i,d}=\widehat b_{i,d}-b_{i+1,d}+[\pi_i]_d
 \quad(H_i<d\le K) \tag{5}
\]

at an active stage. At inactive stages \(c_{i,d}=0\). Equations (3)--(5)
give the low residual coefficients through both actual mixed sources and the
complete moving normal equations.

## 3. Repair the final head in the old dictionary

Every final-head trace of \(U_{i+1}\) is already realizable in \(U_i\).
Indeed, a squarefree conductor \(d\le K\) divides \(L_i\). All other new
conductors exceed \(K\), and their first \(K\) values are \(n/d\), which
can be replaced by \((L_i/d)g_{L_i}(n)\). Here \(L_i>K\): otherwise the
existing exact-head seed, which is \(L_i\)-periodic and zero at \(L_i\),
could not equal one through \(K\).

Let \(s_i\) be the unique minimum-norm vector in \(U_i\) whose first
\(K\) values agree with \(r_i\). It exists by the preceding trace argument.
Then

\[
 s_i\in T_i^{H_i},\qquad s_i\perp T_i^K,
 \qquad q_i:=r_i-s_i\in T_{i+1}^K\cap(T_i^K)^\perp. \tag{6}
\]

**Proof.** The common trace is zero through \(H_i\); minimum norm gives
orthogonality to the kernel of the final-head map. Subtracting the two traces
puts \(q_i\) in \(T_{i+1}^K\). Both \(r_i\) and \(s_i\) are orthogonal
to \(T_i^K\). This proves (6).

For \(i<j\), nesting gives \(q_i\in T_j^K\), hence
\(\langle q_i,q_j\rangle=0\). Also (2) gives
\(\langle r_i,s_i\rangle=0\). Therefore, with
\(\mathcal Q_N=\sum_{i=N}^{2N-1}q_i\) and
\(\mathcal S_N=\sum_i\|s_i\|^2\),

\[
 \boxed{\displaystyle
 \sum_i\ell_i=\|\mathcal Q_N\|^2-\mathcal S_N.} \tag{7}
\]

This is a finite exact identity. The original \(r_i\) are not asserted
orthogonal. The subtracted repairs in (7) are essential.

An alternative projection decomposition is also valid: set
\(\rho_i=P_{T_{i+1}^K}r_i\), \(\sigma_i=r_i-\rho_i\). The \(\rho_i\)
are pairwise orthogonal, and
\(\sum_i\ell_i=\|\sum_i\rho_i\|^2+\sum_i\|\sigma_i\|^2\).
The positive remainder here is the minimum repair in the **new** dictionary.
It must not be confused with the old repair \(s_i\) in (7).

There is a fully explicit old trace representative. For
\(H_i<d\le K<2(H_i+1)\), the floor is zero or one, so

\[
 r_i(n)=-\sum_{H_i<d\le n}c_{i,d}\quad(1\le n\le K).
\]

Thus \(\sum_{H_i<d\le K}c_{i,d}(g_d-(L_i/d)g_{L_i})\) has the required
trace. Projecting off \(T_i^K\) gives \(s_i\). In particular

\[
 \|s_i\|^2\ge\sum_{n=H_i+1}^{K}Q(n)
                   \left(\sum_{H_i<d\le n}c_{i,d}\right)^2. \tag{8}
\]

All conductor sums in this section range over squarefree divisors. The
elementary coefficient extraction used here follows by writing
\(r(n)=n\sum c_d/d-\sum c_d\lfloor n/d\rfloor\), then taking first
differences and inducting through its zero head.

## 4. An exact signed block identity

Put

\[
 a_i=\Phi_i-\widehat F_i,\quad
 \Delta_N^K=\Phi_N-F_{2N},\quad
 H_N=\|\Phi_N-F_N\|^2,\quad
 \mathcal P_N=\sum_i\langle a_i,s_i\rangle.
\]

Since \(a_i,s_i\in T_i^{H_i}\), equations (2) and (6) imply

\[
 \langle\Phi_i,q_i\rangle
       =\|r_i\|^2-\langle a_i,s_i\rangle.
\]

Also \(\Phi_N-\Phi_i\in T_i^K\) and \(F_{2N}\perp T_{2N}^K\).
Summing therefore yields a common-vector source identity

\[
 \sum_i\ell_i=\langle\Delta_N^K,\mathcal Q_N\rangle+
                    \mathcal P_N. \tag{9}
\]

Combine (7) and (9), keeping the exact completion square:

\[
 \sum_i\ell_i=\|\Delta_N^K\|^2+\mathcal S_N+2\mathcal P_N
                      -\|\Delta_N^K-\mathcal Q_N\|^2. \tag{10}
\]

The old head repair and the fixed-final-head period gain satisfy
\(E_{2N}-E_N=H_N-\|\Delta_N^K\|^2\). Hence (1) gives

\[
 \boxed{\displaystyle
 \sum_{i=N}^{2N-1}C_i
   =H_N+\mathcal S_N+2\mathcal P_N
       -\|\Delta_N^K-\mathcal Q_N\|^2
   \le H_N+\mathcal S_N+2\mathcal P_N.} \tag{11}
\]

Equivalently the signed summands in the upper bound are
\(\|a_i+s_i\|^2-\|a_i\|^2\). No positivity assumption on them is used.
Nonprime head costs and negative gains at dependent heads remain in the
endpoint/head identities and in the physical \(y_i\); none have been omitted.

## 5. Moving normal equations and a signed Abel expansion

Let \(f_{i,d}\) be the coefficients of \(\Phi_i\), and define

\[
 \kappa_i=L_i\langle\Phi_i,g_{L_i}\rangle,\qquad
 \eta_{i,d}=\sum_{e\in D_i}f_{i,e}G(e,d)-\kappa_i/d.
\]

The final-head normal equations give \(\eta_{i,d}=0\) for old \(d>K\).
The analogous sources for \(\widehat F_i\) vanish for \(d>H_i\).
The repair has charge zero and its coefficients through \(K\) equal those
of \(r_i\). Expanding its pairing in the complete dictionary therefore gives

\[
 \mathcal P_N=\sum_{i=N}^{2N-1}\quad
              \sum_{H_i<d\le K}c_{i,d}\eta_{i,d}. \tag{12}
\]

This is an equality, not a bound by absolute sources.

Let \(S_N=\{d:N+1<d\le K,\ d\text{ squarefree}\}\). For these conductors,
write \(h_{i,d}=\widehat b_{i,d}-b_{i,d}\) for the old head increment,
and \(y_{i,d}\) for the coefficients of the physical gain vector. The
nonsquarefree definition of \(y_i\) in Section 1 is needed for the uniform
identity \(c_{i,d}=b_{i,d}-b_{i+1,d}+h_{i,d}-y_{i,d}\).
Set

\[
 \begin{aligned}
 \mathcal D_N&=\sum_{i=N}^{2N-1}\sum_{d\in S_N}
       (b_{i+1,d}+\mu(d))(\eta_{i+1,d}-\eta_{i,d}),\\
 \mathcal W_N&=\sum_{i=N}^{2N-1}\sum_{d\in S_N}
       (h_{i,d}-y_{i,d})\eta_{i,d}.
 \end{aligned}
\]

Finite summation by parts, with the terminal coefficients
\(b_{2N,d}=-\mu(d)\), gives

\[
 \mathcal P_N=\sum_{d\in S_N}(b_{N,d}+\mu(d))\eta_{N,d}
                    +\mathcal D_N+\mathcal W_N
             =-H_N+\mathcal D_N+\mathcal W_N. \tag{13}
\]

For the last equality, expand
\(\langle\Phi_N,\Phi_N-F_N\rangle=H_N\). The charge multiplier cancels,
shared low coefficients cancel, high sources vanish, and the remaining band
coefficients are \(-\mu(d)-b_{N,d}\). This proves the boundary sign in (13).

In particular, another exact form of (11) is

\[
 \sum C_i=-H_N+\mathcal S_N+2\mathcal D_N+2\mathcal W_N
                       -\|\Delta_N^K-\mathcal Q_N\|^2. \tag{14}
\]

## 6. A quantitative source-variation inequality

Here \(N\ge2\). Bertrand's postulate supplies a prime \(N<p\le2N\).
It is odd, so \(t=2p\) is squarefree, divides \(L_N\), and satisfies
\(K<t\le4N\). The **composite** conductor \(t\) is a legal common anchor.
For \(d\in S_N\), put \(w_d=g_d-(t/d)g_t\).
The normal equations show \(\kappa_i=t\langle\Phi_i,g_t\rangle\), so

\[
 \eta_{i,d}=\langle\Phi_i,w_d\rangle,\qquad
 \eta_{i+1,d}-\eta_{i,d}=-\langle\delta_i,w_d\rangle,
 \quad \delta_i=\Phi_i-\Phi_{i+1}. \tag{15}
\]

The \(\delta_i\) belong to the mutually orthogonal spaces
\(T_{i+1}^K\cap(T_i^K)^\perp\). Put \(g_i=\|\delta_i\|^2\); then
\(\sum_i g_i=\|\Delta_N^K\|^2\). Apply finite Bessel to the nonzero
\(\delta_i/\sqrt{g_i}\):

\[
 \sum_{i:g_i>0}\frac{(\eta_{i+1,d}-\eta_{i,d})^2}{g_i}
       \le\|w_d\|^2. \tag{16}
\]

Zero \(g_i\) implies zero source difference, so no term is lost.
For \(n<d\), \(w_d(n)=0\); for all other \(n\),
\(|w_d(n)|\le t/d\). Since
\(\sum_{n\ge d}n^{-2}\le1/(d-1)\), by comparison with
\(1/(n(n-1))\),

\[
 \|w_d\|^2\le\frac{t^2}{\zeta(2)d^2(d-1)}
       \le\frac{16}{\zeta(2)(N+1)}. \tag{17}
\]

Consequently

\[
 \boxed{\displaystyle
 \sum_i|\eta_{i+1,d}-\eta_{i,d}|
    \le\frac{4\|\Delta_N^K\|}{\sqrt{\zeta(2)(N+1)}}.} \tag{18}
\]

This follows by weighted Cauchy--Schwarz in (16). It controls variation
**across periods at the fixed head K for a fixed conductor d**. It is not a
bound for adjacent-conductor differences at the moving actual head, nor does
it assert that \(\|\Delta_N^K\|\) is bounded.

There are at most \(N\) conductors in \(S_N\). A second Cauchy--Schwarz
application to (16)--(17), now over stages and conductors, proves

\[
 \boxed{\displaystyle
 |\mathcal D_N|\le\frac4{\sqrt{\zeta(2)}}\sqrt{\mathcal M_N},\qquad
 \mathcal M_N=\sum_{i=N}^{2N-1}g_i
                  \sum_{d\in S_N}(b_{i+1,d}+\mu(d))^2.} \tag{19}
\]

Indeed the sum of squared source differences divided by \(g_i\), over
both indices, is at most \(16/\zeta(2)\). This proves the displayed constant
without any count of prime stages, inverse-Gram hypothesis, or omission of
composite coefficients.

Keeping the exact signed equality (14) as the primary statement, a useful
finite upper bound is

\[
 \boxed{\displaystyle
 \sum C_i\le-H_N+\mathcal S_N+2\mathcal W_N
       +\frac8{\sqrt{\zeta(2)}}\sqrt{\mathcal M_N}
       -\|\Delta_N^K-\mathcal Q_N\|^2.} \tag{20}
\]

Only the source-drift term was bounded here. The signed work and the exact
negative square were retained.

## 7. What is still missing

For \(N=2^m\), equation (14) identifies the exact unresolved estimate as

\[
 \frac{\bigl[-H_N+\mathcal S_N+2\mathcal D_N+2\mathcal W_N
           -\|\Delta_N^K-\mathcal Q_N\|^2-B\bigr]_+}{1+E_N}\longrightarrow0
 \quad\text{for some fixed }B\ge0. \tag{21}
\]

The new variation estimate controls \(\mathcal D_N\) in terms of the
**actual coefficient-defect moment** \(\mathcal M_N\). No estimate such as
\(\mathcal M_N=o((1+E_N)^2)\) has been established. Nor is there a sufficient
signed bound for \(-H_N+\mathcal S_N+2\mathcal W_N\) against the retained
completion square. These are substantive arithmetic obligations.

An elementary pointwise coefficient extraction only gives a much weaker bound.
For \(j\in[N,2N]\), put \(R_j(n)=1-F_j(n)\). In this band,
\(b_{j,d}+\mu(d)=R_j(d)-R_j(d-1)\) and \(R_j(N+1)=0\). Therefore

\[
 \sum_{d\in S_N}(b_{j,d}+\mu(d))^2
       \le4\zeta(2)K^2\|1-F_j\|^2
       \le8\zeta(2)K^2(1+E_j).
\]

Since \(E_j\le\|\Phi_j\|^2\le E_N+H_N\), this yields only
\(\mathcal M_N\le8\zeta(2)K^2(1+E_N+H_N)\|\Delta_N^K\|^2\).
The factor \(K^2\), and the still uncontrolled head and period energies,
prevent this estimate from supplying the desired small normalized excess.
Thus ordinary Hilbert-space inequalities alone do not finish the argument.

## 8. Numerical check and verification record

The [reproducible diagnostics](MixedTrialLossTransportDiagnostics20261030.md)
use every divisor and complete periodic trigamma weights. On [4,8), they give

| Quantity | Exploratory value |
|---|---:|
| Actual certificate sum | 0.0426718896590010 |
| Actual energy increase | 0.0418278483678175 |
| Total unused loss | 0.0008440412911832 |
| Old repair energy \(\mathcal S_4\) | 0.0000001997017484 |
| \(\|\mathcal Q_4\|^2\) | 0.0008442409929315 |
| Raw cross pairing \(\langle r_4,r_5\rangle\) | 0.0000000914369503 |
| Transported cross pairing \(\langle q_4,q_5\rangle\) | about -3.3e-17 |
| Initial final-head repair \(H_4\) | 0.0581443386263468 |
| Signed work \(\mathcal S_4+2\mathcal P_4\) | 0.0001543040390631 |
| Remaining square \(\|\Delta_4^K-\mathcal Q_4\|^2\) | 0.0156267530064090 |

These are floating-point consistency checks, not rigorous numerical bounds.
Dropping the last square gives approximately 0.05829864, noticeably weaker
than the signed certificate 0.04267189. The paper identity does not itself
improve that numerical certificate.

Lean retry `job_jaLoqWLh0iqcPljrbo8giEQ0CtW0YGa5` returned terminal
`failed`, classification `wall_timeout`, exit code -9, reported run time
180.058 seconds, and `verified: false`. Its output contained dependency replay
warnings; no successful verification or axiom audit of the candidate resulted.
This is not a mathematical refutation. No additional long verification retry
was made after the user instructed continuation on paper if unresponsive.

Only documentation is submitted with this continuation. No new Lean source
is published. The earlier unverified arithmetic candidate remains unverified.
The repository's source-publication gate in `AGENTS.md` is not bypassed.

The finite orthogonality/Bessel ingredients already have general counterparts
in `Analysis/OrthogonalKernelScreening.lean` (`orthogonal_norm_sum` and
`weighted_bessel_finite`) and `Analysis/MovingOrthogonalEnergy.lean`.
The new arithmetic specializations and transport arguments above are paper
proofs. The short-anchor existence uses the standard theorem
[`Nat.exists_prime_lt_and_le_two_mul`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Bertrand.lean)
from Mathlib; retrieving that source is not a verification of this continuation.
