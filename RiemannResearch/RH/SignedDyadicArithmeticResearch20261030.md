# Signed dyadic arithmetic from complete divisor normal equations

Prepared 30 October 2026. Source snapshot: RiemannResearch main at
3457cc758849b09d33ea428b64f087897d274e2b.
This continues [ScreenedMixedTrialResearch20261030.md](ScreenedMixedTrialResearch20261030.md).
The screening transport and determinant proofs are used, not repeated.

## Result and scope

There is an exact cancellation across an entire block of the actual moving
optimizers. The charge multiplier and every shared low-conductor coefficient
cancel. Only the newly imposed conductor band remains in an endpoint dual
pairing. In a dyadic block [N,2N), every squarefree conductor in that band
already belongs to the initial dictionary.

Both mixed sources are expanded below through every divisor and the actual
normal equations. The resulting block identity retains negative period gains,
nonprime head costs, an endpoint distance square, and the accumulated exact
mixed-trial loss. A positive-part sandwich separates endpoint growth from unused
trial loss. A further squarefree-band difference-energy completion gives an
explicit finite upper bound, retaining a head square and a physical tail square.

**The normalized dyadic limit is not proved, and RH is not proved.**
The new reduction supplies no asymptotic bound on the endpoint pairing or loss.
These are paper proofs; the final verification section records their Lean status.

## 1. Definitions and complete dictionary

For n >= 1, Q(n)=1/(zeta(2)n^2), and g_d(n)=(n mod d)/d. All inner products and
norms use the complete infinite Q measure.

Put L_i=primorial(2i+2), D_i={d>1:d divides L_i}, and
U_i=span{g_d:d in D_i}. Every composite squarefree divisor is included.

F_i is the unique minimum-norm vector in U_i equal to one on 1,...,i+1, and
E_i=||F_i||_Q^2. Write

\[
F_i=\sum_{d\in D_i}b_{i,d}g_d.
\]

The g_d for distinct d>1 are independent. Extend b_{i,d} by zero outside D_i.
Removing g_1=0 fixes the otherwise irrelevant coefficient ambiguity.

Existing exact-head coefficient extraction gives

\[
\sum_{d\in D_i}\frac{b_{i,d}}d=1,\qquad
b_{i,d}=-\mu(d)\quad(2\le d\le i+1,\ d\in D_i).
\tag{1}
\]

The next physical mismatch is b_{i,i+2}+mu(i+2), with the zero-extension
convention. The repository already proves this extraction; it is not a new
arithmetic estimate.

For an arbitrary head H in a fixed dictionary of period L, write F for the
actual minimum, define

\[
\kappa=L\langle F,g_L\rangle_Q,\qquad
\eta_d=\langle F,g_d\rangle_Q-\kappa/d.
\tag{2}
\]

The compensated direction w_d=g_d-(L/d)g_L belongs to the same dictionary and
vanishes on the first H sites whenever H<d and H<L. Stationarity therefore gives

\[
\boxed{\eta_d=0\quad(d\mid L,\ d>H).}
\tag{3}
\]

This is the actual full-dictionary normal equation. In matrix form,
G_L b = kappa (1/d)_d + eta, with eta supported on conductors d<=H.
No inverse-Gram estimate and no prime-only restriction is used.

## 2. Both mixed sources in full divisor coordinates

At an eligible stage let p=2i+3, L=L_i, and let Fhat_i be the old-dictionary
minimum with head i+2. Its full coefficients are bhat_e. Define

\[
\widehat\kappa_i=L\langle\widehat F_i,g_L\rangle_Q,\qquad
G(e,f)=\langle g_e,g_f\rangle_Q
=\frac1{\zeta(2)}\sum_{n\ge1}\frac{g_e(n)g_f(n)}{n^2},
\]
\[
r_{i,d}
=\langle\widehat F_i,g_{pd}-(L/(pd))g_L\rangle_Q
=\sum_{e\in D_i}\widehat b_{i,e}G(e,pd)
 -\frac{\widehat\kappa_i}{pd},
\quad d\mid L,\quad d\ge1.
\tag{4}
\]

All sums over conductors are finite; the displayed Gram entries contain the
entire infinite physical tail. The d=1 source is essential.

Let h_i and q_i be the screened floor and compensated-prime directions from
QCRTMixedFloorTrial, and let u_i=<Fhat_i,h_i>, v_i=<Fhat_i,q_i>.
Source preservation, the exact identity
D_p g_d=g_{pd}-g_p/d, and (1) give

\[
\boxed{v_i=r_{i,1},\qquad
u_i=\sum_{d\in D_i}b_{i,d}r_{i,d}-r_{i,1}.}
\tag{5}
\]

Thus the compensated-prime coefficient of D_p F_i is exactly -1 in normalized
coordinates. The original convention allowing a nonzero g_1 coefficient gives
b_1-sum_{d|L}b_d/d=-1 and yields the same vector.

Writing both sources entirely with Gram entries gives

\[
u_i=\sum_{e\in D_i}\widehat b_{i,e}
 \left(\sum_{d\in D_i}b_{i,d}G(e,pd)-G(e,p)\right),
\]
\[
v_i=\sum_{e\in D_i}\widehat b_{i,e}G(e,p)
 -\widehat\kappa_i/p.
\tag{6}
\]

The old multiplier cancels from u_i. It remains in the compensated-prime source
v_i and cannot be discarded. Splitting off the forced low coefficients yields

\[
u_i=-v_i-\sum_{\substack{d\in D_i\\d\le i+1}}\mu(d)r_{i,d}
 +\sum_{\substack{d\in D_i\\d>i+1}}b_{i,d}r_{i,d}.
\tag{7}
\]

The last sum contains the actual moving tail coefficients. Replacing them by
Möbius coefficients would replace the actual optimizer by a different vector.

## 3. Exact cross-stage cancellation

Take 1<=M<=N. Embed the initial coefficients b_M into D_N by zero extension,
and let

\[
\kappa_N=L_N\langle F_N,g_{L_N}\rangle_Q,\qquad
\eta_{N,d}=\langle F_N,g_d\rangle_Q-\kappa_N/d.
\]

Define the endpoint pairing and distance

\[
T_{M,N}=
-\sum_{\substack{d\in D_N\\M+1<d\le N+1}}
   (b_{M,d}+\mu(d))\,\eta_{N,d},\qquad
D_{M,N}=\|F_N-F_M\|_Q^2.
\tag{8}
\]

Then

\[
\boxed{T_{M,N}=\langle F_N,F_N-F_M\rangle_Q,}
\tag{9}
\]
\[
\boxed{E_N-E_M=2T_{M,N}-D_{M,N}.}
\tag{10}
\]

### Proof

Let delta_d=b_{N,d}-b_{M,d} in the common full dictionary D_N. Equation (1)
implies sum delta_d/d=0. Hence

\[
\langle F_N,F_N-F_M\rangle
=\sum_{d\in D_N}\delta_d(\eta_{N,d}+\kappa_N/d)
=\sum_{d\in D_N}\delta_d\eta_{N,d}.
\]

For d<=M+1, the two coefficients agree by exact-head extraction. For d>N+1,
eta_{N,d}=0 by the final moving normal equations. On the remaining band,
delta_d=-mu(d)-b_{M,d}. This proves (9). Expanding the full squared distance
proves (10). Every removed term vanishes exactly; no sign estimate was used.

For N=2M, every squarefree d with M+1<d<=2M+1 divides
primorial(2M+2)=L_M. Thus (8) uses actual initial-dictionary coefficients in
that band. It is not necessary to introduce hypothetical coefficients of
future conductors.

This reduces an all-stage cancellation problem to one signed sum over the
newly imposed head band. The high composite conductors still affect the
optimizer coefficients and dual sources through the full Gram solve.

## 4. Exact mixed certificate accounting and an inequality

Let C_i=fullCertificate actualTrials i and ell_i=fullLoss actualTrials i.
The existing exact transition is

\[
C_i=E_{i+1}-E_i+\ell_i,\qquad \ell_i\ge0.
\]

For every finite block, set L_{M,N}=sum_{i=M}^{N-1}ell_i. Combining its exact
telescope with (10) gives

\[
\boxed{
\sum_{i=M}^{N-1} C_i
=2T_{M,N}-D_{M,N}+L_{M,N}.
}
\tag{11}
\]

The left side still includes all stages: at eligible squarefree prime stages
the old head cost minus mixed gain, at other squarefree stages the old head
cost, and at nonsquarefree sites the exact negative period gain. Equation (11)
does not omit those costs or replace a loss square by zero.

For N=2^m, let Delta_m=E_{2N}-E_N, L_m=L_{N,2N}, W_m=1+E_N. For every real B,

\[
\boxed{
\frac{(\Delta_m-B)_+}{W_m}
\le R_m
\le
\frac{(\Delta_m-B)_+}{W_m}+\frac{L_m}{W_m}.
}
\tag{12}
\]

Proof: W_m>0, L_m>=0, and
x_+ <= (x+L_m)_+ <= x_+ + L_m. Use (11), or equivalently the exact certificate
telescope, with x=Delta_m-B.

Thus a sufficient pair of estimates is

\[
\frac{(2T_{N,2N}-D_{N,2N}-B)_+}{1+E_N}\to0,
\qquad
\frac{L_{N,2N}}{1+E_N}\to0
\quad(N=2^m).
\tag{13}
\]

This is a sufficient decomposition, not an equivalence: a negative energy
increment may compensate a positive loss in the original target. The stronger
condition T_{N,2N}=o(1+E_N) is not needed. Keeping -D_{N,2N} matters.

## 5. A squarefree-band difference energy

There is a further finite inequality on a dyadic block. This part is proved
on paper; the current Lean candidate formalizes the endpoint reduction and
sandwich, not the arithmetic grouping in this subsection.

Fix M>=1, put K=2M+1, and list every squarefree integer in (M+1,K] as
r_1<...<r_s. Put r_(s+1)=K+1, eta_j=eta_(2M,r_j), eta_(s+1)=0, and

\[
a_j=b_{M,r_j}+\mu(r_j),\quad
z_j=\sum_{k\le j}a_k,\quad
\gamma_j=\eta_{j+1}-\eta_j,\quad
W_j=\sum_{n=r_j}^{r_{j+1}-1}Q(n)>0.
\tag{14}
\]

All r_j, including composites, already divide L_M. For r_j<=n<r_(j+1),

\[
\boxed{1-F_M(n)=z_j.}
\tag{15}
\]

Before r_1 and after M+1 this residual is zero. To prove (15), expand F_(2M)-F_M
in the common final dictionary. Its charge is zero, and its coefficients at
d<=M+1 are zero. For M+1<d<=K and n<=K<2d, floor(n/d) is exactly 1 if d<=n and
0 otherwise. The coefficients in this band are -a_j, while conductors above K
have floor(n/d)=0. The formula g_d(n)=n/d-floor(n/d) gives (15).

Discrete summation by parts, with z_0=0 and eta_(s+1)=0, now gives

\[
T_{M,2M}=-\sum_{j=1}^s a_j\eta_j
       =\sum_{j=1}^s z_j\gamma_j.
\]

Define

\[
V_M=\sum_{j=1}^s\frac{\gamma_j^2}{W_j},\qquad
A_M=\sum_{j=1}^s W_j\left(z_j-\frac{\gamma_j}{W_j}\right)^2,
\qquad
J_M=\sum_{n>K}Q(n)|F_{2M}(n)-F_M(n)|^2.
\tag{16}
\]

The full endpoint distance is sum_j W_j z_j^2 + J_M. Completing every scalar
square in (10) therefore gives the exact identity

\[
\boxed{E_{2M}-E_M=V_M-A_M-J_M,}
\]
\[
\boxed{\sum_{i=M}^{2M-1}C_i
       =V_M-A_M-J_M+L_{M,2M}.}
\tag{17}
\]

All three V_M, A_M, J_M are nonnegative. Empty bands use empty sums; then the
head difference vanishes and the same identity holds with V_M=A_M=0.

In particular, this proves the finite, explicit inequalities

\[
\boxed{E_{2M}-E_M\le V_M,\qquad
       \sum_{i=M}^{2M-1}C_i\le V_M+L_{M,2M}.}
\tag{18}
\]

No lower bound on a Gram determinant is needed in this proof. V_M is a weighted
difference energy of the actual final dual sources on consecutive squarefree
conductors. It contains composite conductors and the final boundary
gamma_s=-eta_s. Omitting that boundary changes the identity.

A sufficient arithmetic provider for the original RH consumer is

\[
\frac{(V_{2^m}+L_{2^m,2^{m+1}}-B)_+}{1+E_{2^m}}\longrightarrow0.
\tag{19}
\]

This is stronger than the original signed target, because it discards
-A_M-J_M. No estimate of (19) is claimed. The exact version (17) should be kept
if V_M alone is too large.

For [4,8), the exploratory values are V_4 approximately 0.054066501509,
A_4 approximately 0.000748376414, and J_4 approximately 0.011490276727.
Thus V_4-A_4-J_4 approximately 0.041827848368. This confirms the finite
completion's signs and its nonzero boundary; it does not certify those numbers.

## 6. Numerical check of the endpoint cancellation

The existing complete-period floating-point diagnostic was extended to compute
kappa, eta, the band pairing, and the endpoint distance. Trigamma weights retain
the full infinite tail. These are exploratory checks, not interval inequalities.

| Block | T | Endpoint distance squared | 2T minus distance squared | Sum of mixed losses |
|---|---:|---:|---:|---:|
| [1,2) | 0.135977766650 | 0.204967339945 | 0.066988193355 | 0.020872561532 |
| [2,4) | 0.020811603705 | 0.034879590239 | 0.006743617170 | 0.000000000000 |
| [4,8) | 0.048807716199 | 0.055787584031 | 0.041827848368 | 0.000844041291 |

In the last block, the only squarefree conductors in 5<d<=9 are 6 and 7:

| Conductor d | -(b_(4,d)+mu(d)) eta_(8,d) |
|---|---:|
| 6 | 0.049708987840 |
| 7 | -0.000901271641 |

Consequently
2(0.048807716199)-0.055787584031+0.000844041291
=0.042671889659, reproducing the stated global adjusted certificate.
The largest endpoint identity discrepancy in these three blocks is about
9.2e-15. Such numerical agreement checks signs and conventions; it is not a
rigorous error bound or evidence of a limiting rate.

For reproduction, use the Python definitions in
[ScreenedMixedDiagnostics20261030.md](ScreenedMixedDiagnostics20261030.md),
then evaluate the endpoint calculation recorded in [EndpointSourceDiagnostics20261030.md](EndpointSourceDiagnostics20261030.md). The original dictionary and solver are unchanged.

## 7. Precise remaining arithmetic obstruction

With N=2^m the required estimate is exactly

\[
\boxed{
\frac{(2T_{N,2N}-D_{N,2N}+L_{N,2N}-B)_+}{1+E_N}\to0
\quad\hbox{for some fixed }B\ge0.
}
\tag{20}
\]

Neither (1), the full normal equations, nor finite determinant positivity
supplies this estimate. They give identities and finite solvability. They do not
control the signed correlation between initial coefficient defects
b_(N,d)+mu(d) and final dual sources eta_(2N,d), relative to the retained
endpoint square and the accumulated unused trial loss.

There are two concrete places where a proposed proof would need new input:

1. Bound the signed band pairing together with its negative endpoint square.
   Estimating sum |b_(N,d)+mu(d)| |eta_(2N,d)| separately discards the cancellation
   present already in the d=6,7 diagnostic. A global trace estimate for a Gram
   matrix does not control its inverse or these moving sources.
2. Control the sum of the exact omitted full-family losses for the selected
   two-direction trials, or retain their compensation by negative block energy.
   The losses are nonnegative; stationarity within two directions does not
   assert they are small in the complete added-conductor space.

Ordinary Cauchy-Schwarz gives upper bounds on source magnitudes. It does not give
the lower bound on captured gain needed to pay the old head costs. No such
alignment or signed dyadic bound has been established here.

## 8. Verification and continuation

Workspace token: ws__Qb1Z-i82qGmkP3NMOXzkew20wofuX11.
Server root:
/home/cri_2025/lean-agent-workspaces/ws__Qb1Z-i82qGmkP3NMOXzkew20wofuX11/RiemannResearch.

**No new result in this continuation is Lean-verified.** The mathematical
statements above have paper proofs. Numerical checks and Wolfram algebra
checks are independent diagnostics, not kernel verification.

The first network submission timed out without a job; bounded job recovery
confirmed an empty queue for that workspace. Accepted checks then terminated:

| Job | Scope | Reported wall time | Result |
|---|---|---:|---|
| job_o4F5jSkH05iv9XZCZ8HGJPvlsMYtTwJo | divisor sources and tail normal equations | 120.053 s | wall_timeout, exit -9 |
| job_WqAMKLvGA2hwDpLHrAJutrTsYefJivec | revised source candidate | 300.048 s | wall_timeout, exit -9 |
| job_pCOcoJPjWG5PL0vHK-JKFc4SBVFQygJY | full source, endpoint, and sandwich candidate | 900.059 s | wall_timeout, exit -9 |
| job_AWrJqlS0nw3qQrcrLR3iEdBOezP2JnJp | isolated Mathlib-only weighted completion | 120.037 s | wall_timeout, exit -9; empty output |

The retained output from the full checks ends in dependency replay warnings.
No successful theorem diagnostics or axiom audit was returned. These are
server-reported wall durations, not measurements of kernel proof-checking
time. The logs do not establish the underlying cause of the execution delay.
A timeout is not a mathematical refutation.

The complete arithmetic candidate is preserved separately as
QCRTMixedSourceArithmetic_UNVERIFIED.lean. It proposes
mixed_source_divisor_sum, rawSource_gram, minimumAt_tail_normal,
normalized_mixed_source, endpoint_coefficient_balance,
actual_endpoint_balance, signed_certificate_endpoint, and
normalized_excess_sandwich. The grouped difference-energy argument of
Section 5 is not claimed to be formalized by that candidate.

Publication scope is documentation only: this memorandum, the reproducible
diagnostics, and the catalog status entry. No Lean source or dependency change
is published, and a documentation-only checkpoint is not a mathematical
verification.

The next substantive arithmetic task is to control the final dual-source
differences and boundary in (16), together with the unused full-family loss.
If V_M alone is too large, retain both negative squares in (17). Before another
Lean attempt, resolve the execution blocker using this retained workspace;
do not treat any of these timed-out submissions as checked declarations.

## 9. Sources

- The supplied screened-mixed memorandum and its three Lean modules establish
  the existing trial construction, exact accounting, and conditional RH consumer.
- QCRTPeriodHeadBalance.minimumAt and its completion theorem define the actual
  minimum. QResidueHeadSpace supplies the full finite dictionary and tangent.
- NormalizedResidueExactHeadCharges supplies exact coefficient extraction,
  reciprocal charge one, and the next-coefficient mismatch identity.
- The endpoint cancellation above is derived directly in this continuation.
  No external asymptotic theorem is assumed.
- Wolfram expanded the symmetric finite Gram polarization identity to zero.
  This checks algebra only; it is not a Lean kernel certificate.
