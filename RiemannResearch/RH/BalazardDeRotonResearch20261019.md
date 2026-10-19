# Balazard--de Roton: signed critical-line error and the discrete charge

Date: 19 October 2026 UTC (18 October in the user's timezone).

## Source and scope

The attached `swe.pdf` is the 20-page paper by Michel Balazard and Anne de
Roton, *Sur un critère de Báez-Duarte pour l'hypothèse de Riemann*,
[arXiv:0812.1689](https://arxiv.org/abs/0812.1689).
All twenty pages were read; the displays on pages 18--19 were also rendered
and inspected. The upload has an arXiv v1 margin date of 9 December 2008 and
an internal title-page date of 8 November 2018. Those are source metadata,
not dates of a new theorem in this project.

The paper's main theorem is RH-conditional:

    d_N^2 <<_delta (log log N)^(5/2+delta) / sqrt(log N),  delta>0.

Its main analytic inputs are J_epsilon << epsilon and a quantitative
reciprocal-zeta truncation estimate I_(N,epsilon) << N^(-epsilon/2),
in the small-damping regime relevant to the chosen diagonal.

This update does not prove RH, does not formalize those difficult analytic
inputs, and does not improve the best known exponent. It makes the exact
finite split usable in the actual squarefree Pareto/Q development and
preserves the signed energy discarded in Proposition 1.

## Existing results used, rather than reproved

The inspected baseline is b95a634bbf42bc8128536474bf7850d70edd27d6.

- `DampedMobiusSquarefreeClosure.lean`: actual finite squarefree legality.
- `DampedMobiusHardyBridge.lean`: exact interior Mellin formula, Hardy norm
  equivalence, finite-residual critical-line Plancherel identity, and the
  conditional approximation-to-RH/Q-closure consumers.
- `BaezDuarteNaturalApproximation.lean`: complete exterior charge squared
  and the established factor-two centering comparison.
- `BaezDuarteCellEnergy.lean` and
  `BaezDuarte2002Research20261018.md`: the five-fourths moment comparison,
  with its still-separate full continuous partition identification.

The present work does not relabel the unfinished five-fourths bridge as
proved. The new critical-line route uses the already proved exact physical
Plancherel theorem directly.

## What the paper actually estimates

In H=L2((0,infinity),dt/t^2), put e_d(t)={t/d} and chi=1_[1,infinity).
For N>=1,

    M_(N,epsilon)(s)=sum_(1<=d<=N) mu(d)d^(-epsilon)d^(-s),
    A_(N,epsilon)=sum_(1<=d<=N) mu(d)d^(-1-epsilon).

The paper's natural residual has Mellin transform

    R_nat(s)=[1-zeta(s)M_(N,epsilon)(s)]/s.

Write

    B_epsilon(s)=[1-zeta(s)/zeta(s+epsilon)]/s,
    T_nat(s)=zeta(s)/s*[1/zeta(s+epsilon)-M_(N,epsilon)(s)].

Then R_nat=B+T_nat exactly. On the critical line with measure dt/(2*pi),
I=||T_nat||^2 and J=||B||^2. When both components belong to L2,

    nu=I+J+2 Re<B,T_nat>,
    2(I+J)-nu=||B-T_nat||^2,
    (sqrt(I)-sqrt(J))^2 <= nu <= (sqrt(I)+sqrt(J))^2.

The last bounds follow from the triangle and reverse triangle inequalities.
They sharpen the numerical bound 2I+2J without changing the asymptotic
exponent or eliminating RH. In particular, if I/J -> 0 then nu/J -> 1.
Using the paper's J >> epsilon observation and its upper bound for I,
this applies to its sufficiently small diagonal
epsilon=25*(log log N)^(5/2+delta)/sqrt(log N).
This asymptotic observation is an ordinary argument here, not an additional
Lean theorem about zeta.

## The correction needed in our discrete spaces

Our legal finite vector is

    F_(N,epsilon)(n)=-sum_(1<=d<=N) mu(d)d^(-epsilon)g_d(n),
    g_d(n)=(n mod d)/d.

Its Pareto Mellin transform is zeta(s)/s*[M_(N,epsilon)(s)-A_(N,epsilon)].
Consequently its residual is

    R_P(s)=[1-zeta(s)(M_(N,epsilon)(s)-A_(N,epsilon))]/s
          = B_epsilon(s)+T_P(s),

    T_P(s)=zeta(s)/s*[1/zeta(s+epsilon)-M_(N,epsilon)(s)+A_(N,epsilon)].

Omitting A changes the approximant and the energy problem. It is not a
harmless convention. The new Lean code retains it literally.

For every finite N and real epsilon the exact identity is

    ||1-F_(N,epsilon)||_P^2
      = (1/(2*pi))*integral_R |B_epsilon(1/2+it)+T_P(1/2+it)|^2 dt.

The finite residual is genuinely square integrable independently of RH.
Separate square integrability of B and T_P is required before splitting
their integrals; it is not inferred merely from the finite sum. This also
avoids Lean's totalized Bochner-integral pitfall for nonintegrable functions.

The support is still squarefree because the unchanged coefficients vanish
when mu(d)=0. No nonlinear product or infinite conductor is called legal.

## Lean additions

`ParetoBoundedMellin.lean` proves ordinary Mellin integrability and finite
linearity on Re(s)>0 for bounded physical sequences. It also evaluates the
constant target there. These are unconditional analytic results; boundedness
is supplied explicitly, and the finite damped application proves its bound.

`BalazardDeRotonCriticalEnergy.lean` identifies the actual corrected finite
Mellin residual all the way to the critical line, proves its complete
infinite norm identity, and proves that arbitrarily small such single-line
energies are equivalent to the existing `DampedHardyApproximation` property.
The same hypothesis implies Mathlib's `RiemannHypothesis` and actual
squarefree Q closure through the existing verified consumers.

The signed-energy declarations additionally retain the mixed term and the
nonnegative parallelogram remainder under explicit component L2 hypotheses.
They do not assert that a favorable signed budget is available.

## Source cautions

The uploaded page 18, Proposition 13 display (16), prints zeta(s+epsilon)
where its proof, definition (17), and the definition of I require
1/zeta(s+epsilon). The last integral in the proof on page 19 repeats the
missing inverse. The formal transcription uses the reciprocal consistently.

The displayed high-frequency calculation actually yields

    tail << N^(-1/8)*log N,

and hence the paper's weaker N^(-1/9) bound for large N. Combining the printed
N^(-1/9) and N^(-epsilon/2) estimates directly requires epsilon<=2/9;
the chosen diagonal eventually satisfies this, so it suffices for the main
theorem. We do not infer an unrestricted uniform damping range from those
two estimates. The occurrences of delta versus 6*delta are reconciled by
renaming the arbitrary positive parameter.

## RH-focused next steps and dependency ledger

Established here: finite squarefree candidates retain the full charge; the
actual critical-line norm is identified; the conditional single-line
consumer reaches the existing RH and Q-closure theorems; signed energies
can be retained exactly whenever their components are L2.

Open: prove a sequence of complete corrected critical-line energies tending
to zero without assuming RH. This is the substantive arithmetic/analytic
obligation. Positivity of damping, finite-head matching, and pointwise
coefficient convergence do not discharge it.

1. Use the signed formula to study the mixed bias/truncation/charge energy,
   rather than immediately replacing it by positive diagonal bounds.
2. Separate a paper-faithful RH-to-approximation formalization from an
   unconditional RH attempt. The former must explicitly assume RH and
   prove the reciprocal-zeta, typical-ordinate, and Perron estimates.
3. Retain both the head and the complete infinite physical tail in any
   computational experiment. Finite numerical cancellation is not a bound
   on the infinite norm.
4. Do not seek a better power of epsilon for this same J by elementary
   domination alone: the paper already notes the lower bound J >> epsilon
   from a simple critical-line zero. A better N rate requires better
   truncation control, a different family, or additional signed structure.

## Verification

Publication is gated by server verification of the changed modules and
their affected dependencies. No project-local axioms or admitted proofs
are introduced. The terminal checkpoint result, rather than this document,
is the authoritative record of the verified commit and validation scope.

## Further ordinary theorem: sharp asymptotic P/Q transfer

This section is an ordinary mathematical proof, not an additional Lean
declaration in this update. It retains RH explicitly.

Fix delta>0, put

    epsilon_N=25*(log log N)^(5/2+delta)/sqrt(log N),

and take the exact squarefree damped finite vector F_(N,epsilon_N).
Let nu_N be the paper's natural squared error, J_N=J_(epsilon_N), and
E_P(N), E_Q(N) the complete probability-normalized discrete squared errors.
Then, assuming RH,

    nu_N/J_N -> 1,
    E_P(N)/J_N -> 1,
    zeta(2)*E_Q(N)/J_N -> 1.

Thus the discrete transfer for this particular diagonal has leading
constant 1 in P and 1/zeta(2) in Q. This does not improve the logarithmic
exponent or determine a leading constant for J_epsilon/epsilon.
It is stronger than a fixed global norm-comparison factor for these
specific errors; no priority claim is made.

Proof:

1. The paper gives J_N asymptotic in order to epsilon_N: its RH upper
   bound is Proposition 2, and the lower bound J_epsilon >> epsilon is
   noted on page 8 from a critical-line zero. Proposition 3 gives
   I_N << N^(-epsilon_N/2). Hence I_N/J_N -> 0, and the triangle and
   reverse triangle inequalities give nu_N/J_N -> 1.

2. The complete reciprocal charge satisfies, unconditionally for epsilon>0,

       |A_(N,epsilon)-1/zeta(1+epsilon)|
         <= sum_(d>N) d^(-1-epsilon) <= N^(-epsilon)/epsilon.

   On the displayed diagonal, N^(-epsilon_N)/epsilon_N is smaller than
   every fixed positive power of epsilon_N. The Laurent expansion at one
   therefore gives A_(N,epsilon_N)=epsilon_N+O(epsilon_N^2).

3. In the continuous t model set

       R_N(t)=chi(t)+sum_(d<=N) mu(d)d^(-epsilon_N)e_d(t),
       S_N(t)=R_N(t)-A_(N,epsilon_N)e_1(t).

   For 0<t<1, S_N(t)=0. On each cell n<=t<n+1 with n>=1,
   S_N(t)=1-F_(N,epsilon_N)(n), apart from irrelevant cell endpoints.
   Consequently ||S_N||_H^2=E_P(N). Also K=||e_1||_H^2 is finite:
   the integral on (0,1) is 1 and the integral on (1,infinity) is at most 1.
   The exact equality, retaining its signed term, is

       E_P(N)=nu_N-2*A_(N,epsilon_N)*<R_N,e_1>_H
                    +A_(N,epsilon_N)^2*K.

   Cauchy--Schwarz now yields
   |E_P(N)-nu_N| <= 2*|A_(N,epsilon_N)|*sqrt(K*nu_N)
                         +A_(N,epsilon_N)^2*K
                    = O(epsilon_N^(3/2)).
   Since J_N >> epsilon_N, this proves E_P(N)/J_N -> 1.

4. Write r_N(n)=1-F_(N,epsilon_N)(n). For each fixed positive n and N>=n,

       r_N(n)=1-sum_(d<=n) mu(d)d^(-epsilon_N) floor(n/d)
                  +n*A_(N,epsilon_N).

   The finite floor sum equals 1 at epsilon=0 and is differentiable there.
   More precisely, the divisor identity
   sum_(d|m) mu(d)log(d)=-Lambda(m) gives

       r_N(n)/epsilon_N -> n-psi(n),
       psi(n)=sum_(m<=n) Lambda(m).

   Indeed the derivative of the finite damped floor sum at zero is psi(n),
   and A_(N,epsilon_N)/epsilon_N -> 1. This pointwise head limit itself is
   unconditional for the displayed diagonal; it does not assert an L2
   limit of the normalized errors. In particular r_N(n)=O_n(epsilon_N),
   and for each fixed H the contribution of n<=H to either squared error
   is O_H(epsilon_N^2).

5. The exact difference of the probability weights gives

       zeta(2)*E_Q(N)=E_P(N)+D_N,
       D_N=sum_(n>=1) r_N(n)^2/[n^2(n+1)].

   For every fixed H>=1,

       0 <= D_N <= O_H(epsilon_N^2)+E_P(N)/(H+1).

   Divide by E_P(N), which has order epsilon_N by step 3.
   First let N tend to infinity, then H tend to infinity.
   This proves D_N/E_P(N)->0 and hence
   zeta(2)*E_Q(N)/E_P(N)->1, completing the proof.

All physical tails remain in these identities. The argument uses escape
of the *normalized error energy* from every finite head, not just pointwise
convergence of the errors. A future formalization can reuse
`critical_energy` and the existing exact P/Q weight identities; the
RH-conditional providers from the paper still need separate formalization.
