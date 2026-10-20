# CRT carry and signed-tail verification record — 19 October 2026

This continuation formalizes finite parts of the user's *CRT Carries and
Squarefree Residual Exhaustion* memorandum. Its Section 12 lists research
priorities; Section 13 is the verification and provenance ledger. Completing
that ledger does not discharge its last, explicitly open asymptotic row.
No unconditional RH conclusion is claimed here.

## Formal development and verification boundary

Nine subject modules extend and verify the earlier six-module draft:

| Module | Finite or explicitly conditional content |
|---|---|
| `Analysis/FiniteWeightedTailCharge` | Signed finite Fubini, energy/mass equality, absorption algebra, signed limiting charge under an energy-limit hypothesis. |
| `Analysis/FiniteGramBlockTrace` | Exact inverse-Gram gain and its full trace/score bound. |
| `Analysis/ConditionalGainGeometry` | Projection-energy decomposition, conditional score detection, and the obstruction to positive gain under legal invariance. |
| `Analysis/FiniteIncidenceTailCharge` | Generic incidence inversion, Jordan charge, centering, and exact square decomposition. |
| `RH/QCarryScreenedBlock` | Actual Q screening, representative invariance, full divisor-block span, and trace control. |
| `RH/QRationalCoprimeTail` | Correct rational weights, retained endpoint, residual moment, signed identity, and boundary lower bound. |
| `RH/QRationalCoprimeLegality` | Centered-prefix synthesis and assembly from every divisor normal equation. |
| `RH/QRationalCoprimeMinimum` | Existence of an actual minimizer, exact completion with the weighted remainder, and the signed identity without assumed normal equations. |
| `RH/QBoundedCollapseRate` | Complete-Q cutoff and quantitative collapse from explicit boundedness and head-slope hypotheses. |

Targeted server verification: job `job_pcJGiZt4X95YUSCwGIycW1r7dbr9EuXb`
succeeded with exit code 0 (16.399 seconds) under Lean 4.33.0-rc2. It built
or reused the nine new modules and printed axioms for eight principal
declarations, including `exists_signed_minimum`, `divisorFit_completion`,
`full_prime_block_stage`, and `carry_block_score_bound`. Each inspected
axiom list is exactly `propext`, `Classical.choice`, and `Quot.sound`.
The earlier six-module archive was unverified; this development supersedes
its proof drafts. Publication requires the separate server checkpoint audit
and validation; its terminal job and commit are reported in the session's
publication receipt. The targeted check alone is not a whole-project claim.

`QRationalCoprimeTail.exists_signed_minimum` has only the positive-period
hypothesis L>0. It proves the existence of real divisor coefficients satisfying
the normal equations, the signed identity, and global finite minimality.
The d=1 zero atom is retained: the projection argument allows a singular
dictionary. `divisorFit_completion` retains the exact nonnegative remainder
for every competing divisor fit. Rationality of coefficients is not formalized.

## The signed identity now uses the actual divisor equations

For a positive period L, define

    u_L(a) = 1/a^2 + 2/[L(2a+L)],       1 <= a <= L,
    R_L(a) = 1 - f(a),
    E_L = sum_a u_L(a) R_L(a)^2,
    T_L(k) = sum_{a=k}^L u_L(a) R_L(a),
    S_L = sum_{2<=k<=L, gcd(k,L)=1} T_L(k).

The finite normal equations give the complete identities

    E_L = T_L(1),
    sum_a a u_L(a) R_L(a) = 5/(3L),
    E_L + S_L = 5 phi(L)/(3L^2).

`QRationalCoprimeTail.signed_identity_of_divisor_synthesis` takes an actual
linear synthesis from every divisor of L and its divisor normal equations.
The zero endpoint and fitted-vector normal equation follow from that
synthesis; the centered-coprime-prefix normal equation follows from the
existing arithmetic declarations in `QPrimeSieve` and
`QMobiusPrimePacketArithmetic`. In particular, it is no longer an independent
hypothesis. For squarefree L, all those divisor atoms are legal squarefree
atoms. The exact theorem type and verification record above determine what
has been formally established; no asymptotic estimate is assumed here.

## Complete gcd-class charges and the location of the remaining error

An ordinary finite proof extends the last identity to every divisor e of L:

    B_e := sum_{1<=k<=L, gcd(k,L)=e} T_L(k)
         = 5 phi(L/e)/(3L^2).

Indeed, finite Fubini and each g_d normal equation give

    sum_{d|k, 1<=k<=L} T_L(k) = M/d,     M=5/(3L).

Divisor Möbius inversion gives B_e=(M/e) sum_{j|L/e} mu(j)/j, hence the
formula. The d=1 equation is direct; the e=L class retains T_L(L).
The generic finite inversion theorem is formalized. **The concrete all-gcd
Möbius specialization and its class-cardinality assembly are not yet Lean
bridges in this change.** The case e=1 is the concrete signed identity above.

Each class contains phi(L/e) positions, so all its tail averages equal
c_L=5/(3L^2). Set U_L(k)=T_L(k)-c_L. Then

    sum_{gcd(k,L)=e} U_L(k)=0,
    U_L(1)=E_L-c_L,
    sum_{k=1}^L T_L(k)^2 = L c_L^2 + sum_{k=1}^L U_L(k)^2.

Thus the divisor equations determine the component that depends only on the
gcd: it is constant. The unknown initial energy is a within-class
fluctuation. The generic centering and square identities are formalized;
this is an unweighted finite square decomposition, not the Q-energy of f.

Let P_L and N_L be the positive mass and the magnitude of the negative mass
of T_L on the noninitial coprime positions. The exact Jordan identity is

    S_L=P_L-N_L,
    N_L=E_L-5phi(L)/(3L^2)+P_L.

Every signed contribution remains visible. Positive class totals do not
bound N_L. Indeed, the linear class equations alone permit T(1)=A and a
second coprime value B_1-A for arbitrarily large A. This abstract example is
not asserted to satisfy the actual minimizer's energy and legality conditions.

## Full carry blocks and conditional leakage

For a fresh prime p, screen against W=V_L+R g_p and retain every d|L,d>1.
The representative-independent vectors are h_d=-R_W g_pd. With their Gram
matrix S and residual scores eta, the exact block gain is eta^T S^{-1} eta.
The finite bound is

    sum_d eta_d^2 <= tr(S) * blockGain,
    tr(S) <= [2/(zeta(2)p)] sum_{d|L,d>1} 1/d.

It does not provide a lower bound on the actual scores. Composite old
divisors cannot be omitted merely because pairwise prime carries are easier
to compute. Screened linear independence is still an explicit input to the
inverse-Gram application; its assembly for the complete block remains work.

For an actual nested optimizer increment h and old residual r, write
I=||h||^2, D=||r||^2, J=||C h||^2, with C the old cylinder projection. The
generic Hilbert identities give

    I=J+||h-C h||^2,       I^2<=D J,       J<=I.

The concrete Q-cylinder application remains an integration step. Legal
invariance of C h would force zero gain; it cannot justify positive gains.

## Remaining analytic obligations and finite evidence

The needed one-sided estimate is still open:

    S_L >= -theta E_L-epsilon_L,
    theta<1 fixed, epsilon_L -> 0.

The proved absorption algebra turns this into
E_L <= [5phi(L)/(3L^2)+epsilon_L]/(1-theta). For actual Q projection errors,
another sufficient cumulative target is divergence of the relative gains
(D_M-D_{M+1})/D_M. Finite identities, positive individual gains, and bounded
approximants alone do not establish either target.

Other formalization gaps remain explicit: construction and product bounds
of the full Haar optimizer; specializing the generic cutoff to its chosen
integer cutoff; complete rational-to-Q upper-weight comparison and limiting
projection convergence; the Q-cylinder specialization; and complete screened
independence assembly. The general collapse bound retains the entire
inverse-square tail and does not transfer the Haar optimizer into an RH proof.

Wolfram exact checks cover the signed finite identities at L=2,6,30,210.
Python Fraction checks cover L=2,6,30, including all gcd-class charges,
Jordan mass, and centered-square identities. At L=30 the noninitial coprime
tails are all negative. These finite computational checks are separate from
Lean verification and establish no asymptotic bound. The complete standalone standard-library script and exact JSON outputs
are preserved in `CRTCarryGcdChecks20261019.md`.

## Primary-source context

Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of
the Riemann hypothesis* (2006), [Remark 8 and the weight-comparison discussion](https://arxiv.org/pdf/math/0607733),
support the discrete squarefree closed-span criterion and comparison of
weights. They supply no unconditional vanishing estimate for these tails.

Alouges, Darses, and Hillion, *Polynomial approximations in a generalized
Nyman–Beurling criterion* (2022), [article](https://numdam.org/articles/10.5802/jtnb.1227/),
provides context for separating approximation from coefficient and Gram
control. No RH conclusion is imported. The specialized CRT and signed-tail
arguments originate in the user's memorandum and this continuation; no
novelty claim is made for the underlying standard identities.

## Reproducible Wolfram all-class check

The following exact-arithmetic evaluation returned `True` at every displayed
period. It checks finite arithmetic independently of the Lean proof chain.

```wl
Table[Module[{ds = Rest[Divisors[L]], w, j, c, r, t},
  w = Table[1/a^2 + 2/(L (2 a + L)), {a, 1, L}];
  j = Table[Mod[a, d]/d, {a, 1, L}, {d, ds}];
  c = LinearSolve[Transpose[j].DiagonalMatrix[w].j, Transpose[j].w];
  r = 1 - j.c;
  t = Reverse[Accumulate[Reverse[w r]]];
  {L, And @@ Table[
    Total[Pick[t, Table[GCD[k, L] == e, {k, 1, L}]]] ==
      5 EulerPhi[L/e]/(3 L^2), {e, Divisors[L]}]}
], {L, {2, 6, 30, 210}}]
(* {{2, True}, {6, True}, {30, True}, {210, True}} *)
```
