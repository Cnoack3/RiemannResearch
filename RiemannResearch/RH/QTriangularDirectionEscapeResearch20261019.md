# Triangular target charge and escaping inverse-Gram directions

Date: 19 October 2026.

## Result

The proposed mixed-direction route from Section 11 of
BalazardTriangularResearch20261019.md does not work for the natural
primorial divisor dictionaries: its normalized target capture tends to
zero, not one. This is an unconditional theorem in the actual complete
Q Hilbert space. It does not rule out squarefree approximation by the full
dictionary, and it does not prove or disprove RH.

Source: the user-directed review of Michel Balazard,
*An arithmetical function related to Baez-Duarte's criterion for the
Riemann hypothesis*, arXiv:1812.04309, supplies the triangular-dual
background. The scalar projection and weak escape argument below were
developed from standard Hilbert geometry in this continuation; no
mathematical novelty claim is made.

## Exact arithmetic target charge

Write m(j)=sum_{d<=j} mu(d)/d and
tau_N=N^{-1} sum_{0<=j<N} m(j), with the usual zero convention at N=0.

QTriangularTargetMean.lean proves, with the repository's positive Riesz sign,

    charge N qOne = tau_N
    tau_N = m(N) - N^{-1} sum_{1<=d<=N} mu(d)
    e_N = tau_N^2 + N^{-1} sum_{0<=j<N} (m(j)-tau_N)^2.

The variance is nonnegative, so tau_N^2<=e_N. The limit tau_N->0 uses
the existing unconditional PNT-based reciprocal-Mobius cancellation.
This closes the previously unformalized arithmetic target evaluation.
It does not turn a dual lower certificate into an approximation upper bound.

## Exact finite target geometry

For a finite injective dictionary d_i>1, let G be its actual Q Gram matrix,
b_i=<qOne,g_{d_i}>_Q, v_i=1-1/d_i, and put

    U = sum_i (G^{-1}v)_i g_{d_i},
    A = v^T G^{-1}v = ||U||_Q^2,
    C = v^T G^{-1}b = <qOne,U>_Q,
    J = C^2/A,
    R = (C/A) U.

Division by zero is interpreted as zero in Lean. If A=0 then U=0 and C=0,
so the following exact identities also cover an empty dictionary:

    ||R||_Q^2 = J,
    ||qOne-R||_Q^2 = 1-J,
    ||qOne-R||_Q^2 = ||qOne-P_V qOne||_Q^2 + ||P_V qOne-R||_Q^2.

The existing QTriangularRayleigh.lean module retains the full scalar
completion for A nonzero:

    ||qOne-aU||_Q^2 = 1-J + A(a-C/A)^2.

Thus R is the best scalar rescaling of the controlled direction.
The gap to the full target projection is an actual squared Q norm.
In particular J<=b^T G^{-1}b<=1. All these finite identities are unconditional.

## Why the normalized direction escapes

The general lemma in Analysis/EscapingRieszDirections.lean has two steps.

1. If tests v_n tend to zero in norm while <u_n,v_n> tends to one,
   then ||u_n|| tends to infinity.
2. Suppose u_n belongs to the closed span of generators and each fixed
   generator's pairing with u_n eventually equals a fixed scalar.
   If ||u_n|| tends to infinity, then u_n/||u_n|| converges weakly to zero.
   The proof first tests the generators, uses the bound
   ||u_n/||u_n||||<=1 to pass to their closed span, and projects an arbitrary
   ambient test onto that span. No density of the legal span in the ambient
   Hilbert space is assumed.

The actual inverse-Gram vector satisfies

    <g_{d_i},U>_Q = 1-1/d_i.

For changing dictionaries, assume every earlier conductor is eventually
retained and there is a chosen conductor tending to infinity. The existing
complete-Q theorem g_d->0 then provides the tests in step 1. Retention gives
the fixed generator pairings for step 2. Consequently

    <qOne,U_n/||U_n||>_Q -> 0,
    J_n = <qOne,U_n/||U_n||>_Q^2 -> 0.

These hypotheses are finite dictionary geometry, not RH-strength providers.

## Actual primorial specialization

QPrimorialChargeDirection.lean uses

    L_n = primorial(max(3,n+1)),
    D_n = {d>1 : d divides L_n}.

The dictionary type is the literal finite subtype D_n, with conductor map
equal to its natural-number value. Injectivity and d>1 are proved.
The existing anchor a_n dividing L_n with n+1<a_n<=2(n+1) supplies the
escaping conductor. Divisibility of consecutive periods supplies retention.
There is no assumed escape, overlap, norm bound, or target-closure provider
in the final specialized theorems:

- primorial_directionFit_norm_tendsto_atTop;
- primorial_rayleighGain_tendsto_zero;
- primorial_rayleighFit_error_tendsto_one.

The squared approximation error of this optimally scaled direction tends
to one. Its inability to approximate the target does not constrain the
full target projection, whose additional captured energy is exactly the
retained gap above.

## Numerical diagnostic (not a Lean proof)

A floating-point check used all nontrivial divisors of L, the complete
periodic-Q weights psi_1(r/L)/(zeta(2)L^2), and dense linear solves.
These values motivated the investigation; the general theorem does not
depend on them.

| L | Dictionary size | J | Full captured energy b^T G^{-1}b |
|---|---:|---:|---:|
| 6 | 3 | 0.42463254 | 0.94523306 |
| 30 | 7 | 0.09377379 | 0.97459977 |
| 210 | 15 | 0.01285977 | 0.98312956 |
| 2310 | 31 | 0.00114917 | 0.98645052 |

The finite full gains increasing is not evidence of their limit being one.

## Updated research agenda

Established: the target charge evaluation, its exact arithmetic variance,
the exact optimal-ray error, the full-projection gap, and unconditional
loss of primorial target capture for this one direction.

Open: obtain a uniform bound on complete legal exact-head energy, or supply
the existing signed cost-minus-gain budget that implies squarefree closure.
The existing sublinear energy estimates do not provide a uniform bound.

A useful next finite dependency is the all-cutoff atom charge formula

    Lambda_N(g_d) = (min(N,d)-1)/(N*d),   N>=1, d>=2.

For N>=max D these directions are proportional to the same v and cannot
repair the one-direction obstruction. Cutoffs inside the dictionary produce
different clipped directions. Their exact multi-direction Gram geometry
is worth formalizing, followed by an actual uniform synthesis-energy bound.
The displayed all-cutoff formula and any sufficient multi-direction
asymptotic estimate are Open in this update.

The current obstruction suggests concentrating on signed Schur gain and
complete legal synthesis energy, rather than trying to force the single
ratio J to one. RH remains open.
