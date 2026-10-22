# Squarefree exact-head linear Q-error benchmark

Source: Christian Noack's squarefree infinite CRT continuation, October 16,
2026, Section 9. This continuation formalizes its unconditional benchmark
using the existing canonical Mobius candidate and complete Q/P norm
transfer. Squarefree legality and physical identification reuse the lemmas
already established in QSquarefreeSublinearHeads. No mathematical novelty claim is made.

For every positive requested head H, Bertrand's postulate supplies a prime
H < p <= 2H. Choose N = p-1 and use QMobiusExactHead.exactHead N:

F_N = -sum_{1<=d<=N} mu(d)*g_d + (N+1)*S(N)*g_(N+1).

The correction conductor N+1 is prime. All nonzero lower coefficients
are supported on squarefree conductors, so F_N is finite squarefree legal.
It equals one through N, hence through H, and H <= N < 2H.

The physical Q/P identification is exact, including every infinite tail.
The established complete Pareto norm bound gives

||F_N||_Q^2 < 8*N/zeta(2),
||1-F_N||_Q^2 <= 2 + 16*N/zeta(2)
              <= 2 + 32*H/zeta(2).

This is an explicit unconditional O(H) complete-error upper bound for every
head. The existing QSquarefreeSublinearHeads module separately gives the
stronger asymptotic o(N) error. This benchmark supplies an explicit constant
and a cutoff H <= N < 2H for every positive H.
It does not prove bounded or subpolynomial error, legal approximation of
reflected atoms, or RH. The subpolynomial energy provider remains Open.

Verification uses serialized server checks and one final push-enabled
checkpoint. The final chat report records its terminal result and commit;
queued jobs alone are not verification.
