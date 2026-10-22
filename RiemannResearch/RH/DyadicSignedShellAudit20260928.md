# Dyadic signed-shell audit at the stretched scale

Continuation of 03f86c192fbcbb6ed1e5c81888533ca6a6d4e855, 28 September 2026.
Source: the user's requested combination of the repository's exact shell
identities, signed canonical Mobius pairing, PNT tail obstruction, and
stretched source transfer. The arguments below are elementary consequences
of those inputs; no novelty is claimed.

## Conclusion and status

No unconditional cofinal upper bound on the actual residual tail was
obtained. Dyadic telescoping and the existing signed pairing do not turn the
checked Cauchy--Schwarz lower constraints into upper estimates.

The reusable progress is an exact signed-shell accounting identity and
a sharp cumulative one-sided criterion at the stretched scale. Its remaining
signed-shell estimate is explicitly **Open**. The criterion does not discharge
the inverse-Gram or residual-tail bottleneck and does not prove RH.

## Normalization

Write F = P_V 1, r = 1-F, D = ||r||^2, and

    T_N = sum_(n>N) r(n)^2/[n(n+1)],
    S_N = sum_(N<n<=2N) r(n)^2/[n(n+1)] = T_N-T_(2N).

Here A_N is the boundary-corrected exact-head canonical Mobius vector
canonicalMobiusHilbert N, not the natural residual carrying the same letter
in some older notes. It belongs to the legal closed space and equals one
at physical coordinates 1,...,N. Put

    Phi(N) = ((6+log N) log(6+log N))^(1/11),
    w_b(N) = N exp(-b Phi(N)).

The checked arithmetic provider supplies a>0, C>=0 and, eventually,

    ||1-A_N||^2 <= 8 + C w_a(N).

The checked transfer gives D^2 <= (8+C w_a(N)) T_N. For every 0<b<a,
D>0 implies w_b(N) T_N -> infinity. At the full provider exponent a,
cofinal smallness of w_a(N) T_N implies D=0.

## The exact signed shell and the term that cannot be omitted

Let <.,.>_(N,2N] mean the weighted Pareto pairing on this finite physical
shell, and <.,.>_(>2N) the complete infinite tail pairing. Define

    J_N = <r, A_N-F>_(N,2N],
    Q_N = <r, A_(2N)-A_N>_(>2N),
    H_N = J_N-Q_N.

The existing canonical shell theorem says

    <r,1-A_N>_(N,2N] = -Q_N.

Since 1-A_N = r-(A_N-F), it follows exactly that

    H_N = S_N.

This is residualSignedShell_eq_energy. Global orthogonality gives
<r,A_N-F>=0, but it does NOT give J_N=0: the tail and head contributions
to this inner product still have to cancel. Omitting J_N would turn an
identity into an unsupported estimate.

For fixed canonical cutoff N, the differently indexed shell series

    sum_(j>=0) <r,1-A_N>_(2^j N,2^(j+1)N] = D

is also exact when N>=1. Indeed the product series is absolutely summable
by Hilbert-space Cauchy--Schwarz, the shells partition the physical tail,
1-A_N vanishes on its head, and <r,A_N>=0, <r,1>=D.
This observation is justified here in prose. Replacing A_N by A_(2^j N)
inside this series changes it; the resulting moving-cutoff expressions
cannot be telescoped as if the second factor were fixed.

## The smallest direct cumulative estimate in this bookkeeping

For ANY real weight w, define the net signed shell gain

    G_w(N) = w(2N) H_N - (w(2N)-w(N)) T_N.

For n_j=2^j N_0, N_0>=1, exact finite telescoping gives

    w(n_K) T_(n_K)
      = w(N_0) T_(N_0) - sum_(j<K) G_w(n_j).              (1)

This holds without assumptions on the signs or growth of w. In particular,
the full-provider dyadic condition

    for every epsilon>0, for arbitrarily large K,
    sum_(j<K) G_(w_a)(n_j) > w_a(N_0) T_(N_0)-epsilon     (2)

is EXACTLY equivalent to cofinal smallness on this dyadic orbit.
It implies liminf_(N->infinity) w_a(N) T_N=0, and hence D=0 by the
existing checked transfer. This equivalence is scoped to the chosen
dyadic orbit; no unjustified equivalence with every all-cutoff subsequence
is needed.

Condition (2) preserves all signs. It requires neither absolute summability
nor a gain at every individual shell. It is the smallest direct one-sided
cumulative estimate in (1), not a new arithmetic bound.

## A weaker practical provider at any smaller exponent

There is a checked universal a>0 such that for every 0<b<a and N_0>=1,

    r=0  iff  there exists C such that, for arbitrarily large K,
               sum_(j<K) G_(w_b)(n_j) >= -C.             (3)

Proof: the forward direction has all tails and shell gains zero.
Conversely, (1) turns the right side into a cofinal bound on w_b(n_K)T_(n_K).
If r were nonzero, then D>0 and the checked stretched barrier would force
this product to infinity, including along the cofinal dyadic orbit.
This is a contradiction.

Thus a provider need only prevent the cumulative signed gain from tending
to minus infinity. A stronger, more local sufficient estimate is

    H_N >= [1 - (1/2) exp(b(Phi(2N)-Phi(N)))] T_N          (4)

on every shell of one sufficiently late dyadic orbit. It makes each gain
nonnegative and supplies (3) with C=0. Formula (4) follows by dividing the
gain inequality by w_b(2N)>0. Negative individual gains are permitted by
the weaker criterion (3).

The condition in (3) is already equivalent to zero residual. It must not
be described as an established consequence of PNT. Via the repository's
checked forward density-to-RH bridge it implies RH. No converse
RH-to-density theorem is silently imported.

## Why the available estimates do not supply the provider

1. The unsigned identity S_N=T_N-T_(2N) supplies no lower fraction of T_N
   that must fall in a shell. Summability permits arbitrarily slow tail
   decay.
2. The signed canonical identity bounds a shell observation by a later
   tail pairing. Cauchy--Schwarz yields
       |<r,1-A_N>_shell|^2 <= T_(2N) ||(A_(2N)-A_N)_(>2N)||^2.
   This is a lower constraint on T_(2N) for a known nonzero observation.
   Substitution of a stretched energy ceiling does not reverse it.
3. The uniform stretched source theorem tests 1-A_N against individual
   residue atoms. It provides no rate for the local term J_N, a moving
   projected dual, or the cumulative gains in (2)/(3). Passing from atoms
   to arbitrary approximations of F requires quantitative control of the
   coefficients and approximation error that is not in the input theorem.
4. The PNT and stretched barriers strengthen the obstruction if D>0;
   they do not force an upper estimate.

For a concrete rate check, the abstract Hilbert tail

    T_N=(N+1)^(-1/2)

has positive shells, T_N->0, N T_N->infinity, and
w_b(N)T_N->infinity for every fixed b>0 because Phi(N)=o(log N).
It is realized by a Pareto Hilbert vector with

    v(n)^2=n(n+1)[n^(-1/2)-(n+1)^(-1/2)], n>=1.

Its norm squared is one. This is ONLY a counterexample to deriving an
upper rate from scalar summability/telescoping/lower-growth facts.
It is not asserted to be the arithmetic residual or to satisfy all
arithmetic orthogonality identities; it is not a counterexample to RH.

## Formalization

RH/ParetoDyadicShellCriterion.lean contains:

- hilbert_weighted_dyadic_shell_telescope: arbitrary-vector, arbitrary-weight
  finite dyadic telescoping.
- dyadicCutoff_tendsto_atTop: cofinality for positive starting cutoffs.
- residualSignedShell_eq_energy: the complete signed expression H_N=S_N.
- residual_weighted_dyadic_telescope: formula (1) for the actual residual.
- cofinally_small_dyadic_tail_iff_signed_gain: exact criterion (2).
- limitEnergy_eq_zero_of_cofinal_dyadic_signed_gain: the full-provider
  conditional assembly, retaining both its energy and signed-gain premises.
- exists_stretched_signed_shell_criterion: criterion (3), assembled from
  the unconditional arithmetic provider, with the gain bound still explicit.

The signed-shell upper-control provider is Open. RH remains unproved here.

## Verification record

The complete Lean candidate passed serialized job
job_v_w482-cugfhsRPifbivm4G9hE0tyAA4 with exit_code=0 and verified=true.
Axiom inspection of residualSignedShell_eq_energy,
limitEnergy_eq_zero_of_cofinal_dyadic_signed_gain, and
exists_stretched_signed_shell_criterion reports only propext,
Classical.choice, and Quot.sound. Their substantive hypotheses and the
unproved gain provider are described above; axiom inspection does not
discharge a theorem's explicit hypotheses.

The publication checkpoint additionally validates the saved module and
its affected project dependents.
