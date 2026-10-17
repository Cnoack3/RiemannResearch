# Möbius prime packets: recovered Lean verification

Date: 17 October 2026.

Source: the user-provided Möbius-packet investigation and
[QSquarefreePrimePacketResearch20261016.md at commit 306ccae](https://github.com/Cnoack3/RiemannResearch/blob/306ccae061620c4663b5969cf233cea45d999d8a/RiemannResearch/RH/QSquarefreePrimePacketResearch20261016.md).
That source supplies the arithmetic trial and the RH-facing research question,
not a uniform arithmetic lower bound.

## Exact arithmetic identity

Let L,p>0, g_d(k)=(k mod d)/d, rho_L=phi(L)/L, and let A_L(x)
count positive integers at most x coprime to L. The checked declarations
in RH/QMobiusPrimePacketArithmetic.lean retain the integer quotients:

    h_(L,p)(k) = sum_(d|L) mu(d)*g_(p*d)(k)
              = (k/p)*sum_(d|L) mu(d)/d
                - sum_(d|L) mu(d)*floor(k/(p*d))
              = k*phi(L)/(p*L) - A_L(floor(k/p)).

The finite inclusion-exclusion provider is QPrimeSieve.divisor_sift.
coprimeCount_eq_floor_sum counts every multiple before any real coercion.
coprimeCount_self and divisorDensity_eq_totient identify the density with
the actual Nat.totient. No squarefreeness or primality premise is needed
for this arithmetic statement.

The same module checks the short-head identity for k<p, exact p*L
periodicity, and arithmeticPacket_six_five_seven: h_(6,5)(7)=-8/15.
The later signed count discrepancy is not discarded.

## Actual signed covariance trial

RH/QCovarianceTrial.lean works with the existing actual Q Hilbert vectors.
For old conductors a, new conductors b, and arbitrary real trial weights t,
it defines trialVector, trialSource=alpha, and trialEnergy=E.
All means and covariances use Q(k)=1/(zeta(2)*k^2), k>=1.

Write C for the old centered covariance, V for the cross covariance,
S for the new centered covariance, m for the new mean vector, and b_old
for the old mean vector. Then the checked finite formulas are

    alpha = sum_j t_j * (m_j - sum_i (C^(-1)b_old)_i * V_ij),
    E     = sum_i t_i * sum_j
              (S_ij - sum_k V_ki * (C^(-1)V)_kj) * t_j.

Thus alpha=t^T delta and E=t^T R t, with every signed and mixed term retained.
The residual pairing is

    alpha = (1+kappa_old) * <1-F_old, sum_j t_j*g_(b_j)>_Q.

For an independent complete old/new family and nonzero t, E>0.
The actual capacity gain Gamma satisfies

    alpha^2 <= Gamma*E,
    alpha^2/E <= Gamma.

trial_gain_complete retains the exact Hilbert remainder:

    Gamma = alpha^2/E + ||v_star - (alpha/E)*w_t||_Q^2,

where w_t is the genuinely screened centered trial vector and v_star is
the screened inverse-source representer. This is an equality before its
nonnegative remainder is dropped. alpha is the signed screened source,
not the mean of the centered screened vector (whose mean is zero).

## Actual squarefree primorial assembly

RH/QMobiusPrimePacket.lean specializes the preceding statements to the
existing cutoff-indexed period L_n=primorial(n+3), with a fresh prime p.
The index includes EVERY divisor d of L_n, including d=1.

* moebiusWeight_ne_zero uses mu(1)=1.
* moebiusPacket_physical and moebiusPacket_physical_eq_count identify the
  actual QHilbert packet pointwise with the full arithmetic formula.
* moebiusPacket_mem_squarefreeSpan proves literal finite legal membership.
* moebiusSource_eq_residual_pairing uses the actual primorialOptimizer.
* moebiusEnergy_pos proves positivity from freshness and independence.
* moebius_trial_lower_bound bounds the existing actual packetGain.
* moebius_gain_lower_of_bounds consumes explicit estimates
  a^2<=alpha^2, E<=e, 0<e and concludes a^2/e<=packetGain.

No abstract replacement covariance, truncated Q law, unsigned source,
prime-only CRT span identity, or presumed vanishing residual is used.

## Verification evidence

The previously queued snippet eventually ran and hit its 180-second
wall timeout without diagnostics. That was not a mathematical refutation.
The retained workspace was resumed and the draft modules were repaired
using serialized project-file checks.

Successful targeted server checks, all exit_code=0 and verified=true:

* Arithmetic: job_0F99sVE_ZGs_skF97v4efNi8eYbCfOMG.
* Full covariance trial: job_uaCwuIQXvJ11kyE0vLe9F1js8C_iAnJx.
* Actual primorial assembly: job_fbjC497ioXJ3v2cnutVoxh2ytfU4t1HZ.

These checks are distinct from the final publication checkpoint.
Axiom audit job_oXvrjUDXCRywSTKjNu-WmtHW5rBaRS93 also succeeded with
exit_code=0 and verified=true. Eight main declarations, including the complete
remainder and actual Möbius gain consumer, depend only on propext,
Classical.choice, and Quot.sound. No project-local axiom or sorryAx appears
in those transitive reports. Local arithmetic input estimates are explicit
parameters in the consumer; this audit does not discharge them.

The original publication checkpoint validated the original source tree and
created retained local commit 359edd4e1e16b6756a53783f508cdb1b47a5c104, but
a concurrent theorem-catalog addition on newer main prevented integration.
No source was pushed from that failed integration. The exact verified modules
were carried unchanged to current main 5873a31797dc426d57071105f2b76bd65b421ce9;
the catalog entry preserves the newer additions. Publication requires a
successful final server checkpoint of that current-main source tree.
Its job and commit are reported separately.

## Numerical evidence and open obligations

The preceding investigation saved outward exact-integer interval calculations
through p*L=30030, including the entire periodic inverse-square tail and
interval LDL conditioning control. Those external numerical certificates
are not newly Lean-formalized in this change.

In particular, the single Möbius trial need not capture most of the full
packet gain, its gain bound need not increase at each next-prime step,
and the short head alone does not lower-bound the signed source.
Neither these tests nor the finite identities provide an asymptotic theorem.

Conditional research reduction: along actual next-prime stages, estimates

    |alpha_j| >= a_j,  0<E_j<=e_j,
    sum_j a_j^2/e_j = infinity

would force unbounded accumulated gains. Each arithmetic estimate and the
divergence premise remain Open until proved independently. The existing
capacity telescope retains the initial capacity:

    kappa_N = kappa_0 + sum_(j<N) actualGain_j.

Open: uniform quantitative estimates for the actual signed screened source
and full screened energy on a sufficiently large set of next-prime stages.
Open: global divergence of accumulated actual packet gains.
No RH conclusion is claimed here.
