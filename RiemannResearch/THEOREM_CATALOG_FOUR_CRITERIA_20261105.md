# Four regularity criteria continuation: theorem catalog

Date: 4 November 2026 Pacific / 5 November 2026 UTC.

## Newly proved reductions

The coherent candidate was kernel checked by job_EcqnlnEtExDVciEky8fLHXRDrEw3c6ty:
verified=true, exit code 0, 7.995 seconds of reported verification time.
The final modular source is separately validated by the publication checkpoint.
No domain-specific axiom or unfinished proof is introduced.

- NumberTheory/SquareDifferenceRigidity.lean:
  squareOrbit_ge_two; squareOrbit_strictMono;
  adjacent_eq_of_one_weighted_test; constant_of_one_weighted_test;
  constant_of_difference_tendsto_zero.
- NumberTheory/PrimeMultiplierRigidity.lean:
  adjacent_eq_of_two_selected_tests; constant_of_two_selected_tests.
- RH/QSquarefreePrimeLocalTests.lean:
  displacement_constant_of_two_selected_tests;
  riemannHypothesis_of_two_selected_tests;
  displacement_constant_of_weighted_local_tests;
  riemannHypothesis_of_weighted_local_tests;
  riemannHypothesis_of_difference_tendsto_zero.
- RH/QSquarefreeFinitePolylog.lean, namespace QSquarefreeFiniteDisplacement:
  riemannHypothesis_of_sitewise_frequent_polylog.

Four definitions support these thirteen theorems:
squareOrbit, localTest, TwoSelectedTests, WeightedLocalTests.

## Open provider obligations

All RH consumers above are **conditional research reductions**.

| Consumer | Open actual arithmetic premise |
|---|---|
| two selected tests | The chosen small- and large-conductor tests vanish at each physical site. |
| weighted local tests | Lambda_n(k d(k))=0 for every n>=2. |
| difference limit | d(n)-d(n-1) tends to zero. |
| finite polylog | Every fixed site has arbitrarily large finite projection stages within one common polylog envelope. |

Square-recurrence legality, physical sublinearity, finite-projection convergence,
and the original displacement-boundedness RH bridge are inherited providers.
The ordinary converse RH→d=0 uses Bagchi's published squarefree criterion;
no new Lean reverse provider is claimed.

## Paper developments, not newly kernel checked

See FourCriteriaContinuation20261105.md and FourCriteriaQuantitative20261105.md:
scaled leakage criterion; geometric endpoint/annular means; finite future-gain
criterion; Chebyshev acceleration; stronger Vinogradov--Korobov growth profile;
counterexamples to automatic CRT regularity.

Wolfram confirmed the exact local polynomial identity and Chebyshev recurrence
identities/table. Such computations are not substituted for kernel verification.

The original paper's tau local-test definition equals +p Lambda_n(hg_p),
not the prose's minus sign. The correction leaves the zero-test consumers intact.
