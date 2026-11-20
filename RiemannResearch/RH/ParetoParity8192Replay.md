# Exact replay of the conductor-8192 Pareto head

The input is the signed coefficient table used by Lean in [ParetoParity8192Data](ParetoParity8192Data.lean). For each physical site \(n\), add the integer ceiling of \(e(n)^2/[n(n+1)]\), where \(e(n)=10^9-\sum_d c_d(n\bmod d)\). The executable starts each block with the actual residue at the preceding site. The Lean theorem [residual_succ](ParetoParity8192Head.lean) identifies its update as \(-\sum_d c_d+\sum_{d\mid n}d c_d\), and the theorem `roundedHead_eq_blocks` gives its partition of the head.

[ParetoParity8192Sieve](ParetoParity8192Sieve.lean) proves that the following final expression equals the defining rounded head. Its individual blocks use the same starting residual and ceiling convention.

```lean
import RiemannResearch.RH.ParetoParity8192Sieve
open RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192
open scoped BigOperators

#eval sievedBlock 0 (2 ^ 17)
#eval ∑ b ∈ Finset.range 8192, sievedBlock ((2 ^ 17) * b) (2 ^ 17)
```

The kernel checked the equivalence of the sieve and the defining sums, the first 128 site contributions in aggregate, and the signed CRT constants. The full C++ replay below checks every site and all eight group totals. A single Lean evaluator run over all eight groups reached its 2,400-second wall limit. The enclosure theorem keeps the full finite head inequality as a separate premise. [Server replay record](https://app.buildbuddy.io/invocation/f705b485-8d82-4a5d-804b-65bae6fd05e7)

From the repository root, extract the C++ source and run

```sh
awk '/^```cpp$/{copy=1;next} /^```$/{copy=0} copy' RiemannResearch/RH/ParetoParity8192Replay.md > /tmp/pareto8192.cpp
g++ -std=c++17 -O3 -fopenmp /tmp/pareto8192.cpp -o /tmp/pareto8192
/tmp/pareto8192 RiemannResearch/RH/ParetoParity8192Data.lean
```

A successful run prints `roundedHead(1073741824) = 5067697348817286`. Lean packs each row into signed base-\(2^{31}\) digits biased by \(2^{30}\). The executable reads those digit literals directly. The loops operate on integers throughout. The program checks the array dimensions, indexing order, integer-width limits, all eight stripe subtotals, and the final head equality. Compiling without OpenMP gives the same sum serially.

```cpp
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <regex>
#include <stdexcept>
#include <string>
#include <vector>

using Integer = std::int64_t;
using Wide = __int128_t;

constexpr Integer conductor = 8192;
constexpr Integer scale = 1000000000;
constexpr Integer cutoff = Integer{1} << 30;
constexpr Integer block_length = Integer{1} << 17;

std::vector<Integer> read_coefficients(const char* path) {
    std::ifstream input(path);
    if (!input) throw std::runtime_error("cannot open the Lean coefficient source");
    std::string source((std::istreambuf_iterator<char>(input)), {});
    const std::regex chunk(R"(private def chunk([0-9]{2}) : ℕ := signedRow!\[([^\]]+)\])");
    const std::regex number(R"(-?[0-9]+)");
    std::vector<Integer> result{0, 0};
    std::vector<std::string> names;

    for (std::sregex_iterator it(source.begin(), source.end(), chunk), end; it != end; ++it) {
        const auto index = names.size();
        if (index >= 64 || std::stoul((*it)[1]) != index)
            throw std::runtime_error("unexpected coefficient chunk");
        names.push_back("chunk" + (*it)[1].str());
        const std::string values = (*it)[2];
        const auto before = result.size();
        for (std::sregex_iterator term(values.begin(), values.end(), number); term != end; ++term)
            result.push_back(std::stoll(term->str()));
        if (result.size() - before != (index == 63 ? 127 : 128))
            throw std::runtime_error("incorrect coefficient chunk length");
    }
    if (result.size() != conductor + 1) throw std::runtime_error("incorrect trial size");

    const std::regex table(R"(private def chunks \(i : ℕ\) : ℕ :=([\s\S]*?)def coeff)");
    std::smatch match;
    if (!std::regex_search(source, match, table)) throw std::runtime_error("missing chunk table");
    const std::string body = match[1];
    const std::regex name(R"(chunk[0-9]+)");
    std::vector<std::string> order;
    for (std::sregex_iterator it(body.begin(), body.end(), name), end; it != end; ++it)
        order.push_back(it->str());
    if (order != names) throw std::runtime_error("chunk lookup order differs from the source order");
    return result;
}

Integer replay(const std::vector<Integer>& c) {
    Wide coefficient_sum = 0, residual_bound = scale, increment_bound = 0;
    for (Integer d = 2; d <= conductor; ++d) {
        const Wide magnitude = c[d] < 0 ? -Wide(c[d]) : Wide(c[d]);
        coefficient_sum += c[d];
        residual_bound += (d - 1) * magnitude;
        increment_bound += (d + 1) * magnitude;
    }
    // These bounds keep residues and all partial sieve updates in int64. They
    // also keep cutoff times the largest squared residue within signed int128.
    if (residual_bound > 2000000000000LL || increment_bound > 2000000000000LL)
        throw std::runtime_error("trial exceeds the integer-width bounds");

    const Integer blocks = cutoff / block_length;
    std::vector<Wide> heads(blocks);
    #pragma omp parallel for schedule(dynamic, 4)
    for (Integer b = 0; b < blocks; ++b) {
        const Integer start = b * block_length;
        Integer residual = scale;
        std::vector<Integer> steps(block_length, -Integer(coefficient_sum));
        for (Integer d = 2; d <= conductor; ++d) {
            residual -= c[d] * (start % d);
            const Integer first = (d - (start + 1) % d) % d;
            for (Integer j = first; j < block_length; j += d) steps[j] += d * c[d];
        }
        Wide total = 0;
        for (Integer j = 0; j < block_length; ++j) {
            const Integer n = start + j + 1;
            residual += steps[j];
            const Integer divisor = n * (n + 1);
            total += (Wide(residual) * residual + divisor - 1) / divisor;
        }
        heads[b] = total;
    }
    Wide total = 0;
    constexpr std::array<Integer, 8> expected_stripes{
        5067609285810939LL, 50137322697LL, 16722620391LL, 8405113792LL,
        5074680560LL, 3405419927LL, 2455668609LL, 1862180371LL
    };
    for (Integer g = 0; g < 8; ++g) {
        Wide subtotal = 0;
        for (Integer j = 0; j < blocks / 8; ++j) subtotal += heads[g * (blocks / 8) + j];
        if (subtotal != expected_stripes[g]) throw std::runtime_error("stripe subtotal differs");
        total += subtotal;
    }
    if (total != 5067697348817286LL) throw std::runtime_error("rounded head differs");
    return Integer(total);
}

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: pareto8192 PATH/TO/ParetoParity8192Data.lean\n";
        return 2;
    }
    try {
        const auto head = replay(read_coefficients(argv[1]));
        std::cout << "roundedHead(" << cutoff << ") = " << head << '\n';
    } catch (const std::exception& e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}

```
