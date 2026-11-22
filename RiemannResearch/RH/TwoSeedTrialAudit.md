# Complete errors for rational two-seed trials

Each JSON row `[p,m,a]` contributes $(a/10^6)(r_{pm}-r_m)$, where $r_d(n)=n\bmod d$. The target is the constant on positive integers. With $c_d$ the collected integral coefficients of the residues, put $R(n)=10^6-\sum_d c_d r_d(n)$. The full squared error is $10^{-12}\sum_{n\ge1}R(n)^2/[n(n+1)]$. All coefficients, head units and endpoints in this note are integers or rational numbers.

| Largest allowed dilation | Dictionary columns | Last head site $T$ | Rounded head lower, in units of $10^{-18}$ | Rounded head upper, in units of $10^{-18}$ | Complete squared error, outward interval |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 384 | 640 | 134,217,728 | 23292988311894838 | 23292988446112554 | (0.02329298, 0.02329340) |
| 1,536 | 2,560 | 536,870,912 | 20219950239628219 | 20219950776499112 | (0.02021995, 0.02022743) |
| 2,048 | 3,414 | 1,073,741,824 | 19703477935380231 | 19703479009122035 | (0.01970347, 0.01971066) |

The finite coefficients were chosen by solving the Gram normal equations numerically and rounding to denominator one million. The error checks below use the rounded coefficients. The intervals enclose the errors of the supplied trials. There are 640, 2,558, and 3,407 nonzero rounded coefficients, respectively. [Dilation-384 coefficient table](TwoSeedTrial384.json) · [Dilation-1,536 coefficient table](TwoSeedTrial1536.json) · [Dilation-2,048 coefficient table](TwoSeedTrial2048.json)

## Search and tail calculation

The sparse Gram calculation applies the digamma jump formula to each pair of digit functions. For $u(n)=\lfloor n/m\rfloor\bmod p$ and $v(n)=\lfloor n/k\rfloor\bmod q$ take $L=\operatorname{lcm}(pm,qk)$. In the product jump use $\Delta(uv)(r)=\Delta u(r)v(r)+u(r-1)\Delta v(r)$. Thus the two sums visit the multiples of $m$ and $k$. The unscaled digit mean is $\log(p)/m$. The column selection proceeds by increasing $m$ and then $p$ and keeps an edge $m\to pm$ if it connects previously disconnected vertices. Every discarded difference $r_{pm}-r_m$ is a signed sum along the existing path. [Digamma identity](TwoSeedDigammaJumps.lean)

For the integer replay, $R(0)=10^6$ and
$$
R(n)-R(n-1)=-\sum_d c_d+\sum_{d\mid n}d c_d.
$$
For $1\le n\le T$ the verifier adds both the floor and the ceiling of $10^6R(n)^2/[n(n+1)]$. For the remaining sites use the signed covariance quantities
$$
\mu=10^6-\tfrac12\sum_d c_d(d-1),\quad
A=\sum_d |c_d|d(d-1),\quad
U=\mu^2+\tfrac1{12}\sum_{d,e}c_dc_e(\gcd(d,e)^2-1),\quad
D=(A^2+4|\mu|A)/8 .
$$
The sum of $R(n)^2-U$ on every interval has absolute value at most $D$. Partial summation against the decreasing weights bounds the omitted unscaled loss by $U/(T+1)+D/[(T+1)(T+2)]$. Positivity makes the downward-rounded head a lower bound on the full loss. The precise finite integers above were checked externally. The kernel verifies the general tail argument, the separate 56-term trial of period 5,040, and the complete-error digamma identity. [Signed tail proof](ParetoRawTrialPeriodicTail.lean) · [56-term Lean certificate](TwoSeedPeriodicCertificate.lean)

## Replay

Run the following in this directory with Python 3 and a C++17 compiler supporting 128-bit integers. It recompiles the integer verifier, checks each pair of head totals, computes each rational tail and prints the exact endpoints. The 128-bit products prevent overflow in the squared residuals. The physical residual is cross-checked directly on the first 1,024 sites and at each block boundary.

```sh
python3 -c 'from pathlib import Path; t=Path("TwoSeedTrialAudit.md").read_text(); s=t.split("\n```python\n",1)[1].split("\n```",1)[0]; exec(compile(s,"TwoSeedTrialAudit.md","exec"),{"__file__":"TwoSeedTrialAudit.md","__name__":"__main__"})'
```

```python
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess

root = Path(__file__).resolve().parent
note = (root / "TwoSeedTrialAudit.md").read_text()
cpp = note.split("```cpp\n", 1)[1].split("\n```", 1)[0]
with TemporaryDirectory() as work:
    source = Path(work) / "head.cpp"
    binary = Path(work) / "head"
    source.write_text(cpp)
    subprocess.run(["c++", "-O3", "-std=c++17", str(source), "-o", str(binary)], check=True)
    for budget, sites, expected in [
        (384, 2**27, (23292988311894838, 23292988446112554)),
        (1536, 2**29, (20219950239628219, 20219950776499112)),
        (2048, 2**30, (19703477935380231, 19703479009122035)),
    ]:
        data = json.loads((root / f"TwoSeedTrial{budget}.json").read_text())
        rows = data["rows"]
        scale = data["denominator"]
        assert scale == 10**6 and data["maximum_dilation"] == budget
        words = [f"{budget} {sites} {len(rows)}"] + [f"{p} {m} {a}" for p, m, a in rows]
        result = subprocess.run([str(binary)], input="\n".join(words), text=True,
                                capture_output=True, check=True)
        head = tuple(map(int, result.stdout.split()))
        assert head == expected
        coeff = defaultdict(int)
        for p, m, a in rows:
            coeff[p * m] += a
            coeff[m] -= a
        coeff.pop(1, None)
        mean = scale - sum(Fraction(z * (d - 1), 2) for d, z in coeff.items())
        amplitude = sum(abs(z) * d * (d - 1) for d, z in coeff.items())
        covariance = sum(z * w * (gcd(d,e)**2 - 1)
                         for (d,z), (e,w) in product(coeff.items(), repeat=2))
        uniform_square = mean**2 + Fraction(covariance, 12)
        discrepancy = (amplitude**2 + 4 * abs(mean) * amplitude) / 8
        tail = uniform_square / (sites + 1) + discrepancy / ((sites + 1) * (sites + 2))
        lower = Fraction(head[0], 10**18)
        upper = Fraction(head[1], 10**18) + tail / scale**2
        print(budget, lower, upper)
```

```cpp
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <map>
#include <vector>

using Integer = std::int64_t;
using Wide = __int128_t;

int main() {
    Integer cutoff, sites, count;
    if (!(std::cin >> cutoff >> sites >> count) || cutoff < 1 || cutoff > 2048 ||
        sites < 1 || sites > (Integer{1} << 30) || count < 1 || count > 3414) return 1;
    std::map<Integer, Integer> residues;
    Integer lower = 1000000, upper = 1000000;
    for (Integer i = 0; i < count; ++i) {
        Integer p, m, a;
        if (!(std::cin >> p >> m >> a) || (p != 2 && p != 3) ||
            m < 1 || m > cutoff || a < -1000000 || a > 1000000) return 2;
        residues[p * m] += a;
        residues[m] -= a;
        Integer extent = (p - 1) * m * a;
        lower -= std::max(Integer{0}, extent);
        upper -= std::min(Integer{0}, extent);
    }
    residues.erase(1);
    Integer slope = 0;
    for (const auto &[d, z] : residues) slope -= z;
    constexpr Integer width = 65536;
    std::vector<Integer> jumps(width);
    Integer residual = 1000000, rounded = 0;
    Wide total = 0;
    for (Integer start = 1; start <= sites; start += width) {
        Integer end = std::min(start + width, sites + 1);
        std::fill(jumps.begin(), jumps.end(), slope);
        for (const auto &[d, z] : residues)
            for (Integer n = ((start + d - 1) / d) * d; n < end; n += d)
                jumps[n - start] += d * z;
        for (Integer n = start; n < end; ++n) {
            residual += jumps[n - start];
            if (residual < lower || residual > upper) return 3;
            if (n <= 1024 || n == sites || n == start) {
                Integer direct = 1000000;
                for (const auto &[d,z] : residues) direct -= z * (n % d);
                if (direct != residual) return 4;
            }
            Wide numerator = Wide{1000000} * residual * residual;
            Integer denominator = n * (n + 1);
            Wide floor = numerator / denominator;
            total += floor;
            rounded += (numerator != floor * denominator);
        }
    }
    if (total + rounded > std::numeric_limits<Integer>::max()) return 5;
    std::cout << static_cast<Integer>(total) << " "
              << static_cast<Integer>(total + rounded) << "\n";
}
```
