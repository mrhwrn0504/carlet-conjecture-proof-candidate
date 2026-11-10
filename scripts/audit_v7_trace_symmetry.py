#!/usr/bin/env python3
"""Independent V7 finite-field count/symmetry audit. No third-party dependencies.

This script proves only the four finite calculations below. The infinite
existence theorem relies on a separate Hasse--Weil curve estimate and is
NOT yet Lean-verified.
"""

from math import sqrt


def deg(x):
    return x.bit_length() - 1


def reduce_poly(x, p):
    d = deg(p)
    while x and deg(x) >= d:
        x ^= p << (deg(x) - d)
    return x


def mul(a, b, p):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return reduce_poly(out, p)


def power(a, k, p):
    r = 1
    while k:
        if k & 1:
            r = mul(r, a, p)
        a = mul(a, a, p)
        k >>= 1
    return r


def gcd(a, b):
    while b:
        a, b = b, reduce_poly(a, b)
    return a


def primes(n):
    ps = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        ps.append(n)
    return ps


def irreducible(p, n):
    return deg(p) == n and power(2, 1 << n, p) == 2 and all(
        gcd(power(2, 1 << (n // d), p) ^ 2, p) == 1 for d in primes(n)
    )


def trace(x, n, p):
    result = 0
    for _ in range(n):
        result ^= x
        x = mul(x, x, p)
    assert result in (0, 1)
    return result


def trace_triple(t, n, p):
    q = mul(t, t, p) ^ t
    d = power(q, 3, p) ^ q ^ 1
    if not d:
        return q, d, None
    inverse = power(d, (1 << n) - 2, p)
    return q, d, (
        trace(inverse, n, p),
        trace(mul(power(q, 2, p), inverse, p), n, p),
        trace(mul(power(t, 6, p), inverse, p), n, p),
    )


# n, polynomial, (t,z,s,v) small certificate, expected solutions, D-roots
CASES = (
    (7, 0x83, (0x02, 0x7A, 0x78, 0x10), 42, 0),
    (9, 0x203, (0x34, 0x134, 0x1CE, 0x1FC), 54, 6),
    (11, 0x805, (0x4C, 0x742, 0x61C, 0x3EC), 264, 0),
    (13, 0x201B, None, 780, 0),
)


def audit(n, p, certificate, want_n, want_roots):
    assert n % 2 == 1 and irreducible(p, n)
    Q = 1 << n
    sums = [0] * 8
    N = roots = 0
    for t in range(Q):
        q, d, vals = trace_triple(t, n, p)
        if vals is None:
            roots += 1
            continue
        if vals == (0, 0, 0):
            N += 1
            assert q not in (0, 1)
            assert trace_triple(t ^ 1, n, p)[2] == (0, 0, 0)
        for mask in range(1, 8):
            parity = 0
            for j in range(3):
                if mask & (1 << j):
                    parity ^= vals[j]
            sums[mask] += 1 if parity == 0 else -1
    assert (N, roots) == (want_n, want_roots)
    assert 8 * N == Q - roots + sum(sums[1:])  # character orthogonality
    assert sums[4] == sums[7] and sums[5] == sums[6]  # t -> t+1
    assert 8 * N == Q-roots+sums[1]+sums[2]+sums[3]+2*sums[4]+2*sums[5]
    assert N % 2 == 0
    for S in sums[1:]:
        assert max(0, abs(S) - 1)**2 <= 100 * Q
    if certificate:
        t, z, s, v = certificate
        q, d, vals = trace_triple(t, n, p)
        assert vals == (0, 0, 0)
        inv = power(d, Q - 2, p)
        assert mul(z, z, p) ^ z == inv
        assert mul(s, s, p) ^ s == mul(mul(q, q ^ 1, p), z, p)
        assert mul(v, v, p) ^ v == mul(q, s, p)
    print(f"n={n}, Q={Q}, r={roots}, N={N}, "
          f"S001=S111={sums[4]}, S101=S011={sums[5]}, "
          f"lower_bound={(Q-70*sqrt(Q)-5)/8:.2f}")


def main():
    D = 0b1111111
    a, b, c = 1, 0b10100, 0b1000000
    assert D == 0b1111111 and gcd(0b1011, 0b1101) == 1
    for mask in range(1, 8):
        A = ((mask & 1) != 0)*a ^ ((mask & 2) != 0)*b ^ ((mask & 4) != 0)*c
        assert gcd(A, D) == 1
    for case in CASES:
        audit(*case)
    print("PASS: all four independent V7 finite-field audits.")


if __name__ == "__main__":
    main()
