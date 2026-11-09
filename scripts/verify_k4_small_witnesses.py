#!/usr/bin/env python3
"""Reproduce the small-degree K4 trace-witness certificates.

Elements of F_2[X]/(P) are represented by bit masks: bit i is the
coefficient of X^i. This script checks irreducibility, the K4 parameter
identities, the three rational trace values, and their zero traces.
It is a reproducible finite certificate, not a replacement for the
general Weil-bound argument or the Lean formalization.
"""


def degree(a: int) -> int:
    return a.bit_length() - 1


def poly_mod(a: int, modulus: int) -> int:
    d = degree(modulus)
    while a and degree(a) >= d:
        a ^= modulus << (degree(a) - d)
    return a


def poly_mul(a: int, b: int) -> int:
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out


def mul(a: int, b: int, modulus: int) -> int:
    return poly_mod(poly_mul(a, b), modulus)


def power(a: int, exponent: int, modulus: int) -> int:
    out = 1
    while exponent:
        if exponent & 1:
            out = mul(out, a, modulus)
        a = mul(a, a, modulus)
        exponent >>= 1
    return out


def gcd_poly(a: int, b: int) -> int:
    while b:
        a, b = b, poly_mod(a, b)
    return a


def prime_divisors(n: int) -> list[int]:
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return result


def is_irreducible(modulus: int, n: int) -> bool:
    x = 0b10
    if power(x, 1 << n, modulus) != poly_mod(x, modulus):
        return False
    for p in prime_divisors(n):
        test = power(x, 1 << (n // p), modulus) ^ x
        if gcd_poly(test, modulus) != 1:
            return False
    return True


def trace(a: int, modulus: int, n: int) -> int:
    out = 0
    x = a
    for _ in range(n):
        out ^= x
        x = mul(x, x, modulus)
    if out not in (0, 1):
        raise AssertionError(f"trace did not land in F_2: {out}")
    return out


def inverse(a: int, modulus: int, n: int) -> int:
    if a == 0:
        raise ZeroDivisionError("zero has no inverse")
    return power(a, (1 << n) - 2, modulus)


def polynomial_string(a: int) -> str:
    if a == 0:
        return "0"
    terms = []
    for i in range(degree(a), -1, -1):
        if (a >> i) & 1:
            terms.append("1" if i == 0 else ("X" if i == 1 else f"X^{i}"))
    return " + ".join(terms)


# (degree, modulus, t); all values use the polynomial-basis bit encoding.
CERTIFICATES = [
    (7,  0x083, 0x002),
    (9,  0x203, 0x034),
    (11, 0x805, 0x04C),
]


def verify(n: int, modulus: int, t: int) -> None:
    assert degree(modulus) == n
    assert is_irreducible(modulus, n), (n, "modulus is not irreducible")

    t2 = mul(t, t, modulus)
    q = t2 ^ t
    q2 = mul(q, q, modulus)
    q3 = mul(q2, q, modulus)
    denominator = q3 ^ q ^ 1

    assert q != 0
    assert q != 1
    assert denominator != 0

    d_inv = inverse(denominator, modulus, n)
    q2_over_d = mul(q2, d_inv, modulus)
    t6 = power(t, 6, modulus)
    t6_over_d = mul(t6, d_inv, modulus)

    trace_values = [
        trace(d_inv, modulus, n),
        trace(q2_over_d, modulus, n),
        trace(t6_over_d, modulus, n),
    ]
    assert trace_values == [0, 0, 0], (n, trace_values)

    print(f"n={n}")
    print(f"  P(X) = {polynomial_string(modulus)}")
    print(f"  t    = {polynomial_string(t)}")
    print(f"  q    = {polynomial_string(q)}")
    print(f"  D    = {polynomial_string(denominator)}")
    print(f"  1/D  = {polynomial_string(d_inv)}")
    print(f"  q²/D = {polynomial_string(q2_over_d)}")
    print(f"  t⁶/D = {polynomial_string(t6_over_d)}")
    print(f"  traces = {trace_values}")


if __name__ == "__main__":
    for certificate in CERTIFICATES:
        verify(*certificate)
    print("All small-degree K4 trace-witness certificates verified.")
