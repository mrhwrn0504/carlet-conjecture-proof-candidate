#!/usr/bin/env python3
"""Reproduce the small-degree K4 trace and Artin--Schreier certificates.

Elements of F_2[X]/(P) are represented by bit masks: bit i is the
coefficient of X^i. This checks irreducibility, the K4 parameter
identities, all three rational traces, and explicit roots z,s,v of

    z^2 + z = 1/D,
    s^2 + s = q(q+1)z,
    v^2 + v = qs.

These are finite computational certificates, not a replacement for the
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


# (degree, modulus, t, z, s, v), in polynomial-basis bit encoding.
# The roots were recomputed for the exact t values in the original trace
# certificate list; do not substitute the earlier, mismatched display values.
CERTIFICATES = [
    (7,  0x083, 0x002, 0x07A, 0x078, 0x010),
    (9,  0x203, 0x034, 0x134, 0x1CE, 0x1FC),
    (11, 0x805, 0x04C, 0x742, 0x61C, 0x3EC),
]


def verify(n: int, modulus: int, t: int, z: int, s: int, v: int) -> None:
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

    z2_plus_z = mul(z, z, modulus) ^ z
    s2_plus_s = mul(s, s, modulus) ^ s
    v2_plus_v = mul(v, v, modulus) ^ v
    s_rhs = mul(mul(q, q ^ 1, modulus), z, modulus)
    v_rhs = mul(q, s, modulus)
    assert z2_plus_z == d_inv, (n, "z equation", hex(z2_plus_z), hex(d_inv))
    assert s2_plus_s == s_rhs, (n, "s equation", hex(s2_plus_s), hex(s_rhs))
    assert v2_plus_v == v_rhs, (n, "v equation", hex(v2_plus_v), hex(v_rhs))

    print(f"n={n}")
    print(f"  P(X) = {polynomial_string(modulus)}")
    print(f"  t    = {polynomial_string(t)}")
    print(f"  q    = {polynomial_string(q)}")
    print(f"  D    = {polynomial_string(denominator)}")
    print(f"  z    = {polynomial_string(z)}")
    print(f"  s    = {polynomial_string(s)}")
    print(f"  v    = {polynomial_string(v)}")
    print(f"  1/D  = {polynomial_string(d_inv)}")
    print(f"  q²/D = {polynomial_string(q2_over_d)}")
    print(f"  t⁶/D = {polynomial_string(t6_over_d)}")
    print(f"  traces = {trace_values}")
    print("  Artin-Schreier equations = [True, True, True]")


if __name__ == "__main__":
    for certificate in CERTIFICATES:
        verify(*certificate)
    print("All small-degree K4 trace and Artin-Schreier certificates verified.")
