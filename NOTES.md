# Types


bool: [0, 1].
- 0: False
- 1: True

booly: [0, q]
- 0: False
- 1-q: True

range(a, b): [a, b]

u8, byte: range(0, 0xff)

u16: range(0, 0xffff)


# Rules


BOOLY(e: expr) -> booly

- if e(x) == 0 then False else True

IF (b: booly) THEN e: expr

- if b(x) is truthy then BOOLY(e(x))

> e * p

IF (e: bool) THEN e1: expr ELSE e2: expr

- if e(x) is true then e1, else e2

> e * p
> (1 - e) * p

e1: booly AND e2:booly -> booly

> e1 * e2

e1: bool AND e2:bool -> bool

> e1 * e2

e1: bool OR e2:bool -> bool

> e1 + e2 - e1 * e2

e1: expr == q: const -> bool

> (1 - (e1 - q) * w)
% (e1 - q) * (1 - (e1 - q) * w)
$ w := inv(e1 - q) if (e1 - q) != 0
$ w := 0 if (e1 - q) == 0

not(e: expr in S) -> booly
  for S = {s1, s2, ..., sn}

(e - s1) * (e - s2) * ... * (e - sn)

CONSTRAIN(not(e: booly))

- e(x) == false

> e == 0

# Gadgets

## IsZero

inputs:
- `value: any`

outputs:
- `is_zero: bool`


```
gadget iz_zero(value: expr) -> bool expr {
    let value_inv: advice;
    witness {
        value_inv = if value != 0 {
            value.invert();
        } else {
            0
        };
    }
    let is_zero_expression: bool expr = 1 - value * value_inv;
    constrain_zero(value * value_inv); 
    return is_zero_expression;
}
```

## LowerThan

inputs:
- `lhs: range(0, 2.pow(8*N))`
- `rhs: range(0, 2.pow(8*N))`

outputs:
- `lt: bool`

```
gadget lt(N: usize)(lhs: range(0, 2.pow(8*N)) expr, rhs: range(0, 2.pow(8*N)) expr) -> bool advice {
    let lt: bool advice;
    witness {
        lt = lhs < rhs;
    }
    constrain_bool(lt);
    let diff_bytes: [u8 advice; N];
    witness {
        let diff: field = (lhs - rhs) + if lt { 2.pow(8*N) } else { 0 };
        for i in 0..N {
            diff_bytes[i] = (diff >> 8*i) & 0xff;
        }
    }
    let diff: range(0, 2.pow(8*N) expr = diff_bytes.zip(0..N).map(|(b, i)| b * 2.pow(8 * i)).sum();
    constrain_zero(lhs - rhs - diff + lt * 2.pow(8*N));
    return lt;
}
```

## Add256

inputs:
- `a: [u8 expr; 32]`
- `b: [u8 expr; 32]`

```
alias u128 = range(0, 2.pow(128));
gadget add256(a: [u8 expr; 32], b: [u8 expr; 32]) -> [u8 expr; 32] {
    let from_bytes_le = |bytes| bytes.zip(0..bytes.len()).map(|(b, i)| b * 2.pow(8 * i)).sum();
    let sum: [u8 advice; 32];
    let carry_lo: range(0, 1) advice;
    let carry_hi: range(0, 1) advice;
    let a_lo: u128 expr = from_bytes_le(a[..16]);
    let b_lo: u128 expr = from_bytes_le(b[..16]);
    let a_hi: u128 expr = from_bytes_le(a[16..]);
    let b_hi: u128 expr = from_bytes_le(b[16..]);
    let sum_lo: u128 expr = from_bytes_le(sum[..16]);
    let sum_hi: u128 expr = from_bytes_le(sum[16..]);
    constrain_eq(a_lo + b_lo, sum_lo + carry_lo * 2.pow(128));
    constrain_eq(a_hi + b_hi + carry_lo, sum_hi + carry_hi * 2.pow(128));
    constrain_in(carry_lo, [0, 1]);
    constrain_in(carry_hi, [0, 1]);
    return sum;
}
```

