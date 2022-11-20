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

# DSL design notes

This is a list of features that the DSL should optimize for
- Constraint definition and witness assignment should be done together
- Should not expose rotations, only variables (advices, constants?) and expressions.
- Should add gadget selectors implicitly
- Should allow modeling state machines gadgets
- Should make it easy to add negative tests
- A constraint checker should report the line and trace (in case of nested
  gadgets) of a failing constraint along with the values used in that
  constraint
- Advice and Expressions can be typed, and a checker will verify that the types
  are correct.

This is a list of nice to have features
- Witness assignment should be done automatically when possible

Open questions:
- How is composition modeled?
- How are dynamic lookups modeled?  What about composition via dynamic lookups?
- How does it work with the challenge API?

# Embeddable scripting languages for Rust

- https://github.com/pistondevelopers/dyon
- https://github.com/gluon-lang/gluon
- https://github.com/rune-rs/rune
- https://github.com/rhaiscript/rhai

# Gadgets

Aux

```
let from_bytes_le = |bytes| bytes.zip(0..bytes.len()).map(|(b, i)| b * 2.pow(8 * i)).sum();

fn from_bytes_le(bytes: &[T]) -> T {
    let mut res = 0;
    for i in 0..bytes.len() {
        res += b * 2.pow(8 * i)
    }
    res
}
```


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
gadget lt(N: usize, lhs: range(0, 2.pow(8*N)) expr, rhs: range(0, 2.pow(8*N)) expr) -> bool advice {
    let lt: bool advice;
    witness {
        lt = lhs < rhs;
    }
    @ lt in bool;
    let diff_bytes: [u8 advice; N];
    for i in 0..N {
        @ diff_bytes[i] in u8
    }
    witness {
        let diff: field = (lhs - rhs) + if lt { 2.pow(8*N) } else { 0 };
        for i in 0..N {
            diff_bytes[i] = (diff >> 8*i) & 0xff;
        }
    }
    let diff: range(0, 2.pow(8*N) expr = from_bytes_le(diff_bytes);
    @ lhs - rhs = diff - lt * 2.pow(8*N);
    return lt;
}
```

## Add256

inputs:
- `a: [u8 expr; 32]`
- `b: [u8 expr; 32]`

```
alias u128 = range(0, 2.pow(128));
gadget add256(a_le: [u8 expr; 32], b_le: [u8 expr; 32]) -> ([u8 advice; 32], bool advice) {
    let res_le: [u8 advice; 32];
    let carry_lo: range(0, 1) advice;
    let carry_hi: range(0, 1) advice;
    witness {
        let mut carry = 0;
        for i in 0..32 {
            let tmp = a_le[i] + b_le[i];
            res_le[i] = tmp & 0xff + carry;
            carry = tmp >> 8;
            if i == 15 {
                carry_lo = carry;
            }
        }
        carry_hi = carry;
    }

    let a_lo: u128 expr = from_bytes_le(a_le[..16]);
    let b_lo: u128 expr = from_bytes_le(b_le[..16]);
    let a_hi: u128 expr = from_bytes_le(a_le[16..]);
    let b_hi: u128 expr = from_bytes_le(b_le[16..]);
    let res_lo: u128 expr = from_bytes_le(res_le[..16]);
    let res_hi: u128 expr = from_bytes_le(res_le[16..]);
    @ a_lo + b_lo = res_lo + carry_lo * 2.pow(128);
    @ a_hi + b_hi + carry_lo = res_hi + carry_hi * 2.pow(128);
    @ carry_lo in [0, 1];
    @ carry_hi in [0, 1];
    return res_le;
}
```

