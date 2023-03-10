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
- if b(x) is truthy then BOOLY(e(x)) is false
> e * p

IF (e: bool) THEN e1: expr ELSE e2: expr
- if e(x) is true then e1(x) == 0, else e2(x) == 0
> e * e1
> (1 - e) * e2

e1: booly AND e2:booly -> booly
> e1 * e2

e1: bool AND e2:bool -> bool
> e1 * e2

e1: bool OR e2:bool -> bool
> e1 + e2 - e1 * e2
> [alt] 1 - ((1 - e1) * (1 - e2)) = 1 - (1 - e2 - e1 + e1 * e2) = e1 + e2 - e1 * e2 # DeMorgan

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

# Polynomail constraint analysis



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
- https://github.com/RustPython/RustPython

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
    let value_inv: witness;
    witness {
        value_inv = if value != 0 {
            value.invert();
        } else {
            0
        };
    }
    let is_zero_expression: bool expr = 1 - value * value_inv;
    @ value * value_inv = 0;
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
gadget lt(N: usize, lhs: T2P8 expr, rhs: T2P8 expr) -> bool witness 
    where T2P8 is range(0, 2.pow(8*N)) {
    let lt: bool witness;
    witness {
        lt = lhs < rhs;
    }
    let diff_bytes: [u8 witness; N];
    witness {
        let diff: field = (lhs - rhs) + if lt { 2.pow(8*N) } else { 0 };
        for i in 0..N {
            diff_bytes[i] = (diff >> 8*i) & 0xff;
        }
    }
    let diff: T2P8 expr = from_bytes_le(diff_bytes);
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
gadget add256(a_le: [u8 expr; 32], b_le: [u8 expr; 32]) -> ([u8 witness; 32], bool witness) {
    let res_le: [u8 witness; 32];
    let carry_lo: range(0, 1) witness;
    let carry_hi: range(0, 1) witness;
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
    return res_le;
}
```

## Bytecode circuit

An example of a state machine + lookupable table circuit

https://hackmd.io/Cv5Pmh8fRyuuuwCFcCZdzg

Types: 
- Tag: enum{ Length, Byte }
- Word: [u128, u128]

BytecodeLookup:
- codeHash: Word
- tag: Tag
- index: u16
- value: u8

State:
- tag: Tag
- length: u16
- index: u16
- value: u8
- is_code: bool
- push_data_size: u16
- push_data_left: u16
- hash: Word
- values_rlc: field
- is_first: bool fixed
- is_last: bool fixed

Witness: list of State structs with the following values defined:
- tag
- if tag == Length
    - length
    - hash
- if tag == Byte
    - value

```
circuit bytecode(curr: State, next: State) {
    // Length state validation
    if curr.tag == Length {
        @ curr.index = 0;
        @ curr.value = curr.length;
        if curr.length == 0 {
            @ curr.hash = EMPTY_HASH;
        }
    }
    // Byte state validation
    if curr.tag == Byte {
        @ curr.push_data_size = push_data_size_table[curr.value];
        @ curr.is_code = (curr.push_data_left == 0);
        if curr.is_code {
            @ next.push_data_left = curr.push_data_size;
        } else {
            @ next.push_data_left = curr.push_data_left - 1;
        }
    }

    // Start state
    if curr.is_first {
        @ curr.tag = Tag.Length;
    } 
    // End state
    if curr.is_last {
        @ curr.tag = Tag.Length;
    }

    // State transition validation
    if !curr.is_last {
        // Length -> Byte
        if curr.tag == Length and next.tag == Byte {
            @ next.length = curr.length;
            @ next.index = 0;
            @ next.is_code = 1;
            @ next.hash = curr.hash;
            @ next.values_rlc = next.value;
            @ next.value = any;
            @ next.push_data_left = any;
        }

        // Length -> Length
        if curr.tag == Length and next.tag == Length {
            @ curr.length = 0;
            @ curr.hash = EMPTY_HASH;
            @ next.length = any;
            @ next.index = any;
            @ next.value = any;
            @ next.is_code = any;
            @ next.push_data_left = any;
            @ next.hash = any;
            @ next.values_rlc = any;
        }

        // Byte -> Byte
        if curr.tag == Byte and next.tag == Byte {
            @ next.length = curr.length;
            @ next.index = curr.index + 1;
            @ next.hash = curr.hash;
            @ next.values_rlc = curr.values_rlc * randomness + curr.value;
            @ next.value = any;
        }

        // Byte -> Length
        if curr.tag == Byte and next.tag == Length {
            @ curr.index = curr.length - 1;
            @ curr.hash = keccak256[curr.values_rlc, curr.length];
            @ next.length = any;
            @ next.index = any;
            @ next.value = any;
            @ next.hash = any;
            @ next.values_rlc = any;
        }
    }
}
```

Exercice: write a function that given a list of byte vectors, generates the list of Bytecode
circuit states.

```
fn gen(inputs: &[Vec<u8>]) -> Vec<State> {
    let mut states = Vec::new();
    for input in inputs {
        states.push(State{
            tag: Lenght,
            value: input.len(),
            hash: rlc(r, hash(input)),
        });
        for byte in input {
            states.push(State{
                tag: Byte,
                value: byte,
            });
        }
    }
}
```
