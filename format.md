# plaf: Plonkish Arithmetization Format

Original notes for Plaf.  The current implementation is slightly different.

```
[info]
name = "Circuit Foo"
size = 4096 # k = 12

[columns.witness]
w0 = {}
w1 = {}
w2 = { phase = 2 } # dictionary allows adding extra properties to witness columns

[columns.fixed]
q0 = {}
q1 = {}
q2 = {}
q3 = {}

[constraints.poly]
"gate 1" = "q0 * ((w0 - 0) * (w0 - 1))"
"gate 2" = "q1 * (w0 - w1)"
"gate 3" = "q2 * w0 * w1 * w2"
"gate 4" = "q3 * (w1[1] = w0[0])"

[constraints.lookup]
"lookup 1" = [["w0", "w1"], ["w2[0]", "w2[1]"]]
"lookup 2" = [["w0", "w0 + w1"], ["w2 + w2", "q0 * w2"]]

[[constraints.copy]]
columns = ["w0", "w1"]
offsets = [[0, 10], [1, 11], [2, 12]]

[[constraints.copy]]
columns = ["w0", "w2"]
offsets = [[0, 1], [2, 3], [4, 5]]
```

# cova: Column Values

## covab: Column Values in Binary

## covat: Column Values in Text

It's just CSV, where values can be in decimal (with "-" to negate), hex (with "0x" prefix)
The first line contains the column names, the rest are values. which can be skipped to mean
unassigned (0).

Why CSV?  Because it's the simplest text format to encode table values, and it can be easily
imported into sqlite to explore big tables.

```
w0,w1,w2
12,0x4,-1
,,33
12345,88,0x124
```

```
q0,q1,q2,q3
,,,1
1,1,
1,,,
```
