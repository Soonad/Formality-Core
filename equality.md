# System-ϝ  equality algorithm

`System-ϝ` terms are defined as follows:

```
<term> :=
  | <number>_<number>        -- variable
  | <name>                   -- reference to a recursion
  | Type                     -- the type of types
  | μ <name>. <term>         -- recursion
  | ∀ <term> <term>          -- forall
  | λ <term>                 -- lambda
  | (<term> <term)           -- application
  | let <name> <term> <term> -- let expression
  | : <term> <term>          -- type annotation
```

Variables contain a pair of two indices: First, a relative index which indicates
the number of binders between the variable and its binder (De Bruijn index).
Second, a subscript which indicates the depth of the variables binder.

For example

```
0 1 2 3
λ λ λ λ 1_2
3 2 1 0
```

Here the variable `1_2` points to the third lambda from the left, which is `1`
lambda away from the variable and is at depth `2` in the term.

Informally, for a variable at depth `d + 1`

```
0    1    ... d
λ    λ    ... λ   x_y
d (d - 1) ... 0
```

we can see that for any lambda, its depth plus its distance from the variable
equal `d`, therefore for any `x_y`, `x + y = d = depth - 1`

Looking at the action of `μ` on variables:

When the lambda is inside the `μ` the relative index is constant but the
absolute index diverges:

```
μ x. λ 0_0 x
λ 0_0 (μ x. λ 0_1 x)
λ 0_0 (λ 0_1 (μ x. λ 0_2 x))
...
```

When the lambda is outside the `μ` and there is an intervening lambda within the
`μ` then the relative index diverges but the absolute index is constant

```
λ (μ x. λ 1_0 x)
λ (λ 1_0 μ x. λ 2_0 x)
λ (λ 1_0 (λ 2_0 (μ x. λ 3_0 x)))
...
```

## Bohm Tree

A bohm tree is the structure formed by the possible reductions on a term:

```
   ((λy.y) z)
        |
        z
```

```
                 (((λy.y) (λz.z)) ((λx.x) w))
            /                                 \
   ((λz.z) ((λx.x) w))                 (((λy.y) (λz.z)) w)
      /         \                               |
((λx.x) w))   ((λz.z) w)                    ((λz.z) w)
      |                                         |
      w                                         w
```

Terms can be:

- normalizable, as in the above case, which is when their bohm
trees are finite (TODO: prove local confluence of System-ϝ, i.e. all leaves are
the same)

- regular

- irregular

- divergent




