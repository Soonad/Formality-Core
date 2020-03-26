Formality
=========

Formality is a dependently-typed programming language that enables developers to
use formal proofs to make their applications safer, faster and friendlier.

## Design Principles

**Portable:** Available everywhere, like a type-safe JSON for code. Formality
has a minimal core that bootstraps the language and can be quickly implemented
anywhere.

**Efficient:** On the web, Formality's JavaScript compiler is [competitive with
native JS
code](https://medium.com/@maiavictor/the-refreshing-simplicity-of-compiling-formality-to-anything-388a1616f36a).
On the blockchain, the EVM compiler is also extremely performant at
approximately [270 gas per
beta-reduction](https://medium.com/@maiavictor/compiling-formality-to-the-evm-99aec75677dd).
Additionally, Formality can compile to a new massively parallel,
non-garbage-collected, Lévy-optimal functional runtime.

**Accessible:** Usable by regular developers, not just experts. Formality has a
a familiar syntaxes that resembles popular languages and takes inspiration from
the [Zen of Python](https://www.python.org/dev/peps/pep-0020/).

## 0. Table of Contents

- [0. Table of Contents](#0-table-of-contents)
- [1. Formality-Core](#1-formality-core)
    - [1.0.0. Syntax](#100-syntax)
    - [1.0.1. Evaluation](#101-evaluation)
    - [1.0.2. Type-Checking](#102-type-checking)
- [2. Formality-Lang](#2-formality-lang)
- [3. Formality-Comp](#3-formality-comp)
- [4. Examples](#4-examples)
- [5. Problems](#5-problems)
- [6. Implementations](#6-implementations)
    - [6.0. Formality-Core](#60-formality-core)
        - [6.0.0. Haskell](#600-haskell)
        - [6.0.1. Python](#601-python)
        - [6.0.2. JavaScript](#602-javascript)

## 1. Formality-Core

Formality-Core is the minimal semantic core behind Formality. If you look at
Formality as a programming language, then Core is the minimal amount of features
required to derive everything else as libraries. If you look at it as proof
language, then Core is the set of axioms underlying the proof system. The
[Curry-Howard
correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)
describes both perspectives as essentially identical and implies that, in
principle, Formality is capable of expressing any mathematical statement.

In this section, we'll specify Formality-Core informally. Reference
implementations using several popular programming languages are provided in this
repository.

#### 1.0.0. Syntax

Formality-Core programs are split as modules (`Module`), each module containing
a number of definitions, each definition containing 2 expressions (`Term`), one
for its type and one for its value, each expression containing a number of
variables, references and other terms. The syntax of a `Term` is defined as
follows:

syntax                        | variant | meaning
----------------------------- | ------- | -------
`<name>`                      | Var     | a variable
`<name>`                      | Ref     | a reference
`Type`                        | Typ     | type of types
`(<var> : <term>) -> <term>`  | All     | dependent function type
`(<var> : <term>;) -> <term>` | All     | dependent function type (erased)
`(<var>) => <term>`           | Lam     | dependent function value
`(<var>;) => <term>`          | Lam     | dependent function value (erased)
`<term>(<term>)`              | App     | dependent function application
`<term>(<term>;)`             | App     | dependent function application (erased)
`#{<name>} <term>`            | Slf     | self type
`#inst{<term>} <term>`        | Ins     | self value
`#elim{<term>}`               | Eli     | self elimination
`<term> :: <term>`            | Ann     | inline annotation
`(<term>)`                    | -       | parenthesis

So, for example:

- `Type` is a valid term of variant `Typ`
- `(A : Type) -> Type` is a valid term of variant `All` containing a two valid terms of variant `Typ`.
- `foo(bar)` is a valid term of variant `App` containing two valid terms of
variant `Ref`.
- References and variables are both parsed as `<name>`, and desambiguated based on
context.

The syntax for a `<name>` is defined as a sequence of ASCII characters on the following set: 

```
a b c d e f g h i j k l m n o p q r s t u v w x y z
A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
0 1 2 3 4 5 6 7 8 9 _
```

In the reference implementations, terms and modules are represented with
algebraic datatypes, when available, or as a JSON emulating a tagged union, when
not. For example, in Haskell, we use `data`:

```haskell
-- Formality-Core term
data Term
  = Var Int                  -- Variable
  | Ref Name                 -- Reference
  | Typ                      -- Type type
  | All Eras Name Term Term  -- Forall, erased/unerased
  | Lam Eras Name Term       -- Lambda, erased/unerased
  | App Eras Term Term       -- Application, erased/unerased
  | Slf Name Term            -- Self-type
  | Ins Term Term            -- Self-type instantiation
  | Eli Term                 -- Self-type elimination
  | Ann Bool Term Term       -- Type annotation
  deriving (Eq, Show, Ord)

type Name = String
type Eras = Bool

-- Definition
data Def = Def { _name :: Name, _type :: Term, _term :: Term } deriving Show

-- Module
type Module = [Def]
```

In Python and JavaScript, we use functions that return a JSON with the contained
fields, and an additional "ctor" field to track the selected variant.

```python
def Var(indx):
    return {"ctor": "Var", "indx": indx}
```

The `Var` variant represents a variable bound by a function value (`Lam`), a
function type (`All`), or a self type (`Slf`). It stores a number representing
how many binders there are between its location and the location where it is
bound.

```python
def Ref(name):
    return {"ctor": "Ref", "name": name}
```

The `Ref` variant represents a reference, which is the usage of a top-level
definition. The `name` field stores the name of the referenced definition.

```python
def Typ():
    return {"ctor": "Typ"}
```

The `Typ` variant represents the type of types. Note that due to [Girard's
Paradox](https://en.wikipedia.org/wiki/System_U#Girard's_paradox) this would
appear to make Formality inconsistent as proof language by allowing the
proof of impossible propositions. Nevertheless, we recover consistency in a
subset of the language through the use of a consistency checker, whose design
will be explained later in this document.

```python
def All(eras,name,bind,body):
    return {"ctor": "All","eras": eras,"name": name,"bind": bind,"body": body}
```

The `All` variant represents the type of a function whose return type can depend
on its argument. This is also known as a dependent function type, a pi type, a
universal quantification, or a "forall". The `name` field stores its bound
variable name, the `bind` field stores the type of its argument, the `body`
field stores its return type, and the `eras` field represents its computational
relevance (whether the function is erased at runtime).

```python
def Lam(eras,name,body):
    return {"ctor": "Lam","eras": eras,"name": name,"body": body}
```

The `Lam` variant represents a pure function, also known as a lambda. The `name`
field stores its bound variable name, the `body` field stores its returned
expression, and the `eras` field represents its computational relevance.

```python
def App(eras,func,argm):
    return {"ctor": "App","eras": eras,"func": func,"argm": argm}
```

The `App` variant represents a function application. The `func` field stores the
function to be applied, and the `argm` field stores the argument. The `eras`
field, again, represents the computational relevance of the argument. Erased
lambdas can only be validly typed when applied to erased arguments.

```python
def Slf(name,type):
    return {"ctor": "Slf","name": name,"type": type}
```

The `Slf` variant represents a self type, which is a special kind of type which
can depend on its term-level value. The `name` field stores its bound variable
name representing the term, and the `type` field stores a type that can refer to
that term. Self types are used by Formality-Core to encode datatypes, which will be explained in more detail later.

```python
def Ins(type,term):
    return {"ctor": "Slf","type": type,"expr": expr}
```

The `Ins` variant represents the instantiation of a value of a self-type. The
`type` field stores the type of that value and the `expr` field represents the
value itself.

```python
def Eli(expr):
    return {"ctor": "Eli","expr": expr}
```
The `Eli` variant represents the use, inspection, or elimination of a self-type
value. The `expr` field stores the value to be inspected.

```python
def Ann(done,expr, type,):
    return {"ctor": "Ann","done": done,"expr": expr,"type": type}
```

The `Ann` variant represents an inline type annotation. The `expr` field
represents the annotated expression, and the `type` field represents its type.

As an example, the `(a) => (b) => (c) => a(b)(c)` term would be represented as:

```json
{
  "ctor": "Lam",
  "eras": false,
  "name": "a",
  "body": {
    "ctor": "Lam",
    "eras": false,
    "name": "b",
    "body": {
      "ctor": "Lam",
      "eras": false,
      "name": "c",
      "body": {
        "ctor": "App",
        "eras": false,
        "func": {
          "ctor": "App",
          "eras": false,
          "func": {
            "ctor": "Var",
            "indx": 2
          },
          "argm": {
            "ctor": "Var",
            "indx": 1
          }
        },
        "argm": {
          "ctor": "Var",
          "indx": 0
        }
      }
    }
  }
}
```

or as

```haskell
 (Lam False "a" (Lam False "b" (Lam False "c"
    (App False (App False (Var "a") (Var "b"))) (Var "c"))))
```

as a Haskell datatype.

And the `(A : Type;) -> (x : A) -> A` term would be represented as:

```json
{
  "ctor": "All",
  "eras": true,
  "name": "A",
  "bind": {
    "ctor": "Typ"
  },
  "body": {
    "ctor": "All",
    "eras": false,
    "name": "x",
    "bind": {
      "ctor": "Var",
      "indx": 0
    },
    "body": {
      "ctor": "Var",
      "indx": 1
    }
  }
}
```

or

```
(All True "A" Typ (All False "x" (Var 0) (Var 1)))
```

In reference implementations, parsing is done through a combination of small
backtracking parsers that receive the code to be parsed and return either a pair
with the leftover code and parsed value, or throw if the parser failed. The term
parser is divided in two phases: first, a base term is parsed, including the
variants `Var`, `Typ`, `All`, `Lam`, `Slf`, `Ins` and `Eli`. Afterwards, the
term is extended by postfix parsers, including the variants `App` and `Ann`.
Parsing involves subtle details that could differ among implementations. To
prevent confusion, the reference implementations in this repository are provided
to disambiguate and specificy the correct semantic behavior. These reference
parsers are *not* designed to be performant, and practical Formality parsers are
expected to differ significantly from them in implementation detail.

The syntax of a `Module` is defined as follows:

syntax                     | variant | meaning
-------------------------- | ------- | -------
`<term> : <term> <module>` | Def     | a top-level definition
`<eof>`                    | Eof     | the end of a module

Modules coincide with files, so, the end of a module should be parsed as
the end of the file. Whitespaces (newlines, tabs and spaces) are ignored. Here
is an example module:

```
identity : (A : Type) -> (a : A) -> A
  (A) => (a) => a

const : (A : Type) -> (a : A) -> (b : B) -> B
  (A) => (a) => (b) => B

apply_twice : (A : Type) -> (f : (x : A) -> A) -> (x : A) -> A
  (A) => (f) => (x) => f(f(x))
```

This module declares 3 top-level definitions, `identity`, `const` and
`apply_twice`. The last definition has `(A : Type) -> (f : (x : A) -> A) -> (x : A) -> A`
type and a `(A) => (a) => a` a value. That value consists of a function
(`{A} => ...`), that returns a function (`(f) => ...`), that returns a function
(`(x) => ...`), that returns `f` applied two times to `x`.

In reference implementations, module are represented as lists of `(name, type,
term)` unions. That is, in Python:

```python
def Ext(head, tail):
    return {"ctor": "Ext", "head": head, "tail": tail}

def Nil():
    return {"ctor": "Nil"}

def Def(name, type, term):
    return {"ctor": "Def", "name": name, "type": type, "term": term}
```

Here, `Nil` and `Ext` are list constructors. `Nil()` represents an empty list,
and `Ext(x, xs)` represents the list `xs` extended with the `x` value.

In Haskell,

```haskell
data Def = Def { _name :: Name, _type :: Term, _term :: Term }

type Module = [Def]
```

#### 1.0.1. Evaluation

Formality-Core is, in essence, just a lambda calculus (e.g. the subset
of languages like JavaScript or Python containing only anonymous functions). 

Its only primitive operation is the beta-reduction (function application): To evaluate a term in the shape `((x) => <body>)(<argm>)`, one must
replace every occurrence of `x` by `<argm>` in `<body>` in a
name-capture-avoiding manner.  Formally:

```
((x) => f)(a)
------------- beta-reduction
f[x <- a]
```

Where, the `f[x <- a]` notation describes "name-capture-avoiding" substitution.

Evaluating Formality-Core programs means applying functions repeatedly until
there is nothing left to do. This is a pure operation that can't output
messages, read packets or write files to disk; instead, it merely transforms an
expression into another, not unlike calling eval in a JavaScript expression
containing only numbers and arithmetic operations. 

As an example:

```
((x) => x(x))(y)
```

This is a function application after one beta reduction becomes:

```
x(x)[x <- y]
```

After completing the substitution and replacing all `x`s in `x(x)` with `y`, we
get the expression:

```
y(y)
```

Since there are no more beta-reductions left, this term is said to be
"fully-evaluated" or in "normal form".

Substitution is the most delicate part of beta-reduction. It is technically
simple, but can be tricky to get right due to "name capture". 

For example, consider the term:

```
(x) => ((a) => (x) => a)(x)
```

If reduced naively, the following the substition would result in the outer `x`
variable getting "captured" by the inner `x` lambda:

```
(x) => (x) => a[a <- x]
```

Which would evaluate incorrectly to

```
(x) => (x) => x
```

The correct substitution would first give all lambdas unique names:

```
(x) => ((a) => (y) => a)(x)
```

Then the name capture does not occcur:
```
(x) => (y) => a[a <- x]
```

This yields the correct term:

```
(x) => (y) => x
```

For a more thorough introduction to the lambda calculus, see either
[Rojas](http://www.inf.fu-berlin.de/lehre/WS03/alpi/lambda.pdf) or [Barendregt &
Barendson](http://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/geuvers.pdf)

Unlike other languages, Formality-Core doesn't define any evaluation order. It
could be evaluated strictly as in JavaScripy and Python, lazily as in Haskell,
or optimally through interaction nets. This subject will be covered on the
Formality-Comp section.

The reference implementation of evaluation uses high-order abstract syntax
(HOAS). That is, the syntax tree, usually stored as a JSON, is converted into a
representation that uses functions for binders like `Lam`. For example, the term
`((a) => (b) => b(a))(x => x)`, which would be represented as:

```json
{
  "ctor": "App",
  "func": {
    "ctor": "Lam",
    "name": "a",
    "body": {
      "ctor": "Lam",
      "name": "b",
      "body": {
        "ctor": "App",
        "func": {"ctor": "Var", "name": "b"},
        "argm": {"ctor": "Var", "name": "a"}
      }
    }
  },
  "func": {
    "ctor": "Lam",
    "name": "x",
    "body": {"ctor": "Var", "name": "x"}
  }
}
```

This is converted into a new "high-order" format that uses native functions
instead of variables:

```
{
  "ctor": "App",
  "func": {
    "ctor": "Lam",
    "name": "a",
    "body": a => {
      "ctor": "Lam",
      "name": "b",
      "body": b => {
        "ctor": "App",
        "func": b,
        "argm": a
      }
    }
  },
  "func": {
    "ctor": "Lam",
    "name": "x",
    "body": x => x
  }
}
```

The above expression can then be evaluated by finding redexes, that is,
sub-terms in the shape:

```
{"ctor": "App", "func": {"ctor": "Lam", "body": x => <BODY>}, "argm": <ARGM>}
```

These terms ar then replaced by the native function applications `(x => <BODY>)(<ARGM>)`. The example above becomes:

```
{
  "ctor": "Lam",
  "name": "b",
  "body": b => {
    "ctor": "App",
    "func": b,
    "argm": {"ctor": "Lam", "name": "x", "body": x => x}
  }
}
```

Which can then be converted back to a low-order term corresponding to
`(b) => b((x) => x)`, the normal form (result) of the example. Since this
process uses native functions under the hoods, it is both fast and simple to
implement. Note there are other ways to evaluate Formality-Core terms; this is
just the one used on the reference implementations.

### 1.0.2. Type-Checking

Type-checking is a computation step on terms that occurs in between parsing and
evaluation which prevents runtime errors by statically checking that certain
expectations hold. For example, if a function assumes an `Int` argument, calling
it with a `String` would be incorrect. Without types, that could result in a
(potentially disastrous) runtime bug. With types, the type-checker can catch
this issue before the program runs, i.e. before it can do any damage.

In Formality, types and programs coexist in the same level without any
distinction between them. Types are no different from numbers or strings. They
can be stored in tuples, returned from functions and so forth. This flexibility
gives Formality unrestricted static checking capabilities, allowing programmers
to verify at compile-time complex properties about the runtime behavior of their
programs.

For example, suppose you want to write a safe division function. In untyped
languages, you could do it as:

```javascript
function safe_div(a, b) {
  // Prevents non-numeric dividends
  if (typeof a !== "number") {
    throw "Dividend is not a number.";
  };

  // Prevent non-numeric divisors
  if (typeof a !== "number") {
    throw "Divisor is not a number.";
  };

  // Prevents division by zero
  if (b === 0) {
    throw "Attempted to divide by zero.";
  };

  return a / b;
};
```

While this prevents divisions of strings, or division by zero, it does so
through runtime checks. Not only does that imply extra runtime overhead, but the
program will still crash if the caller of `safe_div` didn't treat the
exceptions. Most statically typed languages such as TypeScript allow us to do
something a little better:

```typescript
function safe_div(a : Number, b : Number): Number {
  // Prevents division by zero
  if (b === 0) {
    throw "Attempted to divide by zero.";
  };

  return a / b;
};
```

Here, `a` and `b` are statically checked to be numbers, so we don't need to
check their types at runtime. Writing `safe_div("foo","bar")` would be a
compile-time error and never go into production undetected. The problem is, we
still need to check if `b` is zero. That's because the type-systems of TypeScript
as well most other statically typed languages have an expressivity barrier that
doesn't allow it to reason about the values of computations. Fixing that lack of
expressivity is the main benefit of "first-class types" that allow types to be
treated as values.

In Formality, we could write:

```
NonZero(x : Number) : Type
  x != 0

safe_div(a : Number, b : Number, e : NonZero(b);): Number
  a / b
```

Here, `NonZero(b)` is statically, symbolically checked proof that `b` is
different from zero. No runtime checks would be needed, no runtime errors would
be possible, and calling `safe_div` incorrectly would be immediately reported as
a compile error. Note also that since the `e` argument is annotated with the `;`
erasure symbol, it is marked as computationally irrelevant, and is removed at
runtime. This means that `safe_div` is not only safe, but is just as fast and
low-overhead as running the bare `a / b` operation.

In a similar fashion, we could use types to express arbitrarily precise
invariants and expectations, allowing us to go as far as proving mathematical
theorems about the behavior of our programs. Of course, all this power is
optional: one can use Formality as if it were TypeScript by simply writting less
precise types.

As complex as all that sounds, type-checking Formality-Core expressions is
actually surprisingly simple; Here is the type-checker from the JavaScript reference
implementation:

```javascript
function typecheck(term, type = null, ctx = Nil()) {
  var type = type ? reduce(type) : null;
  switch (term.ctor) {
    case "Var":
      var got = find(ctx, (x,i) => i === term.indx);
      if (got) {
        return shift(got.value, got.index + 1, 0);
      } else {
        throw new Error();
      }
    case "Typ":
      return Typ();
    case "All":
      var bind_typ = typecheck(term.bind, Typ(), ctx);
      var body_ctx = Ext(term.bind, ctx);
      var body_typ = typecheck(term.body, Typ(), body_ctx);
      return Typ();
    case "Lam":
      switch (type.ctor) {
        case "All":
          var body_ctx = Ext(type.bind, ctx);
          var body_typ = typecheck(term.body, type.body, body_ctx);
          return All(term.name, type.bind, body_typ, term.eras);
        default:
          throw "Lambda has a non-function type.";
      }
    case "App":
      var func_typ = reduce(typecheck(term.func, null, defs, ctx));
      switch (func_typ.ctor) {
        case "All":
          var argm_typ = typecheck(term.argm, func_typ.bind, ctx);
          var term_typ = reduce(subst(func_typ, term.argm));
          return term_typ;
        default:
          throw "Non-function application.";
      };
    case "Slf":
      var type_ctx = Ext(term, ctx);
      var type_typ = typecheck(term.type, typ, ctx);
      return Typ();
    case "Ins":
      var term_typ = reduce(term.type);
      switch (term_typ.ctor) {
        case "Slf":
          var self_typ = subst(term_typ.type, Ann(term.type, term, true), 0);
          var expr_typ = typecheck(term.expr, self_typ, ctx);
          return term.type;
        default:
          throw "Non-self instantiation.";
      };
    case "Eli":
      var expr_typ = reduce(typecheck(term.expr, null, ctx));
      switch (expr_typ.ctor) {
        case "Slf":
          return subst(expr_typ.type, term.expr, 0);
        default:
          throw "Non-self elimination.";
      };
    case "Ann":
      if (term.done) {
        return term.type;
      } else {
        return typecheck(term.expr, term.type, ctx);
      }
  };
};
```

(... to be continued ...)

## 6. Implementations

(Check the other files on this repository for the reference implementations.
Those will be added to this paper when finished!)
