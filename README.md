# Nat2

Do the natural numbers start from 0 or 1?

Well, why not make everyone angry and make them start from 2 instead?

This repository contains several basic [Lean 4](https://lean-lang.org/) theorems for the type `Nat2` defined as:

```lean
inductive Nat2 where
  | two : Nat2
  | succ : Nat2 → Nat2
```

Addition and multiplication are defined as follows:

```lean
def add : Nat2 → Nat2 → Nat2
  | a, two => succ (succ a)
  | a, succ b => succ (add a b)

def mul: Nat2 → Nat2 → Nat2
  | a, two => add a a
  | a, succ b => add (mul a b) a
```

The base cases for these are more "interesting" than the usual making proofs harder.

The theorems are inspired by the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4). **Beware:** The authors of this game has not seen the light and thus uses natural numbers starting from 0.
