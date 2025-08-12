# Tiny Prolog Interpreter in OCaml

This is a self-contained, minimal Prolog interpreter written in **OCaml** with support for the **Cut** (`!`) operator.  
It demonstrates the core ideas of Prolog resolution, backtracking, unification, and pruning the search space with cut.  

It’s intended for learning and experimentation, **not** as a complete Prolog system.

---

## Features

- Facts and rules
- Variables and unification
- Backtracking over multiple clauses
- Built-in `cut` operator (`!`) to prune choice points
- Simple list-based representation of terms
- Runs entirely in one `.ml` file

---

## Example Prolog Program

You can declare facts and rules like:

```ocaml
let prog = [
  Clause (Compound ("likes", [Atom "bob"; Atom "alice"]), []);
  Clause (Compound ("likes", [Atom "alice"; Atom "bob"]), []);
  Clause (Compound ("likes", [Atom "carol"; Atom "dave"]), []);
  Clause (Compound ("friends", [Var "X"; Var "Y"]),
          [Compound ("likes", [Var "X"; Var "Y"]);
           Compound ("likes", [Var "Y"; Var "X"])]);
  Clause (Compound ("mutual_friend_of", [Var "X"; Var "Z"]),
          [Compound ("friends", [Var "X"; Var "Y"]);
           Compound ("friends", [Var "Y"; Var "Z"])]);
  (* cut example: first_child(P, C) returns only the first child found *)
  Clause (Compound ("parent_of", [Atom "alice"; Atom "bob"]), []);
  Clause (Compound ("parent_of", [Atom "alice"; Atom "carol"]), []);
  Clause (Compound ("first_child", [Var "P"; Var "C"]),
          [Compound ("parent_of", [Var "P"; Var "C"]); Atom "!"])

]

let queries = [
  [Compound ("friends", [Var "A"; Var "B"])];
  [Compound ("likes", [Atom "bob"; Var "Who"])];
  [Compound ("mutual_friend_of", [Var "A"; Var "C"])];
  [Compound ("first_child", [Atom "alice"; Var "Who"])]
]
```

Running this initialization of the system produces this output:

```
Mini Prolog interpreter (with cut)

Query 1: friends(A, B)
Solution 1:
  B = alice
  A = bob
----
Solution 2:
  B = bob
  A = alice
----
Query 2: likes(bob, Who)
Solution 1:
  Who = alice
----
Query 3: mutual_friend_of(A, C)
Solution 1:
  C = bob
  A = bob
----
Solution 2:
  C = alice
  A = alice
----
Query 4: first_child(alice, Who)
Solution 1:
  Who = bob
----
Solution 2:
  Who = carol
----
```