# Rust-Style Ownership/Borrow Checking in Prolog
## Comparison: Backwards vs Forward Analysis

---

## 1. Purpose

Both approaches aim to detect violations of Rust-style ownership and borrowing rules:

- Ownership states: `owned`, `shared_borrow`, `mutable_borrow`
- Violations: double mutable borrow, mutable + shared borrow, freeing while borrowed

The approaches differ in direction of analysis and how requirements or state are propagated.

---

## 2. Backwards Analysis

### Key Idea

- Propagate ownership/borrow requirements backward from uses/consumers to their origins.
- Violations are inferred by checking if the requirements conflict along live paths.

### How it Works

1. CFG edges remain successors (natural program flow).
2. At each node, query successors to see what ownership/borrow requirements exist.
3. Tabling ensures fixed-point convergence, including loops/cycles.
4. Liveness tracking: a variable’s requirements are only relevant while it may be used along some path.

### Pros

- Declarative and elegant in Prolog (tabling handles loops naturally).
- Natural for requirement-driven rules (what must hold to satisfy future uses).
- Easy to integrate borrow lifetimes via liveness.

### Cons

- Violations are detected retroactively, based on propagated requirements.
- May be less intuitive if thinking operationally about current ownership state.

---

## 3. Forward Analysis

### Key Idea

- Propagate current ownership/borrow state forward along CFG edges.
- Violations are detected immediately when a node would introduce a conflict.

### How it Works

1. At program entry, start with initial variable states.
2. Each statement updates the current state of variables and active borrows.
3. Violations are recorded as soon as conflicts occur:
   - Mutable borrow conflicts with existing borrow(s)
   - Free while borrowed
4. Tabling handles loops/cycles by computing fixed-point state.

### Pros

- Operationally intuitive: state always reflects current ownership/borrows.
- Immediate violation detection; easy to report precise error location.
- Can naturally handle incremental program analysis.

### Cons

- Must explicitly track active borrows and state at each node.
- More operational; can be less declarative than requirement-driven backward analysis.
- Liveness has to be encoded into the forward state if you want precise Rust-style lifetime tracking.

---

## 4. Comparison Table

| Feature                     | Backwards Analysis                           | Forward Analysis                               |
|-------------------------------|--------------------------------------------|-----------------------------------------------|
| Direction                    | From uses backward                          | From entry forward                             |
| Key Concept                  | Requirements propagate backward             | Current state propagates forward               |
| Violation Detection          | Retroactively inferred via requirements     | Immediate, as state updates                     |
| Liveness / borrow lifetimes  | Natural to integrate via backward propagation | Must encode live variables in state           |
| Tabling / fixed-point        | Handles loops naturally                     | Handles loops naturally                         |
| Intuition                    | What must hold to satisfy future uses      | What is currently owned/borrowed               |
| Pros                         | Declarative, clean, elegant                 | Operationally intuitive, immediate feedback    |
| Cons                         | Less intuitive for current state            | More operational, needs explicit state tracking|

---

## 5. Summary

- Backwards analysis is well-suited for declarative, requirement-driven reasoning, naturally handling borrow lifetimes with tabling.
- Forward analysis is more operational, tracking current ownership/borrows and detecting violations immediately.
- Both approaches are valid; the choice depends on whether you prefer a declarative fixed-point style or an immediate, state-based style.

---

*Optional next step:* Add a diagram showing the CFG with arrows labeled "backward propagation" vs "forward state propagation" to make the comparison even clearer.

