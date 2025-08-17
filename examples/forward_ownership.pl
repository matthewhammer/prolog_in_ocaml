% -------------------------------------------------------------------
% forward_ownership.pl
%
% A declarative forward Rust-style ownership and borrow checker in Prolog.
%
% Design highlights:
% 1. Forward analysis: ownership/borrow state propagates along CFG edges.
% 2. Tracks active borrows explicitly at each node.
% 3. Detects violations immediately (conflicting borrows, illegal frees).
% 4. Tabling ensures fixed-point computation for loops/cycles.
% -------------------------------------------------------------------

:- table state_at/3.

% -------------------------------------------------------------------
% CFG Representation
% -------------------------------------------------------------------
cfg(1, allocate(p), [2]).
cfg(2, assign(q, p), [3]).
cfg(3, borrow(r, q, shared_borrow), [4]).
cfg(4, call(foo, [r], borrow), [5]).
cfg(5, branch(cond, 6, 7), []).
cfg(6, free(p), []).
cfg(7, free(r), []).

% -------------------------------------------------------------------
% Ownership/Borrow state propagation
%
% state_at(Node, VarStates, Violations)
%   VarStates = list of var(Status)
%   Violations = list of violation(Node, Var, Reason)
% -------------------------------------------------------------------

% Base case: start of program, no variables yet
state_at(1, [], []).

% Forward propagation through CFG
state_at(NextNode, NextVarStates, NextViolations) :-
    cfg(Node, Stmt, Next),
    member(NextNode, Next),
    state_at(Node, VarStates, Violations),
    apply_stmt_forward(Stmt, VarStates, UpdatedVarStates, Violations, UpdatedViolations),
    NextVarStates = UpdatedVarStates,
    NextViolations = UpdatedViolations.

% -------------------------------------------------------------------
% Apply statement to current variable state
% -------------------------------------------------------------------
apply_stmt_forward(allocate(Var), VarStates, UpdatedVarStates, Violations, Violations) :-
    % Allocate: now owned
    update_var_state(Var, owned, VarStates, UpdatedVarStates).

apply_stmt_forward(assign(Var, Expr), VarStates, UpdatedVarStates, Violations, Violations) :-
    % Assignment propagates ownership from Expr to Var
    find_var_state(Expr, VarStates, ExprStatus),
    update_var_state(Var, ExprStatus, VarStates, UpdatedVarStates).

apply_stmt_forward(borrow(BorrowVar, Var, Kind), VarStates, UpdatedVarStates, Violations, UpdatedViolations) :-
    find_var_state(Var, VarStates, VarStatus),
    ( conflict_borrow(VarStatus, Kind) ->
        UpdatedViolations = [violation(BorrowVar, Var, Kind)|Violations],
        UpdatedVarStates = VarStates
    ;
        update_var_state(BorrowVar, Kind, VarStates, TempStates),
        UpdatedVarStates = TempStates,
        UpdatedViolations = Violations
    ).

apply_stmt_forward(free(Var), VarStates, VarStates, Violations, UpdatedViolations) :-
    find_var_state(Var, VarStates, Status),
    ( Status = owned ->
        UpdatedViolations = Violations
    ;
        UpdatedViolations = [violation(Var, free, Status)|Violations]
    ).

apply_stmt_forward(call(_, Args, borrow), VarStates, UpdatedVarStates, Violations, UpdatedViolations) :-
    % Borrow call: mark args as borrowed (shared)
    foldl(mark_borrow(VarStates), Args, VarStates, UpdatedVarStates),
    UpdatedViolations = Violations.

apply_stmt_forward(call(_, Args, own), VarStates, UpdatedVarStates, Violations, UpdatedViolations) :-
    % Own call: ownership is passed
    foldl(mark_owned(VarStates), Args, VarStates, UpdatedVarStates),
    UpdatedViolations = Violations.

apply_stmt_forward(branch(_, Then, Else), VarStates, VarStates, Violations, Violations) :-
    % Branch: no immediate state change; forward propagation handles successors
    true.

% -------------------------------------------------------------------
% Helper predicates
% -------------------------------------------------------------------

% Update or insert variable state
update_var_state(Var, Status, VarStates, UpdatedVarStates) :-
    select(var(Var, _), VarStates, Rest) ->
        UpdatedVarStates = [var(Var, Status)|Rest]
    ; UpdatedVarStates = [var(Var, Status)|VarStates].

% Find variable state
find_var_state(Var, VarStates, Status) :-
    member(var(Var, Status), VarStates), !.
find_var_state(_, _, uninitialized).

% Check for borrow conflicts
conflict_borrow(owned, shared_borrow) :- false.
conflict_borrow(owned, mutable_borrow) :- false.
conflict_borrow(shared_borrow, mutable_borrow) :- true.
conflict_borrow(mutable_borrow, _) :- true.
conflict_borrow(uninitialized, _) :- false.

% Mark variable as borrowed (shared)
mark_borrow(VarStates, Var, Acc, UpdatedAcc) :-
    update_var_state(Var, shared_borrow, Acc, UpdatedAcc).

% Mark variable as owned
mark_owned(VarStates, Var, Acc, UpdatedAcc) :-
    update_var_state(Var, owned, Acc, UpdatedAcc).

% -------------------------------------------------------------------
% Example queries:
% 1. List state at a node
%    ?- state_at(Node, VarStates, Violations).
%
% 2. Check violations anywhere
%    ?- state_at(_, _, Violations), member(V, Violations).
% -------------------------------------------------------------------
