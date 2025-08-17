% -------------------------------------------------------------------
% backward_ownership_liveness.pl
%
% A declarative, backwards Rust-style ownership and borrow checker
% with proper liveness tracking in Prolog.
%
% Design highlights:
% 1. Backwards analysis: ownership/borrow requirements propagate backward
%    across successors in the CFG.
% 2. Functional/tabling: fully declarative, no assertz/retract.
% 3. Borrow tracking: owned | shared_borrow | mutable_borrow.
% 4. Liveness: borrows are only relevant while variables are live; frees
%    are illegal if the variable is live.
% -------------------------------------------------------------------

:- table ownership/3.
:- table live/2.

% -------------------------------------------------------------------
% Control Flow Graph (CFG)
% Each node: ID, statement, list of successors
% Statements:
%   assign(Var, Expr)
%   call(Fun, Args, Mode)       Mode = borrow | own
%   branch(Cond, Then, Else)
%   allocate(Var)
%   free(Var)
%   borrow(BorrowVar, Var, Kind) Kind = shared_borrow | mutable_borrow
% -------------------------------------------------------------------

cfg(1, allocate(p), [2]).
cfg(2, assign(q, p), [3]).
cfg(3, borrow(r, q, shared_borrow), [4]).
cfg(4, call(foo, [r], borrow), [5]).
cfg(5, branch(cond, 6, 7), []).
cfg(6, free(p), []).
cfg(7, free(r), []).

% -------------------------------------------------------------------
% Liveness Analysis (backwards)
% live(Node, Var) is true if Var may be used along some path from Node
% -------------------------------------------------------------------

% Variable used directly in this statement
live(Node, Var) :-
    cfg(Node, Stmt, _),
    used_in_stmt(Stmt, Var).

% Variable live in any successor
live(Node, Var) :-
    cfg(Node, _, Next),
    member(NextNode, Next),
    live(NextNode, Var).

% Determine variables used in a statement
used_in_stmt(assign(Var, Expr), Var).
used_in_stmt(assign(Var, Expr), Expr).
used_in_stmt(borrow(BorrowVar, Var, _Kind), Var).
used_in_stmt(borrow(BorrowVar, Var, _Kind), BorrowVar).
used_in_stmt(call(_, Args, _Mode), Var) :-
    member(Var, Args).
used_in_stmt(free(Var), Var).

% -------------------------------------------------------------------
% Ownership and Borrow Requirements
% ownership(Node, Var, Status)
% Status = owned | shared_borrow | mutable_borrow
% -------------------------------------------------------------------

% Free: must be owned
ownership(Node, Var, owned) :-
    cfg(Node, free(Var), _).

% Allocation: introduces ownership
ownership(Node, Var, owned) :-
    cfg(Node, allocate(Var), _).

% Borrow: original variable must be owned
ownership(Node, Var, owned) :-
    cfg(Node, borrow(_, Var, _), _).

% Borrowed variable itself: status is the borrow kind
ownership(Node, BorrowVar, Kind) :-
    cfg(Node, borrow(BorrowVar, _, Kind), _).

% Assignment: propagate requirements from successors
ownership(Node, Expr, Status) :-
    cfg(Node, assign(Var, Expr), Next),
    ownership_in_successor(Var, Status, Next).

% Call handling
ownership(Node, Var, shared_borrow) :-
    cfg(Node, call(_, Args, borrow), _),
    member(Var, Args).

ownership(Node, Var, owned) :-
    cfg(Node, call(_, Args, own), member(Var, Args)).

% Branch: propagate from both branches
ownership(Node, Var, Status) :-
    cfg(Node, branch(_, Then, Else), _),
    ownership(Then, Var, Status),
    ownership(Else, Var, Status).

% -------------------------------------------------------------------
% Helper: query successors for ownership/borrow requirement
% -------------------------------------------------------------------
ownership_in_successor(Var, Status, [NextNode|_]) :-
    ownership(NextNode, Var, Status), !.
ownership_in_successor(Var, Status, [_|Rest]) :-
    ownership_in_successor(Var, Status, Rest).

% -------------------------------------------------------------------
% Violation detection (considering liveness)
% -------------------------------------------------------------------

% Mutable borrow conflicts with any other borrow while live
violated(Node, Var) :-
    live(Node, Var),
    ownership(Node, Var, mutable_borrow),
    ( ownership(Node, Var, shared_borrow)
    ; ownership(Node, Var, mutable_borrow) ).

% Shared borrow conflicts with a mutable borrow while live
violated(Node, Var) :-
    live(Node, Var),
    ownership(Node, Var, shared_borrow),
    ownership(Node, Var, mutable_borrow).

% Free conflicts with any live borrow
violated(Node, Var) :-
    cfg(Node, free(Var), _),
    live(Node, Var),
    ownership(Node, Var, shared_borrow).

violated(Node, Var) :-
    cfg(Node, free(Var), _),
    live(Node, Var),
    ownership(Node, Var, mutable_borrow).

% -------------------------------------------------------------------
% Example queries:
% 1. List ownership/borrow requirements at each node
%    ?- ownership(Node, Var, Status).
%
% 2. Check violations
%    ?- violated(Node, Var).
% -------------------------------------------------------------------
