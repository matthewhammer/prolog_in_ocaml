% -------------------------------------------------------------------
% backward_ownership.pl
%
% A declarative, backwards ownership checker for a simple imperative
% language in Prolog. 
%
% Design highlights:
% 1. Backwards Analysis:
%    - We propagate ownership requirements "backwards" through the CFG.
%    - CFG edges are stored as successors (natural program flow), but
%      ownership requirements flow from successors to the current node.
%    - This is done declaratively: at each node, we ask "what do my
%      successors require?" and propagate those requirements to this node.
%
% 2. Functional/Declarative Design:
%    - No assertz/retract; no global mutable state.
%    - Tabling is used to memoize ownership facts, so loops/cycles
%      converge naturally to a fixed point.
%    - The analysis is demand-driven: facts are computed when queried.
%
% -------------------------------------------------------------------

:- table ownership/3.

% -------------------------------------------------------------------
% Control Flow Graph (CFG)
% Each node has an ID, a statement, and a list of successor nodes.
% Statements:
%   assign(Var, Expr)
%   call(Fun, Args, Mode)       Mode = borrow | own
%   branch(Cond, ThenNode, ElseNode)
%   allocate(Var)
%   free(Var)
%   borrow(Var, Var2)           Var2 borrows from Var
% -------------------------------------------------------------------

cfg(1, allocate(p), [2]).
cfg(2, assign(q, p), [3]).
cfg(3, borrow(r, q), [4]).
cfg(4, call(foo, [r], borrow), [5]).
cfg(5, branch(cond, 6, 7), []).
cfg(6, free(p), []).
cfg(7, free(r), []).

% -------------------------------------------------------------------
% Ownership Requirements
% ownership(Node, Var, Status)
% Status = owned | borrowed
% This table computes, for a given node and variable, what ownership
% requirement must hold at that point, by looking at successor nodes.
% -------------------------------------------------------------------

% Free: variable must be owned to safely free it
ownership(Node, Var, owned) :-
    cfg(Node, free(Var), _).

% Allocation: variable becomes owned
ownership(Node, Var, owned) :-
    cfg(Node, allocate(Var), _).

% Borrow: original variable must be owned
ownership(Node, Var, owned) :-
    cfg(Node, borrow(_, Var), _).

% Assignment: if the assigned variable is required in a successor,
% propagate that requirement to the source expression
ownership(Node, Expr, Status) :-
    cfg(Node, assign(Var, Expr), Next),
    ownership_in_successor(Var, Status, Next).

% Call: borrowed arguments require only borrowing
ownership(Node, Var, borrowed) :-
    cfg(Node, call(_, Args, borrow), _),
    member(Var, Args).

% Call: owned arguments require full ownership
ownership(Node, Var, owned) :-
    cfg(Node, call(_, Args, own), _),
    member(Var, Args).

% Branch: propagate requirements from both branches
ownership(Node, Var, Status) :-
    cfg(Node, branch(_, Then, Else), _),
    ownership(Then, Var, Status),
    ownership(Else, Var, Status).

% -------------------------------------------------------------------
% Helper: check successors for ownership requirements
% -------------------------------------------------------------------
ownership_in_successor(Var, Status, [NextNode|_]) :-
    ownership(NextNode, Var, Status), !.
ownership_in_successor(Var, Status, [_|Rest]) :-
    ownership_in_successor(Var, Status, Rest).

% -------------------------------------------------------------------
% Detect violations
% A violation occurs if a variable at a node is required to be both
% owned and borrowed at the same time
% -------------------------------------------------------------------
violated(Node, Var) :-
    ownership(Node, Var, owned),
    ownership(Node, Var, borrowed).

% -------------------------------------------------------------------
% Example usage:
% 1. List ownership requirements at all nodes
%    ?- ownership(Node, Var, Status).
%
% 2. Check for any ownership violations
%    ?- violated(Node, Var).
% -------------------------------------------------------------------
