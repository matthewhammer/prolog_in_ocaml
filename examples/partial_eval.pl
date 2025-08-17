% peval_expr_language.pl
% Partial evaluator for a small expression language in Prolog.
% Source-level expressions:
%   int(N)                     - integer constant
%   var(X)                     - variable
%   add(E1,E2), mul(E1,E2)     - arithmetic
%   if(Cond,Then,Else)         - conditional (0 = false, non-zero = true)
%   fun(X,Body)                - anonymous function (lambda)
%   recfun(F,X,Body)           - named recursive function (F bound inside Body)
%   app(F,Arg)                 - application
%
% peval(+Expr, +Env, -Residual)
% Env is a list of Name-Value pairs where Value is a *residual* expression
% (e.g. int(5), var(x), fun(...), recfun(...), add(...), etc.).
% The partial evaluator reduces any subexpressions that can be reduced with
% respect to the environment, and leaves the rest as a residual expression.

% -------------------------
% lookup in environment
% -------------------------
lookup(X, [(X,V)|_], V) :- !.
lookup(X, [_|T], V) :- lookup(X, T, V).

% -------------------------
% main peval clauses
% -------------------------
peval(int(N), _, int(N)).

peval(var(X), Env, R) :-
    (   lookup(X, Env, V) ->
        % variable known in environment: residualize to bound value
        R = V
    ;   % unknown variable: keep symbolic
        R = var(X)
    ).

% arithmetic
peval(add(E1, E2), Env, R) :-
    peval(E1, Env, PE1),
    peval(E2, Env, PE2),
    simplify_add(PE1, PE2, R).

peval(mul(E1, E2), Env, R) :-
    peval(E1, Env, PE1),
    peval(E2, Env, PE2),
    simplify_mul(PE1, PE2, R).

% conditional: treat int(0) as false, any other int(_) as true
peval(if(Cond, Then, Else), Env, R) :-
    peval(Cond, Env, PCond),
    (   PCond = int(0) ->
        peval(Else, Env, R)
    ;   PCond = int(_) ->
        peval(Then, Env, R)
    ;   % condition unknown at PE time: residualize but PE branches too
        peval(Then, Env, PThen),
        peval(Else, Env, PElse),
        R = if(PCond, PThen, PElse)
    ).

% anonymous function: residualize body with the *current* environment
% (we keep functions as source-level fun/recfun forms in residual)
peval(fun(X, Body), Env, fun(X, PBody)) :-
    peval(Body, Env, PBody).

% recursive function: make the name visible inside the body when partially evaluating
peval(recfun(F, X, Body), Env, recfun(F, X, PBody)) :-
    % insert the recfun itself into the environment so recursive occurrences
    % of F are known while peval-ing Body. We insert the original recfun
    % (not the residual) so that var(F) resolves to a recfun(...) node.
    peval(Body, [(F, recfun(F, X, Body)) | Env], PBody).

% application: try to reduce the function and the argument; if function is
% known (fun/recfun), we perform a substitution (by extending env) and
% recursively peval the body.
peval(app(F, Arg), Env, R) :-
    peval(F, Env, PF),
    peval(Arg, Env, PArg),
    (   PF = fun(X, Body) ->
        % known anonymous function: bind parameter to PArg and peval body
        peval(Body, [(X, PArg) | Env], R)
    ;   PF = recfun(Fname, X, Body) ->
        % known recursive function: bind param and function name
        peval(Body, [(X, PArg), (Fname, recfun(Fname, X, Body)) | Env], R)
    ;   % unknown function at PE time: residual application
        R = app(PF, PArg)
    ).

% fallback clause (shouldn't be reached if all forms covered)
peval(Expr, _Env, Expr) :-
    % defensive: if we missed a case, just return expression unchanged
    Expr =.. [F|_],
    format('Warning: peval fallback for ~w~n', [F]).

% -------------------------
% simplification helpers
% -------------------------
simplify_add(int(A), int(B), int(R)) :- R is A + B.
simplify_add(E, int(0), E) :- !.
simplify_add(int(0), E, E) :- !.
simplify_add(E1, E2, add(E1, E2)).

simplify_mul(int(A), int(B), int(R)) :- R is A * B.
simplify_mul(_, int(0), int(0)) :- !.
simplify_mul(int(0), _, int(0)) :- !.
simplify_mul(E, int(1), E) :- !.
simplify_mul(int(1), E, E) :- !.
simplify_mul(E1, E2, mul(E1, E2)).

% -------------------------
% convenience: pretty-print residual with write/1 or portray
% -------------------------

% -------------------------
% Sample queries (copy-paste into SWI-Prolog)
% -------------------------
% 1) simple arithmetic with known variable
% ?- peval(add(mul(int(2), var(x)), add(var(y), int(3))), [(x,int(5))], PE).
% Expected: PE = add(int(10), add(var(y), int(3))).
%
% 2) conditional with known branch variable x but unknown z
% ?- peval(if(var(z), add(var(x), int(1)), int(0)), [(x,int(2))], PE).
% Expected: PE = if(var(z), int(3), int(0)).
%
% 3) application of anonymous function
% ?- peval(app(fun(x, add(x, y)), int(3)), [(y,int(5))], PE).
% Expected: PE = int(8).
%
% 4) recursive factorial
% ?- peval(app(recfun(fact, n,
%                     if(var(n), mul(var(n), app(var(fact), add(var(n), int(-1)))), int(1))),
%                 int(3)), [], PE).
% Expected: PE = int(6).
%
% 5) partially evaluate recursive with unknown argument
% ?- peval(app(recfun(fact, n,
%                     if(var(n), mul(var(n), app(var(fact), add(var(n), int(-1)))), int(1))),
%                 var(x)), [], PE).
% Expected: a residual app(recfun(...), var(x)).

% End of file

