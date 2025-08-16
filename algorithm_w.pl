% Hindley–Milner type inference in ISO Prolog
% Features: variables, lambda, application, let, letrec, pairs, unit.

:- op(500, xfy, '->').   % infix arrow for types

% fresh_typevar(+N0,-N1,-T)
% N0 = input counter, N1 = updated counter, T = fresh type variable
fresh_typevar(N0, N1, tvar(N0)) :-
    N1 is N0 + 1.

% free type vars in a type
ftv(tvar(X), [X]).
ftv(arrow(T1,T2), Vs) :-
    ftv(T1,V1), ftv(T2,V2),
    append(V1,V2,V0), sort(V0,Vs).
ftv(pair(T1,T2), Vs) :-
    ftv(T1,V1), ftv(T2,V2),
    append(V1,V2,V0), sort(V0,Vs).
ftv(unit, []).

% free type vars in a scheme
ftv_scheme(scheme(Vs,T), Out) :-
    ftv(T,F), subtract(F,Vs,Out).

% free type vars in env
ftv_env([],[]).
ftv_env([_-Sch|E],Vs) :-
    ftv_scheme(Sch,V1), ftv_env(E,V2),
    append(V1,V2,V0), sort(V0,Vs).

% instantiate scheme to fresh type
instantiate(scheme(Vs,T), N0, N1, T1) :-
    maplist(fresh_typevar_acc, Vs, N0, N1, Subs),
    copy_with_subs(T, Subs, T1).

fresh_typevar_acc(_, N0, N1, X-tvar(N0)) :-
    N1 is N0+1,
    X = N0. % crude binding

% substitute type variables
copy_with_subs(tvar(X), Subs, T) :-
    ( member(X-T, Subs) -> true ; T = tvar(X) ).
copy_with_subs(arrow(A,B), Subs, arrow(A1,B1)) :-
    copy_with_subs(A, Subs, A1),
    copy_with_subs(B, Subs, B1).
copy_with_subs(pair(A,B), Subs, pair(A1,B1)) :-
    copy_with_subs(A, Subs, A1),
    copy_with_subs(B, Subs, B1).
copy_with_subs(unit, _, unit).

% generalize
generalize(Env,T,scheme(Vs,T)) :-
    ftv(T,Ft), ftv_env(Env,Fe), subtract(Ft,Fe,Vs).

% lookup in env
lookup(X,Env,N0,N1,T) :-
    member(X-Scheme,Env),
    instantiate(Scheme,N0,N1,T).

% unify
unify(tvar(X), T) :- var(T), T = tvar(X).
unify(T, tvar(X)) :- var(T), T = tvar(X).
unify(tvar(X), T) :- \+ occurs(X,T), T = tvar(X).
unify(T, tvar(X)) :- \+ occurs(X,T), T = tvar(X).
unify(arrow(A1,A2), arrow(B1,B2)) :- unify(A1,B1), unify(A2,B2).
unify(pair(A1,A2), pair(B1,B2))   :- unify(A1,B1), unify(A2,B2).
unify(unit, unit).
unify(T,T).

% occurs check
occurs(X,tvar(X)).
occurs(X,arrow(T1,T2)) :- occurs(X,T1) ; occurs(X,T2).
occurs(X,pair(T1,T2)) :- occurs(X,T1) ; occurs(X,T2).

% W algorithm
%
% w(+Env, +Expr, +N0, -N1, -Type)
%
w(_, var(X), N0, N0, _) :- throw(error(unbound_variable(X),_)).
w(Env, var(X), N0, N1, T) :-
    lookup(X,Env,N0,N1,T).

w(Env, lam(X,E), N0, N2, arrow(T1,T2)) :-
    fresh_typevar(N0,N1,T1),
    w([X-scheme([],T1)|Env], E, N1, N2, T2).

w(Env, app(E1,E2), N0, N3, T) :-
    w(Env,E1,N0,N1,T1),
    w(Env,E2,N1,N2,T2),
    fresh_typevar(N2,N3,T),
    unify(T1, arrow(T2,T)).

w(Env, let(X,E1,E2), N0, N2, T) :-
    w(Env,E1,N0,N1,T1),
    generalize(Env,T1,S),
    w([X-S|Env],E2,N1,N2,T).

w(Env, letrec(X,E1,E2), N0,N3,T) :-
    fresh_typevar(N0,N1,Tx),
    w([X-scheme([],Tx)|Env],E1,N1,N2,T1),
    unify(Tx,T1),
    generalize(Env,Tx,S),
    w([X-S|Env],E2,N2,N3,T).

w(Env, pair(E1,E2), N0,N2, pair(T1,T2)) :-
    w(Env,E1,N0,N1,T1),
    w(Env,E2,N1,N2,T2).

w(_, unit, N,N, unit).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Test suite for Hindley–Milner inference (w/5)
%% Requires: SWI-Prolog or any Prolog with plunit
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(hindley_milner).

test(identity) :-
    w([], lam(x,var(x)), 0, _, T),
    assertion(T = arrow(tvar(0), tvar(0))).

test(constant_function) :-
    w([], lam(x, lam(y, var(x))), 0, _, T),
    assertion(T = arrow(tvar(0), arrow(tvar(1), tvar(0)))).

test(application) :-
    w([], app(lam(x,var(x)), lam(y,var(y))), 0, _, T),
    assertion(T = arrow(tvar(2), tvar(2))).

test(unit) :-
    w([], unit, 0, _, T),
    assertion(T = unit).

test(pair) :-
    w([], pair(unit, lam(x,var(x))), 0, _, T),
    assertion(T = pair(unit, arrow(tvar(0), tvar(0)))).

test(let_id) :-
    w([], let(id, lam(x,var(x)), var(id)), 0, _, T),
    assertion(T = arrow(tvar(0), tvar(0))).

test(let_poly) :-
    w([], let(id, lam(x,var(x)),
               pair(app(var(id), unit),
                    app(var(id), lam(y,var(y))))),
        0, _, T),
    assertion(T = pair(unit, arrow(tvar(2), tvar(2)))).

test(letrec_id) :-
    w([], letrec(f, lam(x,var(x)), var(f)), 0, _, T),
    assertion(T = arrow(tvar(0), tvar(0))).

test(letrec_self_apply) :-
    w([], letrec(f, lam(x, app(var(f), var(x))), var(f)), 0, _, T),
    assertion(T = arrow(tvar(2), tvar(3))).

test(letrec_id_apply) :-
    w([], letrec(id, lam(x,var(x)), app(var(id), unit)), 0, _, T),
    assertion(T = unit).

:- end_tests(hindley_milner).
