% HM type inference in ISO Prolog

:- op(500, xfy, '->').   % infix arrow

% fresh_typevar(-T)
fresh_typevar(tvar(X)) :- gensym(t, X).

% free type vars in a type
ftv(tvar(X), [X]).
ftv(arrow(T1,T2), Vs) :- ftv(T1,V1), ftv(T2,V2), append(V1,V2,Vs0), sort(Vs0,Vs).
ftv(pair(T1,T2), Vs)  :- ftv(T1,V1), ftv(T2,V2), append(V1,V2,Vs0), sort(Vs0,Vs).
ftv(unit, []).

% free type vars in a scheme
ftv_scheme(scheme(Vs,T), Out) :-
    ftv(T,F), subtract(F,Vs,Out).

% free type vars in env
ftv_env([],[]).
ftv_env([_-Sch|E],Vs) :-
    ftv_scheme(Sch,V1), ftv_env(E,V2), append(V1,V2,V0), sort(V0,Vs).

% instantiate scheme to fresh type
instantiate(scheme(Vs,T), T1) :-
    copy_term(T-Vs, T1-_).

% generalize env and type into scheme
generalize(Env,T,scheme(Vs,T)) :-
    ftv(T,Ft), ftv_env(Env,Fe), subtract(Ft,Fe,Vs).

% lookup env
lookup(X,Env,T) :-
    member(X-Scheme,Env),
    instantiate(Scheme,T).

% unify types
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
w(_, var(X), T) :- throw(error(unbound_variable(X),_)), fail.
w(Env, var(X), T) :-
    lookup(X,Env,T).

w(Env, lam(X,E), arrow(T1,T2)) :-
    fresh_typevar(T1),
    w([X-scheme([],T1)|Env], E, T2).

w(Env, app(E1,E2), T) :-
    w(Env,E1,T1),
    w(Env,E2,T2),
    fresh_typevar(T),
    unify(T1, arrow(T2,T)).

w(Env, let(X,E1,E2), T) :-
    w(Env,E1,T1),
    generalize(Env,T1,S),
    w([X-S|Env],E2,T).

w(Env, letrec(X,E1,E2), T) :-
    fresh_typevar(Tx),
    w([X-scheme([],Tx)|Env],E1,T1),
    unify(Tx,T1),
    generalize(Env,Tx,S),
    w([X-S|Env],E2,T).

w(Env, pair(E1,E2), pair(T1,T2)) :-
    w(Env,E1,T1),
    w(Env,E2,T2).

w(_, unit, unit).
