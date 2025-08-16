% hindley_milner.pl
% A small Hindley–Milner type inference system in ISO Prolog.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Fresh variable generator
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

gensym(N0, N1, tvar(N0)) :-
    N1 is N0 + 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Type environments and lookup
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

lookup(X, [(X,T)|_], _, _, T).
lookup(X, [_|Env], N0, N1, T) :-
    lookup(X, Env, N0, N1, T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Type generalization and instantiation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

free_type_vars(tvar(X), [X]).
free_type_vars(arrow(T1,T2), Vs) :-
    free_type_vars(T1, V1s),
    free_type_vars(T2, V2s),
    append(V1s, V2s, Vs).
free_type_vars(pair(T1,T2), Vs) :-
    free_type_vars(T1, V1s),
    free_type_vars(T2, V2s),
    append(V1s, V2s, Vs).
free_type_vars(unit, []).
free_type_vars(T, []) :-
    atomic(T).

free_type_vars_scheme(all(Vs,T), Free) :-
    free_type_vars(T, TFs),
    subtract(TFs, Vs, Free).

instantiate(all(Vs,T), N0, N1, Tinst) :-
    instantiate_vars(Vs, N0, N1, Subst),
    subst_type(Subst, T, Tinst).
instantiate(T, N, N, T).

instantiate_vars([], N, N, []).
instantiate_vars([_|Vs], N0, N2, [(tvar(N0),tvar(N1))|Rest]) :-
    N1 = N0,
    Nmid is N0+1,
    instantiate_vars(Vs, Nmid, N2, Rest).

subst_type(_, tvar(X), tvar(X)).
subst_type(Subst, arrow(T1,T2), arrow(T1s,T2s)) :-
    subst_type(Subst, T1, T1s),
    subst_type(Subst, T2, T2s).
subst_type(Subst, pair(T1,T2), pair(T1s,T2s)) :-
    subst_type(Subst, T1, T1s),
    subst_type(Subst, T2, T2s).
subst_type(_, unit, unit).
subst_type(_, T, T) :- atomic(T).
subst_type(Subst, tvar(X), T) :-
    member((tvar(X),T), Subst).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Unification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unify(tvar(X), T) :-
    var_bind(X,T).
unify(T, tvar(X)) :-
    var_bind(X,T).
unify(arrow(T1,T2), arrow(S1,S2)) :-
    unify(T1,S1), unify(T2,S2).
unify(pair(T1,T2), pair(S1,S2)) :-
    unify(T1,S1), unify(T2,S2).
unify(unit, unit).
unify(T,T).

var_bind(X,T) :-
    ( T = tvar(X) -> true
    ; occurs_check(X,T) -> throw(error(occurs_check(X,T),_))
    ; true ).

occurs_check(X,tvar(Y)) :- X=Y.
occurs_check(X,arrow(T1,T2)) :-
    (occurs_check(X,T1); occurs_check(X,T2)).
occurs_check(X,pair(T1,T2)) :-
    (occurs_check(X,T1); occurs_check(X,T2)).
occurs_check(_,unit) :- fail.
occurs_check(_,T) :- atomic(T), fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Algorithm W
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% var
w(Env, var(X), N0, N1, T) :-
    lookup(X, Env, N0, N1, Scheme),
    instantiate(Scheme, N0, N1, T), !.

% w(_, var(X), N, N, _) :-
%    throw(error(unbound_variable(X),_)).

w(_, var(X), N, N, _) :-
    throw(error(unbound_variable(X), context(w/5, 'unbound variable'))).

% lambda
w(Env, lam(X,E), N0, N2, arrow(Tx,Te)) :-
    gensym(N0,N1,Tx),
    w([(X,Tx)|Env], E, N1, N2, Te).

% application
w(Env, app(E1,E2), N0, N3, T) :-
    w(Env,E1,N0,N1,T1),
    w(Env,E2,N1,N2,T2),
    gensym(N2,N3,Tr),
    unify(T1, arrow(T2,Tr)),
    T = Tr.

% let
w(Env, let(X,E1,E2), N0, N2, T) :-
    w(Env,E1,N0,N1,T1),
    free_type_vars(T1,TVs),
    Scheme = all(TVs,T1),
    w([(X,Scheme)|Env], E2, N1, N2, T).

% pair
w(Env, pair(E1,E2), N0, N2, pair(T1,T2)) :-
    w(Env,E1,N0,N1,T1),
    w(Env,E2,N1,N2,T2).

% unit
w(_, unit, N, N, unit).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Example Queries (manual tests)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/** <examples>

?- w([], lam(x, var(x)), 0, _, T).
% Expected: T = arrow(tvar(0), tvar(0)).

?- w([], app(lam(x, var(x)), unit), 0, _, T).
% Expected: T = unit.

?- w([], let(id, lam(x,var(x)), app(var(id), unit)), 0, _, T).
% Expected: T = unit.

?- w([], lam(x, lam(y, pair(var(x),var(y)))), 0, _, T).
% Expected: T = arrow(tvar(0), arrow(tvar(1), pair(tvar(0), tvar(1)))).

*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Robust Hindley–Milner PLUnit test suite
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- begin_tests(hindley_milner).

%% Identity function λx. x : α → α
test(identity) :-
    w([], lam(x,var(x)), 0, _, T),
    unify(T, arrow(tvar(_), tvar(_))),
    !.

%% Application (λx. x) (λy. y) : γ → γ
test(application) :-
    w([], app(lam(x,var(x)), lam(y,var(y))), 0, _, T),
    unify(T, arrow(tvar(_), tvar(_))),
    !.

%% Unit literal
test(unit) :-
    w([], unit, 0, _, T),
    T = unit,
    !.

%% Pair (unit, λx.x) : unit * (α → α)
test(pair) :-
    w([], pair(unit, lam(x,var(x))), 0, _, T),
    T = pair(unit, arrow(tvar(_), tvar(_))),
    !.

%% Let binding: let id = λx. x in id
test(let_id) :-
    w([], let(id, lam(x,var(x)), var(id)), 0, _, T),
    unify(T, arrow(tvar(_), tvar(_))),
    !.

%% Let binding with polymorphism: let id = λx. x in (id unit, id (λy.y))
test(let_poly) :-
    w([], let(id, lam(x,var(x)),
             pair(app(var(id), unit),
                  app(var(id), lam(y,var(y))))),
        0, _, T),
    T = pair(unit, arrow(tvar(_), tvar(_))),
    !.

%% Simple recursion: letrec f = λx. x in f
test(letrec_id) :-
    w([], letrec(f, lam(x,var(x)), var(f)), 0, _, T),
    unify(T, arrow(tvar(_), tvar(_))),
    !.

%% Recursive self-application: letrec f = λx. f x in f
test(letrec_self_apply) :-
    w([], letrec(f, lam(x, app(var(f), var(x))), var(f)), 0, _, T),
    T = arrow(tvar(_), tvar(_)),
    !.

%% Application of recursive identity: letrec id = λx. x in id unit
test(letrec_id_apply) :-
    w([], letrec(id, lam(x,var(x)), app(var(id), unit)), 0, _, T),
    T = unit,
    !.

:- end_tests(hindley_milner).
