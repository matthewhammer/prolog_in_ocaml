% triangles.pl
% Example: Tabled triangle detection with unique IDs using assertions

:- table triangle/3.
:- dynamic triangle_id/2.
:- dynamic triangle_name/2.

% -------------------------------
% Graph definition (with triangles)
% -------------------------------
edge(a,b).
edge(b,c).
edge(c,a).  % triangle 1

edge(a,d).
edge(d,e).
edge(e,a).  % triangle 2

edge(b,d).
edge(d,f).
edge(f,b).  % triangle 3

% -------------------------------
% Tabled triangle detection
% -------------------------------
triangle(X,Y,Z) :-
    edge(X,Y),
    edge(Y,Z),
    edge(Z,X),
    X @< Y, Y @< Z.  % canonical order to avoid duplicates

% -------------------------------
% Simple gensym mechanism
% -------------------------------
init_gensym :-
    retractall(triangle_id(_, _)),
    retractall(triangle_name(_, _)),
    assert(triangle_id(next, 1)).

gensym(Triangle, Id) :-
    retract(triangle_id(next, N)),
    Id = N,
    assert(triangle_id(next, N+1)),
    assert(triangle_name(Triangle, Id)).

% -------------------------------
% Enumerate and name all triangles
% -------------------------------
name_triangles :-
    init_gensym,
    triangle(X,Y,Z),
    gensym(triangle(X,Y,Z), Id),
    write('Triangle '), write(Id), write(': '), writeln([X,Y,Z]),
    fail.
name_triangles.

% -------------------------------
% Example queries to try:
% -------------------------------
% ?- [triangles].
% ?- name_triangles.
% ?- triangle_name(Triangle, Id).
