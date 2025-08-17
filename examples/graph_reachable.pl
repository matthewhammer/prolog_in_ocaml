% reachability.pl
%
% Example of a natural recursive definition that diverges in vanilla Prolog
% but terminates with tabling.

% -------------------------------
% Graph definition (with a cycle)
% -------------------------------
edge(a,b).
edge(b,c).
edge(c,d).
edge(d,b).  % cycle back to b

% -------------------------------
% Reachability relation
% -------------------------------
reachable(X,Y) :- edge(X,Y).
reachable(X,Y) :- edge(X,Z), reachable(Z,Y).

% -------------------------------
% Example queries to try:
% -------------------------------
%
% ?- reachable(a, X).
%    % In vanilla Prolog, this will loop forever because of the cycle.
%
% If you enable tabling:
%
% ?- [reachability].
% ?- table reachable/2.
% ?- reachable(a, X).
%    % Now it terminates and returns:
%    % X = b ;
%    % X = c ;
%    % X = d.
%
% Another query:
% ?- reachable(b, X).
%    % With tabling, returns: X = c ; X = d ; X = b.

