:- module(ssa, [
    ssa_convert/2,
    run_example/0,
    example_cfg/1
]).

/** <module> SSA conversion for a tiny imperative CFG in SWI-Prolog

Representation:

  cfg(Blocks, Edges, Entry)

  Blocks = [ block(Id, Stmts) ... ]
  Edges  = [ edge(From, To) ... ]
  Entry  = Id (entry block)

  Stmts  = list of:
           - assign(Var, Expr)
           - goto(Label)
           - cbranch(Expr, TrueLabel, FalseLabel)

  Expr   = const(C) | var(V) | bin(Op, Expr, Expr)

After SSA:

  Blocks' = [ ssa_block(Id, Phis, Stmts') ... ]

  Phis   = [ phi(Var, ResName, Args) ... ]
           where ResName is var(Var, N)
                 Args = [arg(PredBlockId, var(Var, Npred)), ...]
  Stmts' = like Stmts, but:
           - assign(var(Var,N), Expr')
           - Expr' has variables rewritten to var(Var,N)

Notes:
  - Variables are atoms (e.g., x, y).
  - We assume each basic block ends with an explicit terminator (goto or cbranch)
    or falls through; edges list is the source of truth for CFG topology.
*/

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(library(ordsets)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Public API
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ssa_convert(cfg(Blocks, Edges, Entry), cfg(SSA_Blocks, Edges, Entry)) :-
    blocks_ids(Blocks, Nodes),
    preds_map(Nodes, Edges, Preds),
    succs_map(Nodes, Edges, Succs),
    dominators(Nodes, Entry, Preds, DomMap),
    idoms_from_doms(Nodes, Entry, DomMap, IDom),
    dom_tree(Nodes, IDom, DomChildren),
    dominance_frontiers(Nodes, Succs, DomChildren, IDom, DFMap),
    % collect definitions per variable
    defs_per_var(Blocks, DefSitesMap),
    % insert φ nodes via iterated DF
    insert_phis(Nodes, DFMap, DefSitesMap, PhiMap0),
    % rename along dominator tree, producing SSA blocks
    rename_program(Blocks, Entry, DomChildren, Succs, PhiMap0, SSA_Blocks).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Example + runner
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

example_cfg(cfg(
  [ block(entry, [
        assign(x, const(0)),
        cbranch(var(c), then1, else1)
    ]),
    block(then1, [
        assign(x, const(1)),
        goto(join)
    ]),
    block(else1, [
        assign(y, const(5)),
        goto(join)
    ]),
    block(join, [
        assign(z, bin(+, var(x), const(1)))
    ])
  ],
  [ edge(entry, then1),
    edge(entry, else1),
    edge(then1, join),
    edge(else1, join)
  ],
  entry)).

run_example :-
    example_cfg(CFG),
    ssa_convert(CFG, SSA),
    format('~n=== SSA Blocks ===~n', []),
    SSA = cfg(Blocks, _, Entry),
    format('Entry: ~w~n', [Entry]),
    forall(member(ssa_block(BId, Phis, Stmts), Blocks), (
        format('~nBlock ~w~n', [BId]),
        (Phis = [] -> true ; format('  Phis:~n', [])),
        forall(member(phi(V, Res, Args), Phis), (
            format('    ~w := phi(', [Res]),
            print_phi_args(Args),
            format(')  ; var=~w~n', [V])
        )),
        format('  Stmts:~n', []),
        forall(member(S, Stmts), (format('    '), print_stmt(S), nl))
    )).

print_phi_args([]).
print_phi_args([arg(P, Val)]) :- format('[~w: ~w]', [P, Val]).
print_phi_args([arg(P, Val)|Rest]) :-
    format('[~w: ~w], ', [P, Val]), print_phi_args(Rest).

print_stmt(assign(LHS, RHS)) :- format('~w := ', [LHS]), print_expr(RHS).
print_stmt(goto(L))          :- format('goto ~w', [L]).
print_stmt(cbranch(E, T, F)) :- print_expr(E), format(' ? ~w : ~w', [T, F]).

print_expr(const(C))    :- format('~w', [C]).
print_expr(var(V))      :- format('~w', [V]).
print_expr(var(V,N))    :- format('~w_%w', [V,N]).
print_expr(bin(Op,A,B)) :- format('('), print_expr(A), format(' ~w ', [Op]), print_expr(B), format(')').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CFG utilities
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

blocks_ids(Blocks, Nodes) :- findall(Id, member(block(Id,_), Blocks), Nodes).

preds_map(Nodes, Edges, Preds) :-
    maplist({Edges}/[N,N-Ps]>>findall(P, member(edge(P,N),Edges), Ps), Nodes, Pairs),
    dict_pairs(Preds, preds, Pairs).

succs_map(Nodes, Edges, Succs) :-
    maplist({Edges}/[N,N-Ss]>>findall(S, member(edge(N,S),Edges), Ss), Nodes, Pairs),
    dict_pairs(Succs, succs, Pairs).

block_by_id(Blocks, Id, Stmts) :- member(block(Id, Stmts), Blocks).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Dominators and Dom Tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dominators(Nodes, Entry, Preds, DomMap) :-
    sort(Nodes, Sorted),
    (   select(Entry, Sorted, Others)
    ->  true
    ;   throw(error(entry_not_in_nodes(Entry),_))
    ),
    % init: Dom[Entry]={Entry}; Dom[n]=AllNodes for n≠Entry
    list_to_ord_set(Sorted, All),
    EntrySet = [Entry],
    init_doms(Others, All, Inits),
    dict_pairs(Dom0, dom, [Entry-EntrySet|Inits]),
    iterate_doms(Sorted, Entry, Preds, Dom0, DomMap).

init_doms([], _, []).
init_doms([N|Ns], All, [N-All|Rest]) :- init_doms(Ns, All, Rest).

iterate_doms(Nodes, Entry, Preds, DomIn, DomOut) :-
    (   update_once(Nodes, Entry, Preds, DomIn, Dom1, Changed),
        Changed == true
    ->  iterate_doms(Nodes, Entry, Preds, Dom1, DomOut)
    ;   DomOut = DomIn
    ).

update_once([], _, _, Dom, Dom, false).
update_once([N|Ns], Entry, Preds, DomIn, DomOut, Changed) :-
    update_once(Ns, Entry, Preds, DomIn, DomMid, ChangedTail),
    ( N == Entry ->
        DomOut = DomMid, Changed = ChangedTail
    ;   Preds = preds(PMap),
        (   member(N-PredsN, PMap) -> true ; PredsN = [] ),
        (   PredsN = [] ->
            % unreachable: by convention, Dom[N] stays as is
            get_dict(N, DomMid, Cur), DomOut = DomMid, Changed = ChangedTail, _=Cur
        ;   % Dom[N] = {N} ∪ ⋂ Dom[p]
            findall(Dp, (member(P, PredsN), get_dict(P, DomMid, Dp)), DomsPs),
            intersect_all(DomsPs, Inter),
            ord_add_element(Inter, N, NewDom),
            get_dict(N, DomMid, CurDom),
            (   CurDom = NewDom
            ->  DomOut = DomMid, Changed = ChangedTail
            ;   DomOut = DomMid.put(N, NewDom), Changed = true
            )
        )
    ).

intersect_all([S|Rest], Out) :- intersect_all_(Rest, S, Out).
intersect_all_([], Acc, Acc).
intersect_all_([S|Ss], Acc, Out) :- ord_intersection(Acc, S, I), intersect_all_(Ss, I, Out).

% Immediate dominators from full dom sets
idoms_from_doms(Nodes, Entry, DomMap, IDom) :-
    findall(N-ID, (
        member(N, Nodes),
        ( N == Entry ->
            ID = none
        ;   get_dict(N, DomMap, Doms),
            ord_del_element(Doms, N, Strict),              % strict dominators
            % idom(N) is the D in Strict s.t. no other X in Strict dominates D
            % i.e., D is maximal in Strict by ⊂
            pick_idom(Strict, DomMap, ID)
        )
    ), Pairs),
    dict_pairs(IDom, idom, Pairs).

pick_idom(Strict, _DomMap, none) :- Strict == [], !.
pick_idom(Strict, DomMap, ID) :-
    % choose D in Strict with no other X in Strict where D ∈ Dom[X]
    member(D, Strict),
    \+ ( member(X, Strict), X \= D, get_dict(X, DomMap, DomX), ord_memberchk(D, DomX) ),
    !, ID = D.

dom_tree(Nodes, IDom, DomChildren) :-
    findall(N-Children, (
        member(N, Nodes),
        findall(C, (get_dict(C, IDom, N)), Children)
    ), Pairs),
    dict_pairs(DomChildren, dom_children, Pairs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Dominance Frontiers
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dominance_frontiers(Nodes, Succs, DomChildren, IDom, DFMap) :-
    % Cooper, Harvey, Kennedy algorithm (tree-based)
    findall(N-DF, (
        member(N, Nodes),
        local_df(N, Succs, IDom, Local),
        children_df(N, DomChildren, IDom, ChildDF),
        ord_union(Local, ChildDF, DF)
    ), Pairs),
    dict_pairs(DFMap, df, Pairs).

local_df(N, Succs, IDom, DF) :-
    succs_of(N, Succs, Ss),
    findall(S, ( member(S, Ss), get_dict(S, IDom, ID), ID \= N ), Raw),
    sort(Raw, DF).

children_df(N, DomChildren, IDom, DF) :-
    children_of(N, DomChildren, Cs),
    findall(Y, (
        member(C, Cs),
        children_df(C, DomChildren, IDom, DFc),
        member(Y, DFc),
        get_dict(Y, IDom, ID), ID \= N
    ), Ys),
    sort(Ys, DF).

succs_of(N, succs(Map), Ss) :- (member(N-Ss, Map) -> true ; Ss = []).
children_of(N, dom_children(Map), Cs) :- (member(N-Cs, Map) -> true ; Cs = []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Definition sites per var
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

defs_per_var(Blocks, DefSitesMap) :-
    findall(Var-BlockId, (
        member(block(BlockId, Stmts), Blocks),
        member(assign(Var, _Expr), Stmts)
    ), Pairs),
    group_pairs_by_key(Pairs, Grouped),
    dict_pairs(DefSitesMap, defs, Grouped).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Insert φ nodes (iterated DF)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

insert_phis(Nodes, DFMap, DefSitesMap, PhiMap) :-
    % PhiMap: for each block, a list of phi(Var, pending) initially empty
    empty_phi_map(Nodes, Empty),
    dict_pairs(DefSitesMap, _, VarDefsPairs),
    foldl(insert_var_phis(DFMap), VarDefsPairs, Empty, PhiMap).

empty_phi_map(Nodes, PhiMap) :-
    findall(N-[], member(N, Nodes), Pairs),
    dict_pairs(PhiMap, phis, Pairs).

insert_var_phis(DFMap, Var-DefSites, PhiIn, PhiOut) :-
    % Cytron worklist algorithm
    sort(DefSites, Defs),
    work_phi_var(Var, DFMap, Defs, Defs, PhiIn, PhiOut).

work_phi_var(_Var, _DFMap, _OrigDefs, [], Phi, Phi).
work_phi_var(Var, DFMap, OrigDefs, [X|WL], PhiIn, PhiOut) :-
    get_dict(X, DFMap, DFx),
    foldl(place_phi_at(Var, OrigDefs), DFx, state(PhiIn, WL), state(PhiMid, WL2)),
    work_phi_var(Var, DFMap, OrigDefs, WL2, PhiMid, PhiOut).

place_phi_at(Var, OrigDefs, Y, state(PhiIn, WL), state(PhiOut, WL2)) :-
    get_dict(Y, PhiIn, PhisY),
    (   memberchk(phi(Var, pending, pending), PhisY)
    ->  % already placed
        PhiOut = PhiIn, WL2 = WL
    ;   % place phi at Y
        PhisY2 = [phi(Var, pending, pending)|PhisY],
        PhiTmp = PhiIn.put(Y, PhisY2),
        (   memberchk(Y, OrigDefs)
        ->  WL2 = WL       % Y already a def site; no new defs added to WL
        ;   WL2 = [Y|WL]
        ),
        PhiOut = PhiTmp
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Renaming
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rename_program(Blocks, Entry, DomChildren, Succs, PhiMap0, SSA_Blocks) :-
    % Build maps for quick access
    blocks_ids(Blocks, Nodes),
    % initialize stacks and counters as empty dicts per var
    empty_assoc(VStacks0),
    empty_assoc(VCounters0),
    % Seed: finalize phi result names during traversal; φ args later per edge.
    % Turn Block facts into map for fast lookup
    list_to_blockmap(Blocks, BMap),
    % DFS rename
    rename_dfs(Entry, BMap, DomChildren, Succs, PhiMap0, VStacks0, VCounters0, [], OutBlocksPairs),
    % Complete φ args now filled; convert pairs to list
    pairs_values(OutBlocksPairs, SSA_BlocksUnsorted),
    % Keep original block order if possible
    reorder_blocks(Blocks, SSA_BlocksUnsorted, SSA_Blocks).

list_to_blockmap(Blocks, Map) :-
    findall(Id-Stmts, member(block(Id, Stmts), Blocks), Pairs),
    dict_pairs(Map, blocks, Pairs).

reorder_blocks(OrigBlocks, SSA_Unsorted, SSA_Sorted) :-
    findall(Id, member(block(Id,_), OrigBlocks), Order),
    % build map
    findall(Id-ssa_block(Id, Phis, Stmts),
        member(ssa_block(Id, Phis, Stmts), SSA_Unsorted),
        Pairs),
    dict_pairs(M, _, Pairs),
    findall(ssa_block(Id, Phis, Stmts),
        (member(Id, Order), get_dict(Id, M, ssa_block(Id, Phis, Stmts))),
        SSA_Sorted).

% rename_dfs(Node, ...)
% AccEdgesPhis carries pending φ-argument wiring per successor, but we do it eagerly:
% when leaving a block, we push arguments into each successor's φ based on current stack.
rename_dfs(N, BMap, DomChildren, Succs, PhiMapIn, VStacksIn, VCountersIn, Visited,
           [N-ssa_block(N, PhisOut, StmtsOut) | BlocksOutTail]) :-
    \+ memberchk(N, Visited), !,
    get_dict(N, BMap, Stmts0),
    get_dict(N, PhiMapIn, PhisPending0),
    % 1) Assign result names for each φ in this block (push on stacks)
    assign_phi_results(PhisPending0, VStacksIn, VCountersIn,
                       PhisWithRes, VStacks1, VCounters1),
    % 2) Rename statements in this block
    rename_stmts(Stmts0, VStacks1, VCounters1, Stmts1, VStacks2, VCounters2, DefPops),
    % 3) For each successor, wire φ-arguments using current top-of-stack
    wire_phi_args(N, Succs, PhiMapIn, PhisWithRes, VStacks2, PhiMap1),
    % 4) Recurse to children in dom-tree
    children_of(N, DomChildren, Kids),
    foldl(rename_dfs_kid(BMap, DomChildren, Succs), Kids,
          state(PhiMap1, VStacks2, VCounters2, [N|Visited], []),
          state(PhiMapOut, VStacksAfterKids, VCountersAfterKids, _Visited2, ChildBlocks)),
    % 5) Pop definitions introduced in this block (including φ results)
    pop_defs(DefPops, VStacksAfterKids, VStacks3),
    phi_res_pops(PhisWithRes, VStacks3, VStacksOut),
    % Finalize this block
    PhisOut = PhisWithRes,
    StmtsOut = Stmts1,
    BlocksOutTail = ChildBlocks.

rename_dfs(N, _BMap, _DomChildren, _Succs, _PhiMapIn, _VS, _VC, Visited, BlocksOut) :-
    % already visited (shouldn't happen in dom-tree DFS), skip
    memberchk(N, Visited),
    BlocksOut = [].

rename_dfs_kid(BMap, DomChildren, Succs, Kid,
               state(PhiMapIn, VS, VC, VisitedIn, BlocksAcc),
               state(PhiMapOut, VSOut, VCOut, VisitedOut, BlocksOut)) :-
    rename_dfs(Kid, BMap, DomChildren, Succs, PhiMapIn, VS, VC, VisitedIn, KidBlocks),
    % KidBlocks = [Kid-ssa_block(...) | ...] but we return as a list to concat
    % Convert to same accumulator form
    KidBlocks = [Kid-_|_],
    append(BlocksAcc, KidBlocks, BlocksOut),
    PhiMapOut = PhiMapIn, VSOut = VS, VCOut = VC, VisitedOut = [Kid|VisitedIn].

assign_phi_results([], VStacks, VCounters, [], VStacks, VCounters).
assign_phi_results([phi(Var, pending, pending)|Rest], VStacksIn, VCountersIn,
                   [phi(Var, var(Var, N), PendingArgs)|OutRest],
                   VStacksOut, VCountersOut) :-
    bump_counter(Var, VCountersIn, VC1, N),
    push_stack(Var, N, VStacksIn, VS1),
    PendingArgs = [], % args to be filled later
    assign_phi_results(Rest, VS1, VC1, OutRest, VStacksOut, VCountersOut).

% Rename statements: returns DefPops = [Var-CountToPop] introduced in this block
rename_stmts([], VS, VC, [], VS, VC, []).
rename_stmts([S|Ss], VS0, VC0, [S1|Ss1], VS2, VC2, PopsOut) :-
    rename_stmt(S, VS0, VC0, S1, VS1, VC1, Pops1),
    rename_stmts(Ss, VS1, VC1, Ss1, VS2, VC2, Pops2),
    append(Pops1, Pops2, PopsOut).

rename_stmt(assign(Var, Expr), VS0, VC0,
            assign(var(Var,N), Expr1), VS1, VC1, [Var-1]) :-
    rename_expr_reads(Expr, VS0, Expr1),
    bump_counter(Var, VC0, VCtemp, N),
    push_stack(Var, N, VS0, VS1),
    VC1 = VCtemp.
rename_stmt(goto(L), VS, VC, goto(L), VS, VC, []).
rename_stmt(cbranch(E, T, F), VS, VC, cbranch(E1, T, F), VS, VC, []) :-
    rename_expr_reads(E, VS, E1).

rename_expr_reads(const(C), _, const(C)).
rename_expr_reads(var(V), VS, var(V,N)) :-
    top_stack_default_zero(V, VS, N).
rename_expr_reads(bin(Op, A, B), VS, bin(Op, A1, B1)) :-
    rename_expr_reads(A, VS, A1),
    rename_expr_reads(B, VS, B1).

wire_phi_args(N, Succs, PhiMapIn, PhisHere, VStacks, PhiMapOut) :-
    succs_of(N, Succs, SuccsN),
    foldl(wire_one_succ(N, PhisHere, VStacks), SuccsN, PhiMapIn, PhiMapOut).

wire_one_succ(Pred, PhisHere, VStacks, Succ, PhiMapIn, PhiMapOut) :-
    get_dict(Succ, PhiMapIn, PhisSucc0),
    % For each phi in the successor, add arg(Pred, current version of Var)
    maplist(add_phi_arg(Pred, VStacks), PhisSucc0, PhisSucc1),
    PhiMapOut = PhiMapIn.put(Succ, PhisSucc1).

add_phi_arg(Pred, VStacks, phi(Var, Res, Args0), phi(Var, Res, Args1)) :-
    top_stack_default_zero(Var, VStacks, Npred),
    append(Args0, [arg(Pred, var(Var, Npred))], Args1).

% Pops for normal definitions (assign)
pop_defs([], VS, VS).
pop_defs([Var-K|Rest], VS0, VSOut) :-
    pop_n(Var, K, VS0, VS1),
    pop_defs(Rest, VS1, VSOut).

% Pops for φ result names (one per phi)
phi_res_pops([], VS, VS).
phi_res_pops([phi(Var, _Res, _Args)|Rest], VS0, VSOut) :-
    pop_n(Var, 1, VS0, VS1),
    phi_res_pops(Rest, VS1, VSOut).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Var stacks & counters
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bump_counter(Var, VC0, VC, N) :-
    ( get_assoc(Var, VC0, Cur) -> N is Cur + 1, put_assoc(Var, VC0, N, VC)
    ; N = 0, put_assoc(Var, VC0, 0, VC)
    ).

push_stack(Var, N, VS0, VS) :-
    ( get_assoc(Var, VS0, Stack) -> put_assoc(Var, VS0, [N|Stack], VS)
    ; put_assoc(Var, VS0, [N], VS)
    ).

top_stack_default_zero(Var, VS, N) :-
    ( get_assoc(Var, VS, [Top|_]) -> N = Top
    ; N = 0
    ).

pop_n(_Var, 0, VS, VS).
pop_n(Var, K, VS0, VS) :-
    K > 0,
    ( get_assoc(Var, VS0, [ _ | Rest]) ->
        put_assoc(Var, VS0, Rest, VS1)
    ;   % popping from empty: keep empty
        VS1 = VS0
    ),
    K1 is K - 1,
    pop_n(Var, K1, VS1, VS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Dict helpers
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dict_pairs(Dict, Tag, Pairs) :- is_dict(Dict) -> dict_pairs(Dict, Tag, Pairs) ; dict_create(Dict, Tag, Pairs).

pairs_values([], []).
pairs_values([_-V|Ps], [V|Vs]) :- pairs_values(Ps, Vs).
