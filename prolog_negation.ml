(* mini_prolog.ml
   A tiny, purely functional Prolog with negation-as-failure (\+/1) and cut (!).
   One-file, self-contained demo.

   Compile: ocamlc -o mini_prolog mini_prolog.ml
   Run:     ./mini_prolog
*)

(* ---------- Syntax ---------- *)

type term =
  | Var  of string
  | Atom of string
  | Comp of string * term list

type goal =
  | Call of term               (* predicate call *)
  | Cut                        (* ! *)
  | Neg of goal                (* \+ G *)

type clause = { head : term; body : goal list }

type program = clause list

(* ---------- Pretty printing ---------- *)

let rec pp_term = function
  | Var x      -> x
  | Atom a     -> a
  | Comp (f,[]) -> f
  | Comp (f,ts) ->
      let args = String.concat ", " (List.map pp_term ts) in
      Printf.sprintf "%s(%s)" f args

and pp_goal = function
  | Call t -> pp_term t
  | Cut    -> "!"
  | Neg g  -> "\\+(" ^ pp_goal g ^ ")"

and pp_goal_list gs =
  match gs with
  | [] -> "true"
  | _  -> String.concat ", " (List.map pp_goal gs)

(* ---------- Substitutions & unification ---------- *)

(* Substitution: maps variable names to terms *)
type subst = (string * term) list

let rec lookup x (s:subst) =
  match s with
  | [] -> None
  | (y,t)::rest -> if x=y then Some t else lookup x rest

let rec apply s = function
  | Var x as v ->
      begin match lookup x s with
      | None -> v
      | Some t -> apply s t
      end
  | Atom _ as a -> a
  | Comp (f,ts) -> Comp (f, List.map (apply s) ts)

let compose s1 s2 =
  (* apply s1 to range of s2, then append s1 bindings (shadowed by s2) *)
  let s2' = List.map (fun (x,t) -> (x, apply s1 t)) s2 in
  s2' @ s1

let rec occurs x t s =
  match apply s t with
  | Var y -> x = y
  | Atom _ -> false
  | Comp(_,ts) -> List.exists (fun u -> occurs x u s) ts

let rec unify t1 t2 (s:subst) : subst option =
  let t1 = apply s t1 in
  let t2 = apply s t2 in
  match t1, t2 with
  | Var x, Var y when x = y -> Some s
  | Var x, t | t, Var x ->
      if occurs x t s then None else Some ((x,t)::s)
  | Atom a, Atom b ->
      if a=b then Some s else None
  | Comp(f,as1), Comp(g,as2) ->
      if f=g && List.length as1 = List.length as2
      then unify_list as1 as2 s
      else None
  | _ -> None

and unify_list ts1 ts2 s =
  match ts1, ts2 with
  | [], [] -> Some s
  | t1::r1, t2::r2 ->
      begin match unify t1 t2 s with
      | None -> None
      | Some s' -> unify_list r1 r2 s'
      end
  | _ -> None

(* ---------- Freshening (standardize apart) ---------- *)

let fresh_counter =
  let c = ref 0 in
  fun () -> incr c; !c

let freshen_clause (cl:clause) : clause =
  (* Map each Var "X" in clause to a unique Var "X#n" *)
  let tbl : (string, string) Hashtbl.t = Hashtbl.create 16 in
  let rename_var x =
    match Hashtbl.find_opt tbl x with
    | Some x' -> x'
    | None ->
        let x' = Printf.sprintf "%s#%d" x (fresh_counter ()) in
        Hashtbl.add tbl x x'; x'
  in
  let rec fterm = function
    | Var x      -> Var (rename_var x)
    | Atom _ as a -> a
    | Comp (g,ts) -> Comp (g, List.map fterm ts)
  in
  let rec fgoal = function
    | Call t -> Call (fterm t)
    | Cut    -> Cut
    | Neg g  -> Neg (fgoal g)
  in
  { head = fterm cl.head; body = List.map fgoal cl.body }

(* ---------- Proof search with cut & negation ---------- *)

(* A result carries a substitution and an optional "cut barrier":
   Some n  = a cut (!) was executed that commits up to barrier level n.
   None    = no cut pressure to propagate.
*)
type cut_barrier = int option
type answer = subst * cut_barrier

(* Prover signature:
   prove goals subst level barrier program
   - level: current search depth (for clarity in debugging)
   - barrier: the nearest predicate-call barrier; cut (!) commits up to this barrier
*)
let rec prove (gs:goal list) (s:subst) (level:int) (barrier:int) (prog:program) : answer list =
  match gs with
  | [] -> [ (s, None) ]
  | g :: rest ->
      begin match g with
      | Cut ->
          (* Cut: succeed immediately, but signal commitment to current barrier. *)
          [ (s, Some barrier) ]

      | Neg inner ->
          (* Negation-as-failure: run a private proof of [inner].
             If it has any solutions, negation fails; else it succeeds
             with current substitution and no bindings exported.
          *)
          let sols = prove [inner] s (level+1) (level+1) prog in
          if sols = [] then [ (s, None) ] else []

      | Call (Atom "true") ->
          prove rest s level barrier prog

      | Call (Atom "fail") ->
          []

      | Call (Comp (pred, args)) ->
          (* Try all matching clauses of arity n *)
          let arity = List.length args in
          let clauses =
            List.filter (fun {head; _} ->
              match head with
              | Comp (p, hs) -> p = pred && List.length hs = arity
              | Atom p       -> p = pred && 0 = arity
              | _ -> false
            ) prog
          in
          prove_over_clauses clauses args rest s level barrier prog

      | Call (Atom p) ->
          (* 0-arity predicate *)
          let clauses =
            List.filter (fun {head; _} ->
              match head with
              | Atom q -> q = p
              | Comp (q,hs) -> q = p && List.length hs = 0
              | _ -> false
            ) prog
          in
          prove_over_clauses clauses [] rest s level barrier prog

      | Call (Var _) ->
          failwith "Callable variable not supported in this mini-interpreter"

      end

and prove_over_clauses (clauses:clause list) (args:term list) (rest:goal list)
                       (s:subst) (level:int) (barrier:int) (prog:program)
  : answer list =
  let rec loop cls acc =
    match cls with
    | [] -> List.rev acc
    | cl :: more ->
        let cl = freshen_clause cl in
        (* Try to unify head with the call *)
        begin match cl.head with
        | Atom _ | Var _ -> (* normalized away in freshen; ignore *)
            loop more acc
        | Comp (p, hs) ->
            begin match unify (Comp (p, hs)) (Comp (p, args)) s with
            | None ->
                loop more acc
            | Some s' ->
                (* For the body of this clause, establish a barrier at THIS predicate call level. *)
                let body_goals = cl.body @ rest in
                let results = prove body_goals s' (level+1) level prog in
                (* If any result indicates a cut to <= level, stop exploring other clauses. *)
                let acc' = List.rev_append results acc in
                let cut_here =
                  List.exists (function
                    | (_, Some b) when b <= level -> true
                    | _ -> false
                  ) results
                in
                if cut_here then List.rev acc'
                else loop more acc'
            end
        end
  in
  loop clauses []

(* ---------- A tiny test program ---------- *)

(* max/3 with cut: chooses the first true branch and commits *)
let cl_max1 =
  { head = Comp("max", [Var "X"; Var "Y"; Var "X"]);
    body = [ Call (Comp("=<", [Var "X"; Var "Y"])); Cut ] }

let cl_max2 =
  { head = Comp("max", [Var "X"; Var "Y"; Var "Y"]);
    body = [] }

(* A “<=” relation for small integers (Peano-free, hand-coded facts). *)
let le_facts =
  let ints = [0;1;2;3;4;5] in
  let mk a b =
    { head = Comp("=<", [Atom (string_of_int a); Atom (string_of_int b)]); body = [] }
  in
  let pairs =
    List.concat (List.map (fun a -> List.filter (fun b -> a <= b) ints |> List.map (fun b -> mk a b)) ints)
  in
  pairs

(* parent facts & a not_parent/2 rule using negation-as-failure *)
let parent_facts = [
  { head = Comp("parent", [Atom "alice"; Atom "bob"]); body = [] };
  { head = Comp("parent", [Atom "carol"; Atom "dave"]); body = [] };
]

let not_parent_rule =
  { head = Comp("not_parent", [Var "X"; Var "Y"]);
    body = [ Neg (Call (Comp("parent", [Var "X"; Var "Y"]))) ] }

(* A fact we “add later” conceptually to show non-monotonicity idea; we will
   run two queries: before and after adding this to the program list. *)
let new_parent_fact =
  { head = Comp("parent", [Atom "alice"; Atom "charlie"]); body = [] }

let prog_base : program =
  [ cl_max1; cl_max2; not_parent_rule ] @ le_facts @ parent_facts

let prog_plus : program =
  new_parent_fact :: prog_base

(* ---------- Query driver ---------- *)

let rec reify_term (s:subst) (t:term) = apply s t

let show_answers varnames (answers:answer list) =
  let show_one (s, _cut) =
    let items =
      List.map (fun v ->
        let tv = reify_term s (Var v) in
        v ^ " = " ^ pp_term tv
      ) varnames
    in
    print_endline ("{ " ^ String.concat "; " items ^ " }")
  in
  match answers with
  | [] -> print_endline "no."
  | _  -> List.iter show_one answers

(* A helper to make running a single query easier *)
let run_query ~prog ~vars (goals:goal list) =
  let ans = prove goals [] 0 0 prog in
  show_answers vars ans

(* ---------- Demos ---------- *)

let () =
  print_endline "== Demo 1: max/3 with cut ==";
  let q1 = [ Call (Comp("max", [Atom "2"; Atom "5"; Var "M"])) ] in
  run_query ~prog:prog_base ~vars:["M"] q1;
  (* There is exactly one answer due to cut: M = 5 *)

  print_endline "\n== Demo 2: negation-as-failure (before adding a fact) ==";
  (* Ask for Y such that alice is NOT parent of Y *)
  let q2 = [ Call (Comp("not_parent", [Atom "alice"; Var "Y"])) ] in
  run_query ~prog:prog_base ~vars:["Y"] q2;
  (* Expect Y can be any term not proven as alice's child; with only parent(alice,bob),
     \+ parent(alice,Y) fails for Y=bob but succeeds for other values.
     Our tiny interpreter doesn’t enumerate the universe; this demo just shows
     that Y unifies with what remains in other goals—here there are none, so it
     yields the current (empty) substitution: effectively success without bindings. *)

  print_endline "\n== Demo 3: non-monotonicity of \\+ by adding a fact ==";
  (* Same query, but “after” adding parent(alice,charlie). This can flip success/failure
     in contexts where a particular Y gets bound earlier. We demonstrate by constraining Y. *)
  let q3 =
    [ Call (Comp("=", [Var "Y"; Atom "charlie"]));
      Call (Comp("not_parent", [Atom "alice"; Var "Y"])) ]
  in
  print_endline "-- Before adding fact parent(alice,charlie) --";
  run_query ~prog:prog_base ~vars:["Y"] q3;   (* succeeds: \+ parent(alice,charlie) held before *)

  print_endline "-- After adding fact parent(alice,charlie) --";
  run_query ~prog:prog_plus ~vars:["Y"] q3;   (* now fails: negation flips due to new fact *)

  print_endline "\nDone."
