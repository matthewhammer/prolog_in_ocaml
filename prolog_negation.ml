(* mini_prolog.ml
   A tiny, purely functional Prolog core with negation-as-failure (\+/1) and cut (!/0).
   Includes minimal builtins (= /2, =</2, true/0, fail/0), freshening, and tests.

   Build: ocamlc -o mini_prolog mini_prolog.ml
   Run:   ./mini_prolog
*)

(* ---------- Syntax ---------- *)

type term =
  | Var  of string
  | Atom of string
  | Comp of string * term list

type goal =
  | Call of term            (* predicate call *)
  | Cut                     (* ! *)
  | Neg of goal             (* \+ G *)

type clause = { head : term; body : goal list }
type program = clause list

(* ---------- Pretty printing ---------- *)

let rec pp_term = function
  | Var x       -> x
  | Atom a      -> a
  | Comp (f,[]) -> f
  | Comp (f,ts) ->
      let args = String.concat ", " (List.map pp_term ts) in
      Printf.sprintf "%s(%s)" f args

and pp_goal = function
  | Call t -> pp_term t
  | Cut    -> "!"
  | Neg g  -> "\\+(" ^ pp_goal g ^ ")"

(* ---------- Substitutions & unification ---------- *)

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

(* ---------- Cut signalling ---------- *)

type cut_sig = NoCut | CutTo of int

let cut_frame_counter =
  let c = ref 0 in
  fun () -> incr c; !c

(* ---------- Builtins ---------- *)

let is_int_string s =
  try ignore (int_of_string s); true with _ -> false

let eval_int s t =
  match apply s t with
  | Atom a when is_int_string a -> Some (int_of_string a)
  | _ -> None

(* ---------- Solver ---------- *)

(* Core solver: DFS with proper cut semantics.
   - 'frame' is the current predicate-call frame id (0 at top-level).
*)
let rec solve (prog:program) (goals:goal list) (s:subst) (frame:int) : (subst * cut_sig) list =
  match goals with
  | [] -> [ (s, NoCut) ]
  | g :: gs ->
      let sols_first = solve_one prog g s frame in
      (* Conjunctive sequencing with cut-awareness:
         If any combined answer carries CutTo c where c <= frame,
         we STOP exploring further alternatives for this goal at this frame. *)
      let rec loop sols acc =
        match sols with
        | [] -> List.rev acc
        | (s1, c1) :: more ->
            let rest = solve prog gs s1 frame in
            (* Propagate earlier cut if rest has none *)
            let combined =
              List.map (fun (s2, c2) ->
                match c2 with
                | NoCut -> (s2, c1)
                | _ -> (s2, c2)
              ) rest
            in
            let acc' = List.rev_append combined acc in
            let committed =
              List.exists (function
                | (_, CutTo c) when c <= frame -> true
                | _ -> false
              ) combined
            in
            if committed then List.rev acc'
            else loop more acc'
      in
      loop sols_first []
and solve_one (prog:program) (g:goal) (s:subst) (frame:int) : (subst * cut_sig) list =
  match g with
  | Cut ->
      (* Cut commits to the current frame; choices created before this point at [frame] are pruned. *)
      [ (s, CutTo frame) ]

  | Neg inner ->
      (* Negation-as-failure: run inner in an isolated frame; succeed iff no solutions. *)
      let _inner_frame = cut_frame_counter () in
      let sols = solve prog [inner] s _inner_frame in
      if sols = [] then [ (s, NoCut) ] else []

  | Call (Atom "true") -> [ (s, NoCut) ]
  | Call (Atom "fail") -> []

  | Call (Comp ("=", [t1; t2])) ->
      begin match unify t1 t2 s with
      | None -> []
      | Some s' -> [ (s', NoCut) ]
      end

  | Call (Comp ("=<", [t1; t2])) ->
      begin match eval_int s t1, eval_int s t2 with
      | Some i, Some j -> if i <= j then [ (s, NoCut) ] else []
      | _ -> []  (* require ground ints for this demo *)
      end

  | Call (Comp (pred, args)) ->
      (* User predicate *)
      let arity = List.length args in
      let matching =
        List.filter (fun {head; _} ->
          match head with
          | Atom p       -> (p = pred) && (arity = 0)
          | Comp (p, hs) -> (p = pred) && (List.length hs = arity)
          | _ -> false
        ) prog
      in
      solve_call prog pred args matching s frame

  | Call (Atom p) ->
      (* 0-arity form *)
      let matching =
        List.filter (fun {head; _} ->
          match head with
          | Atom q       -> q = p
          | Comp (q, hs) -> (q = p) && (List.length hs = 0)
          | _ -> false
        ) prog
      in
      solve_call prog p [] matching s frame

  | Call (Var _) ->
      failwith "Callable variables are not supported in this mini-interpreter"
and solve_call (prog:program) (pred:string) (args:term list)
               (clauses:clause list) (s:subst) (parent_frame:int)
  : (subst * cut_sig) list =
  (* Evaluate a predicate call by trying matching clauses.
     Each clause body runs in its own new frame.
     If a body produces CutTo that frame, we stop trying further clauses.
     We **swallow** the cut before returning upward (cut is local to this call). *)
  let rec loop cls acc =
    match cls with
    | [] -> List.rev acc
    | cl :: more ->
        let cl = freshen_clause cl in
        begin
          let head_term =
            match cl.head with
            | Atom p       -> Comp (p, [])
            | Comp (p, hs) -> Comp (p, hs)
            | Var _        -> failwith "Invalid clause head (Var)"
          in
          match unify head_term (Comp (pred, args)) s with
          | None ->
              loop more acc
          | Some s' ->
              let frame' = cut_frame_counter () in
              let sols = solve prog cl.body s' frame' in
              let committed_here =
                List.exists (function
                  | (_, CutTo c) when c = frame' -> true
                  | _ -> false
                ) sols
              in
              (* Swallow local cut signals; they shouldn't escape this call. *)
              let sols' = List.map (fun (s_ans, _) -> (s_ans, NoCut)) sols in
              let acc' = List.rev_append sols' acc in
              if committed_here then List.rev acc'
              else loop more acc'
        end
  in
  loop clauses []

(* ---------- Reification & printing ---------- *)

let reify_term s t = apply s t

let show_answers varnames (answers:(subst * cut_sig) list) =
  match answers with
  | [] -> print_endline "no."
  | _ ->
      List.iter (fun (s, _c) ->
        let items =
          List.map (fun v ->
            let tv = reify_term s (Var v) in
            v ^ " = " ^ pp_term tv
          ) varnames
        in
        print_endline ("{ " ^ String.concat "; " items ^ " }")
      ) answers

let run_query ~prog ~vars goals =
  let ans = solve prog goals [] 0 in
  show_answers vars ans

(* ---------- Test program ---------- *)

(* max/3 with cut: if X =< Y then pick Y and commit; else pick X *)
let cl_max_if =
  { head = Comp("max", [Var "X"; Var "Y"; Var "Y"]);
    body = [ Call (Comp("=<", [Var "X"; Var "Y"])); Cut ] }

let cl_max_else =
  { head = Comp("max", [Var "X"; Var "Y"; Var "X"]);
    body = [] }

(* parents *)
let parent_facts = [
  { head = Comp("parent", [Atom "alice"; Atom "bob"]); body = [] };
  { head = Comp("parent", [Atom "carol"; Atom "dave"]); body = [] };
]

(* not_parent(X,Y) :- \+ parent(X,Y). *)
let not_parent_rule =
  { head = Comp("not_parent", [Var "X"; Var "Y"]);
    body = [ Neg (Call (Comp("parent", [Var "X"; Var "Y"]))) ] }

(* Fact we add later to demonstrate non-monotonicity *)
let new_parent_fact =
  { head = Comp("parent", [Atom "alice"; Atom "charlie"]); body = [] }

let prog_base : program =
  [ cl_max_if; cl_max_else; not_parent_rule ] @ parent_facts

let prog_plus : program =
  new_parent_fact :: prog_base

(* ---------- Demos ---------- *)

let () =
  print_endline "== Demo 1: max/3 with cut (one answer) ==";
  let q1 = [ Call (Comp("max", [Atom "2"; Atom "5"; Var "M"])) ] in
  run_query ~prog:prog_base ~vars:["M"] q1;

  print_endline "\n== Demo 2a: negation-as-failure BEFORE adding fact ==";
  (* Constrain Y first, then negate: succeeds because parent(alice,charlie) is absent. *)
  let q2a = [ Call (Comp("=", [Var "Y"; Atom "charlie"]));
              Call (Comp("not_parent", [Atom "alice"; Var "Y"])) ] in
  run_query ~prog:prog_base ~vars:["Y"] q2a;

  print_endline "\n== Demo 2b: negation-as-failure AFTER adding fact (non-monotonic flip) ==";
  let q2b = [ Call (Comp("=", [Var "Y"; Atom "charlie"]));
              Call (Comp("not_parent", [Atom "alice"; Var "Y"])) ] in
  run_query ~prog:prog_plus ~vars:["Y"] q2b;

  print_endline "\nDone."

