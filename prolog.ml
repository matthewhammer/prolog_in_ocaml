(* mini_prolog_cut.ml
   Minimal Prolog interpreter in one file (OCaml) with Cut (!).
   - Occurs check + variable renaming
   - Depth-first search
   - Cut support to prune alternatives
   - Tiny REPL for single-goal queries
*)

(* ---- data types ---- *)
type term =
  | Var of string
  | Atom of string
  | Compound of string * term list

type clause = Clause of term * term list  (* head :- body1, body2, ... *)

type substitution = (string * term) list  (* var name -> term *)

(* ---- utilities / pretty printing ---- *)
let rec string_of_term = function
  | Var v -> v
  | Atom a -> a
  | Compound (f, []) -> f
  | Compound (f, args) ->
      let args_s = String.concat ", " (List.map string_of_term args) in
      Printf.sprintf "%s(%s)" f args_s

(* ---- substitution application ---- *)
let rec lookup subst v =
  match subst with
  | [] -> None
  | (x, t) :: rest -> if x = v then Some t else lookup rest v

let rec apply_subst (subst : substitution) (t : term) : term =
  match t with
  | Var v ->
      (match lookup subst v with
       | None -> Var v
       | Some t' -> apply_subst subst t')
  | Atom _ -> t
  | Compound (f, args) -> Compound (f, List.map (apply_subst subst) args)

(* ---- occurs check ---- *)
let rec occurs (v : string) (t : term) (subst : substitution) : bool =
  let t = apply_subst subst t in
  match t with
  | Var v2 -> v = v2
  | Atom _ -> false
  | Compound (_, args) -> List.exists (fun a -> occurs v a subst) args

(* ---- unify ---- *)
let rec unify (t1 : term) (t2 : term) (subst : substitution) : substitution option =
  let t1 = apply_subst subst t1 in
  let t2 = apply_subst subst t2 in
  match t1, t2 with
  | Var v1, Var v2 when v1 = v2 -> Some subst
  | Var v, t | t, Var v ->
      if occurs v t subst then None
      else Some ((v, t) :: subst)
  | Atom a1, Atom a2 when a1 = a2 -> Some subst
  | Compound (f1, args1), Compound (f2, args2)
       when f1 = f2 && List.length args1 = List.length args2 ->
      unify_lists args1 args2 subst
  | _ -> None

and unify_lists l1 l2 subst =
  match l1, l2 with
  | [], [] -> Some subst
  | x::xs, y::ys ->
      (match unify x y subst with
       | None -> None
       | Some subst' -> unify_lists xs ys subst')
  | _ -> None

(* ---- variable renaming ---- *)
let counter = ref 0
let fresh_suffix () =
  let n = !counter in
  incr counter;
  "_" ^ string_of_int n

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

let rec collect_vars_term term acc =
  match term with
  | Var v -> StringSet.add v acc
  | Atom _ -> acc
  | Compound (_, args) -> List.fold_left (fun s t -> collect_vars_term t s) acc args

let collect_vars_clause (Clause (head, body)) =
  let s = collect_vars_term head StringSet.empty in
  List.fold_left (fun acc t -> collect_vars_term t acc) s body

let rename_term rename_map term =
  let rec go t =
    match t with
    | Var v -> (try Var (StringMap.find v rename_map) with Not_found -> Var v)
    | Atom _ as a -> a
    | Compound (f, args) -> Compound (f, List.map go args)
  in
  go term

let rename_clause (Clause (head, body)) =
  let vars_set = collect_vars_clause (Clause (head, body)) in
  let rename_map =
    StringSet.fold (fun v m ->
      let v' = v ^ fresh_suffix () in
      StringMap.add v v' m
    ) vars_set StringMap.empty
  in
  let head' = rename_term rename_map head in
  let body' = List.map (rename_term rename_map) body in
  Clause (head', body')

(* ---- resolution with Cut ---- *)
let rec solve program goals subst =
  match goals with
  | [] -> [subst]
  | goal :: rest ->
      match goal with
      | Atom "!" ->
          (* commit: prune alternatives for this branch *)
          solve_cut program rest subst
      | _ ->
          List.fold_left (fun acc clause ->
            let Clause (head, body) = rename_clause clause in
            match unify goal head subst with
            | None -> acc
            | Some subst' ->
                let new_goals = List.map (apply_subst subst') (body @ rest) in
                let sols = solve program new_goals subst' in
                acc @ sols
          ) [] program

and solve_cut program goals subst =
  match goals with
  | [] -> [subst]
  | goal :: rest ->
      match goal with
      | Atom "!" ->
          solve_cut program rest subst
      | _ ->
          let rec try_first_clause = function
            | [] -> []
            | clause :: cs ->
                let Clause (head, body) = rename_clause clause in
                match unify goal head subst with
                | None -> try_first_clause cs
                | Some subst' ->
                    let new_goals = List.map (apply_subst subst') (body @ rest) in
                    solve_cut program new_goals subst'
          in
          try_first_clause program

(* ---- variable listing ---- *)
let rec vars_in_term t acc =
  match t with
  | Var v -> if List.mem v acc then acc else v :: acc
  | Atom _ -> acc
  | Compound (_, args) -> List.fold_left (fun a x -> vars_in_term x a) acc args

let vars_in_query qterms =
  List.fold_left (fun a t -> vars_in_term t a) [] qterms

(* ---- example program ---- *)
let prog = [
  Clause (Compound ("likes", [Atom "bob"; Atom "alice"]), []);
  Clause (Compound ("likes", [Atom "alice"; Atom "bob"]), []);
  Clause (Compound ("likes", [Atom "carol"; Atom "dave"]), []);
  Clause (Compound ("friends", [Var "X"; Var "Y"]),
          [Compound ("likes", [Var "X"; Var "Y"]);
           Compound ("likes", [Var "Y"; Var "X"])]);
  Clause (Compound ("mutual_friend_of", [Var "X"; Var "Z"]),
          [Compound ("friends", [Var "X"; Var "Y"]);
           Compound ("friends", [Var "Y"; Var "Z"])]);
  (* cut example: first_child(P, C) returns only the first child found *)
  Clause (Compound ("parent_of", [Atom "alice"; Atom "bob"]), []);
  Clause (Compound ("parent_of", [Atom "alice"; Atom "carol"]), []);
  Clause (Compound ("first_child", [Var "P"; Var "C"]),
          [Compound ("parent_of", [Var "P"; Var "C"]); Atom "!"])
]

let queries = [
  [Compound ("friends", [Var "A"; Var "B"])];
  [Compound ("likes", [Atom "bob"; Var "Who"])];
  [Compound ("mutual_friend_of", [Var "A"; Var "C"])];
  [Compound ("first_child", [Atom "alice"; Var "Who"])]
]

(* ---- printing solutions ---- *)
let print_solution_for_query query sols =
  let qvars = vars_in_query query in
  if sols = [] then (print_endline "No solutions."; print_endline "----")
  else
    List.iteri (fun i subst ->
      Printf.printf "Solution %d:\n" (i+1);
      List.iter (fun v ->
        let t = apply_subst subst (Var v) in
        Printf.printf "  %s = %s\n" v (string_of_term t)
      ) qvars;
      print_endline "----"
    ) sols

let () =
  Printf.printf "Mini Prolog interpreter (with cut)\n\n";
  List.iteri (fun qi query ->
    Printf.printf "Query %d: %s\n" (qi+1) (String.concat ", " (List.map string_of_term query));
    let sols = solve prog query [] in
    print_solution_for_query query sols
  ) queries
