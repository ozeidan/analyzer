module INV = IntDomain.Interval32
module B = Basetype
module BV = B.Variables
module OPT = BatOption
open OctagonDomain

(* type elt = OctagonDomain.elt *)

let cast varinfo inv =
  let get_ikind varinfo =
    match varinfo.Cil.vtype with
    | Cil.TInt (ikind, _) -> Some ikind
    | _ -> None
  in
  match get_ikind varinfo with
  | Some ikind -> INV.cast_to ikind inv
  | None -> inv

module MatrixCache = struct
  module L = (Lattice.Prod (Lattice.Fake(BV)) (IntDomain.Booleans))
  include Hashtbl.Make (Lattice.Prod (L) (L))
end

(* module MatrixCache = struct *)
(*   let create var_amount = Array.make_matrix (2 * var_amount) (2 * var_amount) None *)
(*   let mem arr ((i, i_inv), (j, j_inv)) = *)
(*     let invert_index i= i ^ 1 in *)
(*     let i = if i_inv then invert_index i else i in *)
(*     let j = if j_inv then invert_index j else j in *)
(*     Array.get (Array.get arr i) arr j |> not OPT.is_none *)
(*   let find arr ((i, i_inv), (j, j_inv)) = *)

(* end *)

module Liszt (B: Lattice.S) =
struct
  include Lattice.Liszt (B)

  let rec map2 keep f x y =
    let concat elt ls = if keep then elt::ls else ls in
    match x, y with
    | [], [] -> []
    | hd::tl, [] | [], hd::tl ->
      concat hd (map2 keep f [] tl)
    | xh :: xs, yh :: ys when (B.compare xh yh) = 0 ->
      f xh yh :: (map2 keep f xs ys)
    | xh :: xs, yh :: ys ->
      if B.compare xh yh = -1
      then concat xh (map2 keep f xs y)
      else concat yh (map2 keep f x ys)

  (* on meets we want to preserve the value of one octagon if *)
  (* the other octagon does not have a value at that position *)
  (* on joins we don't *)
  let meet = map2 true B.meet
  let join = map2 false B.join
  let narrow = map2 true B.narrow
  let widen = map2 false B.widen

  let rec leq x y =
    match x, y with
    | _, [] -> true
    | [], _ -> false
    | x :: xs, y :: ys
      when (B.compare x y) = 0 ->
      B.leq x y && leq xs ys
    | _ :: xs, y ->
      leq xs y
end

module type S =
sig
  include Lattice.S
  type key
  (* type value *)
  val set_constraint  : key * (bool * key) option * bool * int64 -> t -> t
  val adjust          : key -> int64 -> t -> t
  val erase           : key -> t -> t
  val projection      : key -> (bool * key) option -> t -> INV.t
  val strong_closure  : t -> t
  val map_to_matrix   : t -> elt array array * (BV.t, int) Hashtbl.t
  val matrix_to_map   : elt array array -> (BV.t, int) Hashtbl.t -> t
end


module E = struct
  include Lattice.Prod3 (IntDomain.Booleans) (Lattice.Fake(BV)) (INV)

  let compare (lsign, lvar, _) (rsign, rvar, _) =
    let cmp = compare lvar rvar in
    if cmp <> 0 then cmp else
    -(compare lsign rsign)

  let leq (lsign, lvar, linv) (rsign, rvar, rinv) =
    lsign = rsign && BV.equal lvar rvar && INV.leq linv rinv
end

module MyList = Liszt(E)

module VD = Lattice.Prod (INV) (Liszt(E))
module MapOctagon : S
  with type key = BV.t
= struct
  include MapDomain.MapTop (BV) (VD)

  let min_int = INV.top () |> INV.minimal |> BatOption.get
  let max_int = INV.top () |> INV.maximal |> BatOption.get

  let print_oct oct =
    Prelude.Ana.sprint pretty oct

  let rec set_constraint_list (sign, v, upper, value) ls =
    let inv = if upper
      then INV.ending value
      else INV.starting value
    in
    let inv = cast v inv in
    let delete = INV.is_top inv in
    let construct_inv old_inv =
      let old_inv = if INV.is_bot old_inv then INV.top () else old_inv in
      let old_lower = INV.minimal old_inv |> OPT.get in
      let old_upper = INV.maximal old_inv |> OPT.get in
      (if upper
       then INV.of_interval (old_lower, min old_upper value)
       else INV.of_interval (max old_lower value, old_upper))
      |> cast v
    in
    match ls with
    | x :: xs ->
      let (sign2, v2, inv2) = x in
      let cmp = BV.compare v v2 in
      if cmp = 0
      then begin
        if sign = sign2
        then
          let inv = construct_inv inv2 in
          if INV.is_top inv
          then
            xs
          else
            (sign, v, inv) :: xs
        else if sign = true
        then if delete then ls else (sign, v, inv) :: ls
        else
          (* if delete *)
          (* then *)
          x :: (set_constraint_list (sign, v, upper, value) xs)
          (* else x :: (sign, v, inv) :: xs *)
      end
      else if cmp = -1
      then if delete then ls else (sign, v, inv) :: ls
      else x :: (set_constraint_list (sign, v, upper, value) xs)
    | [] -> [(sign, v, inv)]

  let add_var var oct =
    if mem var oct
    then oct
    else add var (INV.top(), []) oct

  let rec delete_constraint (sign, v) ls =
    match ls with
    | x :: xs ->
      let (sign2, v2, _) = x in
      let cmp = BV.compare v v2 in
      if cmp = 0
      then begin
        if sign = sign2
        then xs
        else if sign = true
        then ls
        else x :: (delete_constraint (sign, v) xs)
      end
      else if cmp = -1
      then ls
      else x :: (delete_constraint (sign, v) xs)
    | [] -> []

  let find_constraints var ls =
    let rec find_constraints first ls =
      match ls with
      | (sign, v, inv) :: xs ->
        let cmp = BV.compare var v in
        if cmp = 0 then
          if sign = true then
            find_constraints (Some inv) xs
          else first, (Some inv)
        else if cmp = 1 then
          find_constraints first xs
        else
          first, None
      | [] -> first, None
    in
    find_constraints None ls

  let find x oct =
    try
      find x oct
    with Lattice.Unsupported _ ->
      (* Printf.printf "can't find %s in octagon %s\n" *)
      (*   x.vname (print_oct oct); *)
      raise Not_found

  let rec get_relation i j oct =
    if BV.compare i j = 1 then
      begin
        print_endline "swap"; get_relation j i oct
      end
    else try
        let _, l = find i oct in
        find_constraints j l
      with Not_found ->
        None, None

  let get_interval i oct =
    try
      let (inv, _) = find i oct in
      Some inv
    with Not_found ->
      None

  let print_inv = function
    | None -> print_endline "None"
    | Some i -> print_endline (INV.short 0 i)

  let rec set_constraint const oct =
    match const with
    | var, None, upper, value ->
      let oct = add_var var oct in
      let old_inv, consts = find var oct in
      let old_inv = if INV.is_bot old_inv then INV.top () else old_inv in
      let new_inv =
        if upper
        then INV.of_interval (OPT.get (INV.minimal old_inv), value)
        else INV.of_interval (value, OPT.get (INV.maximal old_inv))
      in
      add var (cast var new_inv, consts) oct
    | var1, Some (sign, var2), upper, value ->
      let cmp = (BV.compare var1 var2) in
      if cmp = 0
      then (Lattice.unsupported "wrong arguments")
      else if cmp = 1
      then
        let upper, value =
          if sign
          then upper, value
          else not upper, Int64.neg value
        in
        set_constraint (var2, Some (sign, var1), upper, value) oct
      else begin
        let oct = add_var var1 (add_var var2 oct) in
        let (const, consts) = find var1 oct in
        let consts = set_constraint_list (sign, var2, upper, value) consts in
        add var1 (const, consts) oct
      end

  let adjust var value oct =
    let add_inv = INV.of_int value in
    try
      let const, consts = find var oct in
      let const = INV.add add_inv const in
      let consts = List.map
          (fun (sign, var2, old_val) ->
             sign, var2, (INV.add old_val add_inv)) consts in
      let oct = add var (const, consts) oct in

      map (fun (a, consts) ->
          (a, List.map (fun (sign, var2, old_val) ->
               if (BV.compare var var2) <> 0
               then sign, var2, old_val
               else if sign = true
               then sign, var2, (INV.add old_val add_inv)
               else sign, var2, (INV.sub old_val add_inv)
             )
              consts)
        ) oct
    with Not_found ->
      oct

  let erase var oct =
    let oct = remove var oct in
    map (fun (a, consts) ->
        (a, List.fold_right (fun a b ->
             let (_, var2, _) = a in
             if (BV.compare var var2) = 0
             then b
             else a :: b
           ) consts [])
      ) oct

  let rec projection var1 var2 oct =
    (* TODO: swap var1 var2 if var1 > var2 *)
    match var2 with
    | None ->
      (try
         let (inv, _) = find var1 oct in
         inv
       with Not_found ->
         INV.top ())
    | Some (sign, var2) ->
      let cmp = (BV.compare var1 var2) in
      if cmp = -1 then
        let (_, consts) = find var1 oct in
        let first, second = find_constraints var2 consts in
        let candidate = if sign then first else second in
        match candidate with
        | Some inv -> inv
        | None -> INV.top ()
      else if cmp = 1 then
        if sign = true then
          projection var2 (Some (true, var1)) oct
        else
          INV.neg (projection var2 (Some (false, var1)) oct)
      else
        Lattice.unsupported "wrong arguments"

  let upper = function
    | None -> None
    | Some inv -> INV.maximal inv

  let lower = function
    | None -> None
    | Some inv -> INV.minimal inv

  let neg = function
    | None -> None
    | Some i -> Some (Int64.neg i)

  let cache = ref (MatrixCache.create 0)

  let matrix_get (i, i_inv) (j, j_inv) oct =
    let key = ((i, i_inv), (j, j_inv)) in
    if MatrixCache.mem !cache key
    then MatrixCache.find !cache key
    else
      let rec matrix_get (i, i_inv) (j, j_inv) oct =
        (* Printf.sprintf "Getting %B %s, %B %s" *)
        (* i_inv (BV.short () i) j_inv (BV.short () j) *)
        (* |> print_endline; *)
        let cmp = BV.compare i j in
        if cmp <> 0
        then
          if cmp = 1
          then
            let sumConst, difConst = get_relation j i oct in
            match i_inv, j_inv with
            | true, false -> upper sumConst
            | false, true -> OPT.map Int64.neg (lower sumConst)
            | false, false ->
              (* (if (i.vname = "b" && j.vname = "a") *)
              (*  then *)
              (*    begin *)
              (*      print_endline "***"; *)
              (*      print_inv difConst *)
              (*    end *)
              (*  else ()); *)
              upper difConst
            | true, true -> OPT.map Int64.neg (lower difConst)
          else if i_inv <> j_inv
          then matrix_get (j, i_inv) (i, j_inv) oct
          else matrix_get (j, not i_inv) (i, not j_inv) oct
        else
          let const = get_interval i oct in
          match i_inv, j_inv with
          | false, true -> OPT.map (Int64.mul (Int64.neg (Int64.of_int 2))) (lower const)
          | true, false -> OPT.map (Int64.mul (Int64.of_int 2)) (upper const)
          | _ -> Some (Int64.zero)
      in
      let res = OPT.bind
        (matrix_get (i, i_inv) (j, j_inv) oct)
        (fun a ->
           let a = min max_int a |> max min_int in
           if a = max_int || a = min_int then None
           else Some a
        )
      in
      MatrixCache.add !cache key res;
      res


  let rec matrix_set (i, i_inv) (j, j_inv) value oct =
    let key = ((i, i_inv), (j, j_inv)) in
    MatrixCache.add !cache key (Some value);
    if BV.compare i j <> 0 then
      (let i, j = j, i in
       let i_inv, j_inv =
         if i_inv = j_inv
         then (not i_inv, not j_inv)
         else i_inv, j_inv
       in
       MatrixCache.add !cache ((i, i_inv), (j, j_inv)) (Some value));
    (* let lower inv = INV.minimal inv |> OPT.get in *)
    (* let upper inv = INV.maximal inv |> OPT.get in *)
    (* Printf.printf "Setting %Ld at %B %s, %B %s\n" *)
    (*   value i_inv (BV.short () i) j_inv (BV.short () j); *)
    let cmp = BV.compare i j in
    if cmp <> 0
    then
      if cmp = 1
      then
        (* let sumConst, difConst = get_relation j i oct in *)
        (* let () = ( *)
        (*   if i_inv && j_inv *)
        (*   then *)
        (*     (print_inv sumConst; print_inv difConst) *)
        (*   else () *)
        (* ) in *)
        (* let sumConst = OPT.default (INV.top ()) sumConst in *)
        (* let difConst = OPT.default (INV.top ()) difConst in *)
        (* let () = print_oct oct |> print_endline in *)
        (* let () = Printf.printf "setting %Ld at %B %s, %B %s\n" value i_inv i.vname j_inv j.vname in *)
        match i_inv, j_inv with
        | true, false ->
          set_constraint (j, Some (true, i), true, value) oct
        | false, true ->
          set_constraint (j, Some (true, i), false, Int64.neg value) oct
        | false, false ->
          set_constraint (j, Some (false, i), true, value) oct
        | true, true ->
          set_constraint (j, Some (false, i), false, Int64.neg value) oct
      else if i_inv <> j_inv
      then matrix_set (j, i_inv) (i, j_inv) value oct
      else matrix_set (j, not i_inv) (i, not j_inv) value oct
    else
      (* let const = OPT.default (INV.top ()) (get_interval i oct) in *)
    if not i_inv && j_inv
    then
      set_constraint (i, None, false, Int64.neg(Int64.div value (Int64.of_int 2))) oct
    else if i_inv && not j_inv
    then
      set_constraint (i, None, true, Int64.div value (Int64.of_int 2)) oct
    else Lattice.unsupported "error"

  (* let rec unpack inv = *)
  (*   match inv with *)
  (*   | None -> unpack (Some (INV.top ())) *)
  (*   | Some inv -> *)
  (*     (match INV.minimal inv, INV.maximal inv with *)
  (*      | Some min, Some max -> min, max *)
  (*      | _ -> unpack (Some (INV.top ()))) *)
  (* in *)


  (* let inv_i, constraints = ilist in let inv_j, _ = jlist in let (li, ui), (lj, uj) = unpack (Some inv_i), *)
  (*                          unpack (Some inv_j) in *)
  (* let (sumConstraint, subConstraint) = *)
  (*   MyList.find_constraints j constraints in *)
  (* let pl, pu = unpack sumConstraint in *)
  (* let nl, nu = unpack subConstraint in *)
  (* let pl, pu = max pl (Int64.add li lj), min pu (Int64.add ui uj) in *)
  (* let nl, nu = max nl (Int64.sub li uj), min nu (Int64.sub ui lj) in *)
  (* let constraints = MyList.set_constraint (true, j, INV.of_interval (pl, pu)) constraints in *)
  (* let constraints = MyList.set_constraint (false, j, INV.of_interval (nl, nu)) constraints in *)
  (* add i (inv_i, constraints) oct *)

  let strong_closure oct =
    let vars = fold (fun key _ keys -> key::keys) oct []
               |> List.rev
    in

    let var_amount = List.length vars in
    cache := MatrixCache.create (var_amount * var_amount * 4);

    let add a b =
      match a, b with
      | Some a, Some b -> Some (Int64.add a b)
      | _ -> None
    in

    let min a b =
      match a, b with
      | Some a, Some b -> Some (min a b)
      | Some a, None | None, Some a -> Some a
      | _ -> None
    in

    let signs = [(false, false);
                 (true, false);
                 (false, true);
                 (true, true)]
    in

    (* let printf name var = *)
    (*   match var with *)
    (*   | Some x -> Printf.printf "%s = %Ld\n" name x *)
    (*   | None -> Printf.printf "%s = None\n" name *)
    (* in *)

    let strong_closure_s oct =
      List.fold_left (fun oct i ->
          List.fold_left (fun oct j ->
              if BV.compare i j > 0 then
                List.fold_left (fun oct (i_sign, j_sign) ->
                    let old_val = matrix_get (i, i_sign) (j, j_sign) oct in
                    let first = (matrix_get (i, i_sign) (i, i_sign <> true) oct) in
                    let second = (matrix_get (j, j_sign <> true) (j, j_sign) oct) in
                    let new_val = add first second in
                    let new_val = OPT.map
                        (fun x -> Int64.div x (Int64.of_int 2))
                        new_val
                    in
                    let new_val = min old_val new_val in
                    if new_val <> old_val &&
                       not (old_val = None &&
                            not ((OPT.get new_val)
                                 < max_int))
                    then
                      match new_val with
                      | Some new_val ->
                        (* print_endline "strong_closure"; *)
                        (* print_oct oct; *)
                        (* printf "old" old_val; *)
                        (* printf "first" first; *)
                        (* printf "second" second; *)
                        (* Printf.printf "Setting value %Ld at %B %s %B %s\n%!" *)
                        (*   new_val i_sign i.vname j_sign j.vname; *)
                        matrix_set (i, i_sign) (j, j_sign) new_val oct
                      | None -> oct
                    else oct
                  ) oct signs
              else oct
            ) oct vars
        ) oct vars
    in

    List.fold_left (fun oct k ->
        (* Printf.sprintf "k = %s" (BV.short 0 k) |> print_endline; *)
        let oct = List.fold_left (fun oct i ->
            List.fold_left (fun oct j ->
                let cmp = BV.compare i j in
                if cmp < 0
                then oct
                else
                  (* let () = Printf.printf "i = %s\n" (BV.short 0 i) in *)
                  (* let () = Printf.printf "j = %s\n" (BV.short 0 j) in *)
                  List.fold_left (fun oct (i_sign, j_sign) ->
                      if cmp = 0 && i_sign = j_sign then oct else
                        (* let () = Printf.printf "i_sign = %B\n" i_sign in *)
                        (* let () = Printf.printf "j_sign = %B\n" j_sign in *)
                        let old_val = matrix_get (i, i_sign) (j, j_sign) oct in
                        let a = add (matrix_get (i, i_sign) (k, false) oct)
                            (matrix_get (k, false) (j, j_sign) oct) in
                        let b = add (matrix_get (i, i_sign) (k, true) oct)
                            (matrix_get (k, true) (j, j_sign) oct) in
                        let c = add (matrix_get (i, i_sign) (k, false) oct)
                            (add (matrix_get (k, false) (k, true) oct)
                               (matrix_get (k, true) (j, j_sign) oct)) in
                        let d = add (matrix_get (i, i_sign) (k, true) oct)
                            (add (matrix_get (k, true) (k, false) oct)
                               (matrix_get (k, false) (j, j_sign) oct)) in
                        let new_val = List.fold_left min old_val [a; b; c; d] in
                        (* printf "new" new_val; *)
                        (* print_oct oct; *)
                        if new_val <> old_val &&
                           not (old_val = None &&
                                not ((OPT.get new_val)
                                     < max_int))
                        then begin
                          let oct =
                            match new_val with
                            | Some new_val ->
                              (* print_oct oct; *)
                              (* printf "old" old_val; *)
                              (* printf "a" a; *)
                              (* printf "b" b; *)
                              (* printf "c" c; *)
                              (* printf "d" d; *)
                              (* Printf.printf "Setting value %Ld at %B %s %B %s (k=%s)\n%!" *)
                              (*   new_val i_sign i.vname j_sign j.vname k.vname; *)
                              matrix_set (i, i_sign) (j, j_sign) new_val oct
                            | None -> oct
                          in oct
                          (* print_oct oct; oct *)
                        end
                        else oct
                    ) oct signs
              ) oct vars
          ) oct vars
        in
        let oct = strong_closure_s oct in
        (* cache := MatrixCache.empty; *)
        oct
      ) oct vars

  (* can't widen the result as it might induce an infinite chain *)
  let widen a b = widen a (strong_closure b)
  let narrow a b = narrow a (strong_closure b) |> strong_closure

  let meet a b = meet a b |> strong_closure
  let join a b = join a b |> strong_closure

  let inv_index i = i lxor 1

  let map_to_matrix oct =
    let vars : (BV.t, int) Hashtbl.t = Hashtbl.create 0 in
    let () = iter (fun var _ -> Hashtbl.add vars var (Hashtbl.length vars)) oct in

    let matrix =
      let size = (Hashtbl.length vars) * 2 in
      Array.make_matrix size size Infinity
    in
    let add_constraints var (const, consts) =
      let set i j v = Array.set (Array.get matrix i) j (Val (Int64.to_float v)) in
      let index1 = (Hashtbl.find vars var) * 2 in
      set index1 index1 Int64.zero;
      set (inv_index index1) (inv_index index1) Int64.zero;
      let upper = INV.maximal const |> OPT.get in
      let lower = INV.minimal const |> OPT.get in
      let two = Int64.of_int 2 in
      if upper <> max_int
      then set (inv_index index1) index1
          (Int64.mul upper two);
      if lower <> min_int
      then set index1 (inv_index index1)
          (Int64.neg (Int64.mul lower two));

      let add_constraints (sign, var2, const) =
        let index2 = (Hashtbl.find vars var2) * 2 in
        let upper = INV.maximal const |> OPT.get in
        let lower = INV.minimal const |> OPT.get in
        if not (Int64.compare lower min_int = 0)
        then if sign = true
          then (set index1 (inv_index index2) (Int64.neg lower);
                set index2 (inv_index index1) (Int64.neg lower))
          else (set (inv_index index2) (inv_index index1) (Int64.neg lower);
                set index1 index2 (Int64.neg lower));
        if not (Int64.compare upper max_int = 0)
        then if sign = true
          then (set (inv_index index1) index2 upper;
                set (inv_index index2) index1 upper)
          else (set index2 index1 upper;
                set (inv_index index1) (inv_index index2) upper)
      in
      List.iter add_constraints consts
    in

    iter add_constraints oct;
    matrix, vars

  let matrix_to_map matrix vars =
    let inv_vars = Hashtbl.create (Hashtbl.length vars) in
    Hashtbl.iter (fun var index -> Hashtbl.add inv_vars (index * 2) var) vars;
    (* let var_amount = (Array.length matrix) / 2 in *)
    let get i j = Array.get (Array.get matrix i) j in

    let rec matrix_iter i j oct =
      if j >= Array.length matrix
      then matrix_iter (i + 2) 0 oct
      else if i >= Array.length matrix
      then oct
      else
        let var1 = Hashtbl.find inv_vars i in
        let var2 = Hashtbl.find inv_vars j in
        if i = j
        then
          let unpack = function | Infinity -> max_int | Val f ->
            Int64.div (Int64.of_float f) (Int64.of_int 2) in
          (* let () = Printf.printf "(%d, %d)\n" (inv_index i) i in *)
          (* let () = Printf.printf "(%d, %d)\n" i (inv_index i) in *)
          let upper = get (inv_index i) i |> unpack in
          let lower = Int64.neg (get i (inv_index i) |> unpack) in
          (* let () = Printf.printf "(%Ld, %Ld)\n" lower upper in *)
          let oct = set_constraint (var1, None, true, upper) oct in
          let oct = set_constraint (var1, None, false, lower) oct in
          matrix_iter i (j + 2) oct
        else if i < j
        then
          let unpack upper =
            function
            | Infinity ->
              if upper
              then max_int
              else min_int
            | Val f ->
              let f = Int64.of_float f in
              if upper then f else Int64.neg f
          in
          let oct =
            let upper = get (inv_index i) j |> unpack true in
            let lower = get i (inv_index j) |> unpack false in
            set_constraint (var1, Some(true, var2), true, upper)
              (set_constraint (var1, Some(true, var2), false, lower) oct)
          in
          let oct =
            let upper = get (inv_index i) (inv_index j) |> unpack true in
            let lower = get i j |> unpack false in
            set_constraint (var1, Some(false, var2), true, upper)
              (set_constraint (var1, Some(false, var2), false, lower) oct)
          in
          matrix_iter i (j + 2) oct
        else
          matrix_iter i (j + 2) oct
    in

    matrix_iter 0 0 (top ())

  let use_matrix_closure = false

  let strong_closure oct =
    if use_matrix_closure
    then
      let matrix, vars = map_to_matrix oct in
      let matrix = ArrayOctagon.strong_closure matrix in
      matrix_to_map matrix vars
    else
      strong_closure oct
end

module MapOctagonBot : S
  with type key = BV.t = struct
  include Lattice.LiftBot (MapOctagon)

  type key = MapOctagon.key
  (* type value = MapOctagon.value *)

  let ignore_bot f = function
    | `Bot -> `Bot
    | `Lifted x -> lift @@ f x

  let set_constraint const =
    ignore_bot (MapOctagon.set_constraint const)

  let adjust key value =
    ignore_bot (MapOctagon.adjust key value)

  let erase key =
    ignore_bot (MapOctagon.erase key)

  let strong_closure =
    ignore_bot MapOctagon.strong_closure

  let map_to_matrix = function
    | `Bot -> Array.make_matrix 0 0 Infinity, Hashtbl.create 0
    | `Lifted x -> MapOctagon.map_to_matrix x

  let matrix_to_map m v = `Lifted (MapOctagon.matrix_to_map m v)

  let projection key key2 = function
    | `Bot -> INV.top ()
    | `Lifted x -> MapOctagon.projection key key2 x
end

module PA = Prelude.Ana

let print_oct oct =
  Prelude.Ana.sprint MapOctagon.pretty oct
let elt_to_string elt =
  match elt with
  | Infinity -> "inf"
  | Val f -> string_of_float f
let to_string_matrix oct =
  Array.fold_left
    (fun s inner -> s ^ "[" ^ (Array.fold_left (fun s elt -> s ^ (elt_to_string elt) ^ " ") "" inner) ^ "]\n") "" oct

let () =
  let oct = MapOctagon.top () in
  (* let oct2 = MapOctagon.top () in *)
  let typ = PA.TInt(PA.IInt, []) in
  (* let i = PA.makeVarinfo false "i" typ in *)
  (* let p = PA.makeVarinfo false "p" typ in *)
  (* let oct = MapOctagon.set_constraint (i, Some(true, p), true, Int64.of_int 10) oct in *)
  (* let oct = MapOctagon.set_constraint (i, Some(true, p), false, Int64.of_int 1) oct in *)
  (* let oct = MapOctagon.set_constraint (i, None, true, Int64.of_int 5) oct in *)
  (* let oct = MapOctagon.set_constraint (i, None, false, Int64.of_int 1) oct in *)
  Random.init 123;
  let var_num = 100 in
  let rec insert_vars i oct =
    if i > var_num then oct else
      let var = PA.makeVarinfo false (string_of_int i) typ in
      let lower = Random.int 100000 in
      let upper = lower + (Random.int 100000) in
      let oct = MapOctagon.set_constraint (var, None, true, Int64.of_int upper) oct in
      let oct = MapOctagon.set_constraint (var, None, false, Int64.of_int lower) oct in
      insert_vars (i + 1) oct
  in
  let oct = insert_vars 0 oct in
  let _ = MapOctagon.strong_closure oct in
  print_newline ()
(* let c = PA.makeVarinfo false "c" typ in *)
(* let oct = MapOctagon.set_constraint (i, None, true, Int64.of_int 1) oct in *)
(* let oct = MapOctagon.set_constraint (i, None, false, Int64.of_int 1) oct in *)
(* let oct = MapOctagon.set_constraint (p, None, true, Int64.of_int 0) oct in *)
(* let oct = MapOctagon.set_constraint (p, None, false, Int64.of_int 0) oct in *)
(* print_oct oct |> print_endline; *)
(* print_oct (MapOctagon.strong_closure oct) |> print_endline *)
(* let matrix_oct, var_map = MapOctagon.map_to_matrix oct in *)
(* (1* print_endline (to_string_matrix matrix_oct); *1) *)
(* (1* let matrix_strong_closure = ArrayOctagon.strong_closure matrix_oct in *1) *)
(* (1* print_endline (to_string_matrix matrix_strong_closure); *1) *)
(* (1* print_oct (MapOctagon.strong_closure oct) |> print_endline *1) *)
(* (1* print_oct (MapOctagon.strong_closure oct) |> print_endline; *1) *)
(* let oct = MapOctagon.matrix_to_map matrix_oct var_map in *)
(* print_oct (MapOctagon.strong_closure oct) |> print_endline *)
