module INV = IntDomain.Interval32
module BV = Basetype.Variables
module OPT = BatOption

module MyList =
struct
  module P = Lattice.Prod3 (IntDomain.Booleans) (Lattice.Fake(BV)) (INV)
  module LD = Lattice.Liszt (P)
  include LD

  let rec leq x y =
    match x, y with
    | _, [] -> true
    | [], _ -> false
    | (_, v1, int1) :: xs, (_, v2, int2) :: ys when (compare v1 v2) = 0 ->
      INV.leq int1 int2 && leq xs ys
    | _ :: xs, y ->
      leq xs y

  let compare_elt (s1, v1, _) (s2, v2, _) =
    if s1 = s2 then compare v1 v2
    else if s1 = true then -1 else 1

  let find_constraints var ls =
    let rec find_constraints first ls =
      match ls with
      | (sign, v, inv) :: xs ->
        if BV.compare var v = 0 then
          if sign = true then
            find_constraints (Some inv) xs
          else first, (Some inv)
        else
          find_constraints first xs
      | [] -> first, None
    in
    find_constraints None ls

  let rec set_constraint (sign, v, inv) ls =
    match ls with
    | (_, v2, _) :: xs when (BV.compare v v2) = -1 ->
      set_constraint (sign, v, inv) xs
    | (sign2, v2, _) :: xs when (BV.compare v v2) = 0 && sign = sign2 ->
      (sign, v, inv) :: xs
    | (sign2, v2, inv2) :: xs when (BV.compare v v2) = 0 && sign <> sign2 ->
      if sign = true then (sign, v, inv) :: (sign2, v2, inv2) :: xs
      else set_constraint (sign, v, inv) xs
    | (_, v2, _) :: xs ->
      (sign, v, inv) :: xs
    | [] -> [(sign, v, inv)]

  let rec map2 f x y =
    let concat elt ls =
      match elt with
      | Some x -> x::ls
      | None -> ls
    in
    match x, y with
    | [], [] -> []
    | hd::tl, [] -> concat(f (Some hd) None)(map2 f tl [])
    | [], hd::tl -> concat(f None (Some hd))(map2 f [] tl)
    | x :: xs, y :: ys when (compare_elt x y) = 0 ->
      concat(f (Some x) (Some y))(map2 f xs ys)
    | xh :: xs, yh :: ys ->
      if compare_elt xh yh = -1
      then concat(f (Some xh) None)(map2 f xs y)
      else concat(f None (Some yh))(map2 f x ys)

  let app f preserve x y =
    match x, y with
    | Some x, Some y -> Some(f x y)
    | None, x | x, None ->
      if preserve then x else None

  let meet = map2 (app P.meet true)
  let join = map2 (app P.join false)
  let widen = map2 (fun x y ->
      match x, y with
      | Some x, Some y -> Some(P.widen x y)
      | _ -> None)

  let narrow = map2 (fun x y ->
      match x, y with
      | Some x, Some y -> Some(P.narrow x y)
      | x, None | None, x -> x)
end

(* module type S = *)
(* sig *)
(*   include MapDomain.MapTop (BV) (VD) *)
(*   val set_constraint : key * (IntDomain.Booleans * key) option * INV.t -> t -> t *)
(* end *)

module MyMapTop (Domain: MapDomain.Groupable) (Range: Lattice.S) = struct

end

module type S =
sig
  include Lattice.S
  type key
  type value
  val set_constraint  : key * (IntDomain.Booleans.t * key) option * INV.t -> t -> t
  val strong_closure  : t -> t
  val print_oct       : t -> unit
end

module VD = Lattice.Prod (INV) (MyList)
module MapOctagon : S
  with type key = BV.t
= struct
  include MapDomain.MapTop (BV) (VD)
  (* type key = M.key *)
  (* let oct_mapi f oct = *)
  (*   let find_consts var2 = *)
  (*     let rec find_consts first = function *)
  (*       | x :: xs -> *)
  (*         let (sign, var, inv) = x in *)
  (*         let cmp = BV.compare var2 var in *)
  (*         if cmp = 0 *)
  (*         then *)
  (*           if sign = true *)
  (*           then find_consts (Some x) xs *)
  (*           else (first, Some x), xs *)
  (*         else if cmp = -1 *)
  (*         then (first, None), x::xs *)
  (*         else if cmp = 1 *)
  (*         then raise Lattice.unsupported *)
  (*       | [] -> (first, None), [] *)
  (*     in find_consts None *)
  (*   in *)
  (*   mapi (fun i (i_inv, consts) -> *)
  (*       mapi (fun j (j_inv, _) (before, consts) -> *)
  (*           if (BV.compare i j) <> -1 *)
  (*           then (before, consts) *)
  (*           else *)
  (*             let consts, after = *)
  (*               find_consts var2 consts in *)
  (*             let var1_inv var2_inv (sumConst, difConst) = *)
  (*               f var1_inv var2_inv consts in *)
  (*         ) oct (difConst::sumConst::before, after) *)
  (*     ) oct *)

  (* let oct_mapi f oct = *)
  (*   (1* TODO: quite expensive, maybe optimize this *1) *)
  (*   fold (fun k (k_inv, k_consts) oct -> *)
  (*       fold (fun i (i_inv, i_consts) oct -> *)
  (*           fold (fun j (j_inv, j_consts) oct -> *)
  (*               if BV.compare i j <> -1 || *)
  (*                  BV.compare i k = 0 || *)
  (*                  BV.compare j k = 0 *)
  (*               then oct *)
  (*               else *)
  (*                 let (sumConst, difConst) = *)
  (*                   MyList.find_constraints j i_consts in *)
  (*                 let (kiSumConst, kiDifConst) = *)
  (*                   if BV.compare i k = -1 *)
  (*                   then MyList.find_constraints k i_consts *)
  (*                   else MyList.find_constraints i k_consts *)
  (*                 in *)
  (*                 let (kjSumConst, kjDifConst) = *)
  (*                   if BV.compare j k = -1 *)
  (*                   then MyList.find_constraints k j_consts *)
  (*                   else MyList.find_constraints j k_consts *)
  (*                 in *)
  (*                 let i_inv', j_inv', sumConst', difConst' = *)
  (*                   f k_inv i_inv j_inv *)
  (*                     (kiSumConst, kiDifConst) *)
  (*                     (kjSumConst, kjDifConst) *)
  (*                     (sumConst, difConst) in *)
  (*                 let oct = if i_inv = i_inv' then oct else set_constraint (i, None, i_inv') oct in *)
  (*                 let oct = if j_inv = j_inv' then oct else set_constraint (j, None, j_inv') oct in *)
  (*                 let oct = if sumConst = sumConst' then oct else set_constraint (i, (true, j), sumConst') oct in *)
  (*                 let oct = if difConst = difConst' then oct else set_constraint (i, (false, j), difConst') oct in *)
  (*                 oct *)
  (*             ) oct oct *)
  (*         ) oct oct *)
  (*     ) oct oct *)


  (* let strong_closure = *)
  (*   let unpack inv = *)
  (*     match INV.minimal inv, INV.maximal inv with *)
  (*     | Some a, Some b -> a, b *)
  (*     | _ -> Lattice.unsupported "error" *)
  (*   in *)
  (*   let add a b = *)
  (*     if a > Int64.sub Int64.max_int b *)
  (*     then In64.max_int *)
  (*     else Int64.add a b in *)
  (*   oct_mapi *)
  (*     (fun k_inv i_inv j_inv *)
  (*       (kiSumConst, kiDifConst) *)
  (*       (kjSumConst, kjDifConst) *)
  (*       (sumConst, difConst) -> *)
  (*       let ld, ud = unpack difConst in *)
  (*       let ls, us = unpack sumConst in *)
  (*       let kild, kiud = unpack kiDifConst in *)
  (*       let kils, kius = unpack kiSumConst in *)
  (*       let kjld, kjud = unpack kjDifConst in *)
  (*       let kjls, kjus = unpack kjSumConst in *)

  (*       let ud = min ud (min (add kjud kiud) (add kjls kius)) in *)
  (*       let ld = min ld (min (add kjus kils) (add *)
  (*     ) *)

  let min_int = INV.top () |> INV.minimal |> BatOption.get
  let max_int = INV.top () |> INV.maximal |> BatOption.get

  let print_oct oct =
    let doc = pretty () oct in
    Prelude.Ana.fprint Pervasives.stdout 80 doc; print_newline ()

  let rec get_relation i j oct =
    if j < i then get_relation j i oct
    else try
        let _, l = find i oct in
        MyList.find_constraints j l
      with Lattice.Unsupported _ ->
        None, None

  let get_interval i oct  =
    try
      let (inv, _) = find i oct in
      Some inv
    with Lattice.Unsupported _ ->
      None

  let rec set_constraint const oct =
    match const with
    | var, None, inv ->
      (try
         let (_, consts) = find var oct in
         add var (inv, consts) oct
       with Lattice.Unsupported _ ->
         print_string "setting new interval for variable";
         INV.short 0 inv |> print_endline;
         add var (inv, []) oct)
    | var1, Some (sign, var2), inv ->
      let cmp = (BV.compare var1 var2) in
      if cmp = 0
      then (Lattice.unsupported "wrong arguments")
      else if cmp = 1
      then
        if sign = true
        then set_constraint (var2, Some (sign, var1), inv) oct
        else set_constraint (var2, Some (sign, var1), INV.neg inv) oct
      else begin
        let oct = try
            let _ = find var2 oct in
            oct
          with Lattice.Unsupported _ ->
            add var2 (INV.top(), []) oct
        in
        (* let delete = INV.is_top const in *)
        try
          let (const, consts) = find var1 oct in
          let consts = MyList.set_constraint (sign, var2, inv) consts in
          add var1 (const, consts) oct
        with Lattice.Unsupported _ ->
          add var1 (INV.top (), [(sign, var2, inv)]) oct
      end

  let upper = function
    | None -> None
    | Some inv -> INV.maximal inv

  let lower = function
    | None -> None
    | Some inv -> INV.minimal inv

  let neg = function
    | None -> None
    | Some i -> Some (Int64.neg i)

  let print_inv = function
    | None -> print_endline "None"
    | Some i -> print_endline (INV.short 0 i)

  (* let matrix_get i j oct = *)
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
          (if (i.vname = "b" && j.vname = "a")
           then
             begin
               print_endline "***";
               print_inv difConst
             end
           else ());
          upper difConst
        | true, true -> OPT.map Int64.neg (lower difConst)
      else if (not i_inv && j_inv) || (i_inv && not j_inv)
      then matrix_get (j, j_inv) (i, i_inv) oct
      else OPT.map Int64.neg (matrix_get (j, j_inv) (i, i_inv) oct)
    else
      let const = get_interval i oct in
      match i_inv, j_inv with
      | false, true -> OPT.map Int64.neg (OPT.map (Int64.mul (Int64.of_int 2)) (lower const))
      | true, false -> OPT.map (Int64.mul (Int64.of_int 2)) (upper const)
      | _ -> Some (Int64.zero)
  (* in matrix_get i j oct *)
  (*    |> OPT.map (min max_int) *)
  (*    |> OPT.map (max min_int) *)

  let rec matrix_set (i, i_inv) (j, j_inv) value oct =
    let lower inv = INV.minimal inv |> OPT.get in
    let upper inv = INV.maximal inv |> OPT.get in
    (* Printf.sprintf "Setting %Ld at %B %s, %B %s" *)
    (* value i_inv (BV.short () i) j_inv (BV.short () j) *)
    (* |> print_endline; *)
    let cmp = BV.compare i j in
    if cmp <> 0
    then
      if cmp = 1
      then
        let sumConst, difConst = get_relation i j oct in
        let sumConst = OPT.default (INV.top ()) sumConst in
        let difConst = OPT.default (INV.top ()) difConst in
        match i_inv, j_inv with
        | true, false ->
          let inv = INV.of_interval (lower sumConst, value) in
          set_constraint (i, Some (true, j), inv) oct
        | false, true ->
          let inv = INV.of_interval (Int64.neg value, upper sumConst) in
          set_constraint (i, Some (true, j), inv) oct
        | false, false ->
          let inv = INV.of_interval (lower difConst, value) in
          set_constraint (i, Some (false, j), inv) oct
        | true, true ->
          let inv = INV.of_interval (Int64.neg value, upper difConst) in
          set_constraint (i, Some (false, j), inv) oct
      else if (not i_inv && j_inv) || (i_inv && not j_inv)
      then matrix_set (j, j_inv) (i, i_inv) value oct
      else matrix_set (j, j_inv) (i, i_inv) (Int64.neg value) oct
    else
      let const = OPT.default (INV.top ()) (get_interval i oct) in
      if not i_inv && j_inv
      then
        let inv = INV.of_interval (Int64.neg(Int64.div value (Int64.of_int 2)), upper const) in
        set_constraint (i, None, inv) oct
      else if i_inv && not j_inv
      then
        let inv = INV.of_interval (lower const, Int64.div value (Int64.of_int 2)) in
        set_constraint (i, None, inv) oct
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

    let printf name var =
      match var with
      | Some x -> Printf.printf "%s = %Ld\n" name x
      | None -> Printf.printf "%s = None\n" name
    in

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
                    printf "old_val" old_val;
                    printf "new_val" new_val;
                    let new_val = min old_val new_val in
                    if new_val <> old_val
                    then
                      match new_val with
                      | Some new_val ->
                        matrix_set (i, i_sign) (j, j_sign) new_val oct
                      | None -> oct
                    else oct
                  ) oct signs
              else oct
            ) oct vars
        ) oct vars
    in


    (* let matrix_get a b oct = *)
    (*   let ret = matrix_get a b oct in *)
    (*   Printf.sprintf "Returning %Ld" ret |> print_endline; *)
    (*   ret *)
    (* in *)


    List.fold_left (fun oct k ->
        Printf.sprintf "k = %s" (BV.short 0 k) |> print_endline;
        let oct = List.fold_left (fun oct i ->
            List.fold_left (fun oct j ->
                if BV.compare i j <> 1
                then oct
                else
                  let () = Printf.printf "i = %s\n" (BV.short 0 i) in
                  let () = Printf.printf "j = %s\n" (BV.short 0 j) in
                  List.fold_left (fun oct (i_sign, j_sign) ->
                      let () = Printf.printf "i_sign = %B\n" i_sign in
                      let () = Printf.printf "j_sign = %B\n" j_sign in
                      let old = matrix_get (i, i_sign) (j, j_sign) oct in
                      printf "old" old;
                      let a = add (matrix_get (i, i_sign) (k, false) oct)
                          (matrix_get (k, false) (j, j_sign) oct) in
                      printf "a" a;
                      let b = add (matrix_get (i, i_sign) (k, true) oct)
                          (matrix_get (k, true) (j, j_sign) oct) in
                      printf "b" b;
                      let c = add (matrix_get (i, i_sign) (k, false) oct)
                          (add (matrix_get (k, false) (k, true) oct)
                             (matrix_get (k, true) (j, j_sign) oct)) in
                      printf "c" c;
                      let d = add (matrix_get (i, i_sign) (k, true) oct)
                          (add (matrix_get (k, true) (k, false) oct)
                             (matrix_get (k, false) (j, j_sign) oct)) in
                      printf "d" d;
                      let new_val = List.fold_left min old [a; b; c; d] in
                      printf "new" new_val;
                      if new_val <> old
                      then begin
                        let oct =
                          match new_val with
                          | Some new_val ->
                            matrix_set (i, i_sign) (j, j_sign) new_val oct
                          | None -> oct
                        in print_oct oct; oct
                      end
                      else oct
                    ) oct signs
              ) oct vars
          ) oct vars
        in
        let () = print_endline "strong_closure_s begin #####" in
        let oct = strong_closure_s oct in
        let () = print_endline "strong_closure_s begin #####" in
        oct
      ) oct vars
end

module PA = Prelude.Ana

let () =
  let min_int = INV.top () |> INV.minimal |> BatOption.get in
  let oct = MapOctagon.top () in
  let typ = PA.TInt(PA.IInt, []) in
  let a = PA.makeVarinfo false "a" typ in
  let b = PA.makeVarinfo false "b" typ in
  let oct = MapOctagon.set_constraint
      (a, None, (INV.of_interval (min_int, Int64.of_int 1))) oct in
  let oct = MapOctagon.set_constraint
      (b, None, (INV.of_interval (min_int, Int64.of_int 2))) oct in
  MapOctagon.print_oct oct;
  let oct = MapOctagon.strong_closure oct in
  MapOctagon.print_oct oct
