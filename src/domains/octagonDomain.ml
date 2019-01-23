module type S =
sig
  include Lattice.S
  type elt
  type sign
  type ineq
  val of_array : float array array -> t
  val set_constraint : t -> (sign * int) option * sign * int * ineq * elt -> int -> unit
  val set_equality : t -> int -> elt -> int -> unit
  val elt_of_float : float -> elt
end


module ArrayOctagon : S =
struct
  (* TODO: implement better narrow function *)
  include Lattice.StdCousot
  include Printable.Blank

  type elt =
    | Val of float
    | Infinity [@name "Inf"]
  [@@deriving yojson]

  let elt_of_float x = Val x

  type t =
    | Matrix of elt array array
    | Top
    | Bot [@@deriving to_yojson]

  type sign =
      Pos | Neg

  type ineq =
      LEq | GEq

  let of_array matrix =
    Matrix (Array.map (fun arr -> Array.map (fun elt -> Val elt) arr) matrix)

  let size oct = (Array.length oct) / 2

  let get_elt oct x y = Array.get (Array.get oct x) y

  let add a b =
    match a, b with
    | Infinity , _ | _ , Infinity -> Infinity
    | Val a, Val b -> Val (a +. b)

  let smaller a b =
    match a, b with
    | Infinity , _ -> false
    | _ , Infinity -> true
    | Val a, Val b -> a < b

  let elt_leq a b =
    match a, b with
    | Infinity , _ -> false
    | _ , Infinity -> true
    | Val a, Val b -> a <= b


  let oct_find2 filter oct1 oct2 =
    if size oct1 <> size oct2
    then raise Lattice.Uncomparable
    else
      let oct_size = Array.length oct1 in
      let rec find i j =
        if i >= oct_size then None else
          let first = get_elt oct1 i j in
          let second = get_elt oct2 i j in
          if filter first second
          then
            Some (first, second)
          else
            let j = j + 1 in
            if j >= oct_size then
              find (i + 1) 0
            else
              find i j
      in
      find 0 0

  (* simple matrix comparison *)
  let equal oct1 oct2 =
    match oct1, oct2 with
    | Matrix oct1, Matrix oct2 ->
      (match oct_find2 (fun a b -> a != b) oct1 oct2 with
       | Some _ -> false
       | None -> true)
    | _ , _ -> oct1 == oct2

  let hash oct = 2

  let compare oct1 oct2 =
    match oct1, oct2 with
    | Matrix oct1, Matrix oct2 ->
      (* Todo: could be more efficient *)
      (match oct_find2 (fun a b -> a < b) oct1 oct2,
             oct_find2 (fun a b -> a > b) oct1 oct2 with
      | None, None
      | Some _, Some _ -> 0
      | None, Some _ -> 1
      | Some _, None -> -1)
    | Bot, Bot | Top, Top -> 0
    | Bot, _ -> -1
    | _, Bot -> 1
    | Top, _ -> 1
    | _, Top -> -1


  let name () = Printf.sprintf "Octagon Domain"

  let leq oct1 oct2 =
    (compare oct1 oct2) = -1

  let oct_map2 fn oct1 oct2 =
    Array.map2 (fun inner1 inner2 ->
        Array.map2 (fun elt1 elt2 -> fn elt1 elt2)
          inner1 inner2)
      oct1 oct2

  let min a b =
    match a, b with
    | Infinity , _ -> b
    | _ , Infinity -> a
    | Val a, Val b -> Val (min a b)

  let max a b =
    match a, b with
    | Infinity , _ -> a
    | _ , Infinity -> b
    | Val a, Val b -> Val (max a b)

  let join oct1 oct2 =
    match oct1, oct2 with
    | Bot, other | other, Bot -> other
    | Top, _ | _, Top -> Top
    | Matrix oct1, Matrix oct2 -> Matrix (oct_map2 max oct1 oct2)

  let meet oct1 oct2 =
    match oct1, oct2 with
    | Bot, _ | _, Bot -> Bot
    | Top, other | other, Top -> other
    | Matrix oct1, Matrix oct2 -> Matrix (oct_map2 min oct1 oct2)

  let widen oct1 oct2 =
    match oct1, oct2 with
    (* TODO: is this case correct? *)
    | Bot, other | other, Bot -> other
    | Top, _ | _, Top -> Top
    | Matrix oct1, Matrix oct2 ->
      Matrix (oct_map2 (fun a b -> if elt_leq b a then a else Infinity) oct1 oct2)


  let bot () = Bot

  let is_bot = function
      Bot -> true
    | _ -> false


  let top () = Top

  let is_top = function
      Top -> true
    | _ -> false

  let inverse_index i = i lxor 1

  let min_elt ls =
    let rec min_elt min = function
        hd :: tl -> if smaller hd min
        then min_elt hd tl
        else min_elt min tl
      | [] -> min
    in
    min_elt Infinity ls

  let print_octagon oct =
    Array.iter (fun a -> Array.iter (fun el -> (match el with
        | Infinity -> print_string "Inf"
        | Val el -> print_float el) ; print_string "\t") a; print_newline ()) oct

  let strong_closure oct =
    (* S+ matrix of the octagon paper *)
    let s oct =
      Array.mapi (fun i inner ->
          Array.mapi (fun j elt ->
              let first = Array.get inner (inverse_index i) in
              let second = get_elt oct (inverse_index j) j in
              let secondval = match first, second with | Val f, Val s -> Val ((f +. s) /. 2.0)
                                                       | _ -> Infinity in
              min_elt [elt ; secondval]
            ) inner) oct
    in

    let c oct k =
      (* C+ matrix of the octagon paper *)
      Array.mapi (fun i inner ->
          Array.mapi (fun j elt ->
              if i == j then Val 0.0 else
                min_elt
                  [elt;
                   (add (get_elt oct i k) (get_elt oct k j));
                   (add (get_elt oct i (inverse_index k)) (get_elt oct (inverse_index k) j));
                   (add (add (get_elt oct i k) (get_elt oct k (inverse_index k))) (get_elt oct (inverse_index k) j));
                   (add (add (get_elt oct i (inverse_index k)) (get_elt oct (inverse_index k) k)) (get_elt oct k j))]
            ) inner ) oct
    in

    let rec strong_closure' oct k =
      let oct_size = size oct in
      if k <= oct_size / 2 then
        strong_closure' (s (c oct (2 * (k - 1)))) (k + 1)
      else
        oct
    in
    strong_closure' oct 1

  let top_of_size size =
    Matrix (Array.init (size * 2)
              (fun _ -> Array.init (size * 2)
                  (fun _ -> Infinity)))


  let set_constraint oct const var_count =
    let oct = match oct with
      | Bot | Top -> top_of_size var_count
      | other -> other
    in

    let set arr i j c = Array.set (Array.get arr i) j c in

    match const with
    (* sums are always leq *)
    | Some (sign1, v1), sign2, v2, _, c ->
      (let i = v1 * 2 in
       let j = v2 * 2 in
       let i1, j1, i2, j2 =
         (match sign1, sign2 with
          | Pos, Neg -> i, j, inverse_index j, inverse_index i
          | Neg, Pos -> j, i, inverse_index i, inverse_index j
          | Pos, Pos -> i, inverse_index j, j, inverse_index i
          | Neg, Neg -> inverse_index j, i, inverse_index i, j)
       in
       match oct with
       | Matrix m -> set m i1 j1 c; set m i2 j2 c
       | _ -> ())
    | None, sign, v, ineq, c ->
      let i = v * 2 in
      match oct with
      | Matrix m ->
        if (ineq == LEq) <> (sign == Pos)
        then set m i (inverse_index i) c
        else set m (inverse_index i) i c
      (* match ineq with *)
      (* | LEq -> *)
      (* | GEq -> *)
      | _ -> ()

  let set_equality oct i c var_count =
    (match c with | Val c -> Printf.printf "setting value %f\n" c | _ -> ());
    set_constraint oct (None, Pos, i, LEq, c) var_count;
    set_constraint oct (None, Pos, i, GEq, c) var_count




  let get_constraints oct =
    let elt_to_string lower = function
      | Infinity -> "∞"
      | Val elt -> string_of_float ((if lower then -1.0 else 1.0)  *. (elt /. 2.0))
    in

    let rec get_constraints i oct =
      let oct_size = size oct in
      if i < oct_size / 2 then
        let lower = elt_to_string true (get_elt oct (2 * i) (2 * i + 1)) in
        let upper = elt_to_string false (get_elt oct (2 * i + 1) (2 * i)) in
        (Printf.sprintf "v%d ∈ [%s , %s]\n" i lower upper) ^ get_constraints (i + 1) oct
      else
        ""
    in
    get_constraints 0 oct
end

(*   let a = Test3.of_array *)
(*   let b = Test3.of_array [|[|2.0; 2.0; 2.0|]; [|2.0; 2.0; 2.0|]; [|2.0; 2.0; 2.0|]|] in *)
(*   let json = Test3.to_yojson a in *)
(*   let json2 = Test3.to_yojson b in *)

(*   Yojson.Safe.to_string json |> print_endline; *)
(*   Yojson.Safe.to_string json2 |> print_endline; *)

(*   print_newline (); *)
(*   print_newline (); *)

(*   Test3.meet a b |> Test3.to_yojson |> Yojson.Safe.to_string |> print_endline; *)
(*   Test3.join a b |> Test3.to_yojson |> Yojson.Safe.to_string |> print_endline; *)
(*   Test3.widen a b |> Test3.to_yojson |> Yojson.Safe.to_string |> print_endline; *)
(*   Test3.compare a b |> string_of_int |> print_endline; *)

(*   print_string "hello"; *)
(*   print_newline (); *)
(*   print_newline (); *)
(*   print_newline (); *)
(*   print_newline () *)
