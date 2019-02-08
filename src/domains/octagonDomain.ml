type elt = | Val of float | Infinity
[@@deriving yojson]

type sign =
    Pos | Neg

type ineq =
    Leq | Geq

let elt_to_string elt =
  match elt with
  | Infinity -> "Infinity"
  | Val f -> string_of_float f

module type S =
sig
  include Lattice.S
  val of_array : float array array -> t
  val set_constraint : t -> (sign * int) option * sign * int * ineq * elt -> int -> t
  val set_var_bounds : t -> int -> elt * elt -> int -> t
  val adjust_variable : t -> int -> int -> float -> t
  val adjust_variables : t -> int -> int -> int -> float -> t
  val projection : t -> int -> elt * elt
  val constraints : t -> string
  val to_string_matrix : t -> string
end
(* with type elt = element *)

module ArrayOctagon : S =
struct
  (* TODO: implement better narrow function *)
  include Lattice.StdCousot
  include Printable.Blank


  type t =
    | Matrix of elt array array
    | Top
    | Bot [@@deriving to_yojson]

  let of_array matrix =
    Matrix (Array.map (fun arr -> Array.map (fun elt -> Val elt) arr) matrix)

  let size oct = (Array.length oct) / 2

  let get_elt oct i j = Array.get (Array.get oct i) j
  let set_elt oct i j c = Array.set (Array.get oct i) j c

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


  let name () = "Octagon Domain"

  let leq oct1 oct2 =
    (compare oct1 oct2) = -1

  let oct_map2 fn oct1 oct2 =
    Array.map2 (fun inner1 inner2 ->
        Array.map2 (fun elt1 elt2 -> fn elt1 elt2)
          inner1 inner2)
      oct1 oct2

  let oct_mapi fn oct =
    Array.mapi (fun i inner ->
        Array.mapi (fun j elt ->
            fn i j elt) inner) oct

  let inverse_index i = i lxor 1

  let min_elt ls =
    let rec min_elt min = function
        hd :: tl -> if smaller hd min
        then min_elt hd tl
        else min_elt min tl
      | [] -> min
    in
    min_elt Infinity ls

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
    | Matrix oct1, Matrix oct2 ->
      let oct1, oct2 = strong_closure oct1, strong_closure oct2 in
      Matrix (oct_map2 max oct1 oct2)

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

  let print_octagon oct =
    Array.iter (fun a -> Array.iter (fun el -> (match el with
        | Infinity -> print_string "Inf"
        | Val el -> print_float el) ; print_string "\t") a; print_newline ()) oct


  let top_of_size size =
    Array.init (size * 2)
      (fun _ -> Array.init (size * 2)
          (fun _ -> Infinity))

  let copy_oct = function
    | Matrix oct -> Matrix (Array.copy oct)
    | a -> a

  let set_constraint oct const var_count =
    let oct = copy_oct oct in
    let oct = match oct with
      | Bot | Top -> Matrix (top_of_size var_count)
      | other -> other
    in

    let set arr i j c =
      let do_change =
        (match Array.get (Array.get arr i) j with
         | Infinity -> true
         | Val old -> old > c)
      in if do_change then
        set_elt arr i j (Val c)
      else () in

    (match const with
     (* sums are always leq *)
     | Some (sign1, v1), sign2, v2, _, Val c ->
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
     | None, sign, v, ineq, Val c ->
       (let i = v * 2 in
        match oct with
        | Matrix m ->
          let c = if ineq = Leq then c else -.c in
          if (ineq = Leq) <> (sign = Pos)
          then set m i (inverse_index i) (2.0 *. c)
          else set m (inverse_index i) i (2.0 *. c)
        | _ -> ())
     | _ -> ());
    oct

  let set_var_bounds oct i (lower, upper) var_count =
    (* TODO: don't copy twice *)
    let oct = set_constraint oct (None, Pos, i, Leq, upper) var_count in
    let oct = set_constraint oct (None, Pos, i, Geq, lower) var_count in
    let rec clear j oct =
      if j >= size oct then ()
      else if i = j then clear (j + 1) oct
      else
        let wipe i j =
          set_elt oct i j Infinity;
          set_elt oct (inverse_index i) j Infinity;
          set_elt oct i (inverse_index j) Infinity;
          set_elt oct (inverse_index i) (inverse_index j) Infinity
        in wipe i j; wipe j i; clear (j + 1) oct
    in
    match oct with
    | Matrix oct -> clear 0 oct; Matrix oct
    | _ -> Bot (* never happens *)

  let projection oct i =
    match oct with
    | Top -> (Infinity, Infinity)
    | Bot -> raise (Lattice.unsupported "constraint for variable unknown")
    | Matrix oct ->
      (let oct = strong_closure oct in
       if i < size oct then
         let lower = (get_elt oct (2 * i) (2 * i + 1)) in
         let upper = (get_elt oct (2 * i + 1) (2 * i)) in
         let fn v is_lower = match v with
           | Infinity -> Infinity
           | Val v -> Val ((if is_lower then -. 1.0 else 1.0) *. v /. 2.0)
         in
         (fn lower true, fn upper false)
       else (Val 0.0, Val 0.0))

  let adjust_variable oct vars k c =
    let adjust oct = Matrix(oct_mapi (fun i j elt ->
        match get_elt oct i j with
        | Infinity -> Infinity
        | Val old ->
          let factor =
            (if j = 2 * k then 1
             else if j = 2 * k + 1 then -1
             else 0)
            +
            (if i = 2 * k then -1
             else if i = 2 * k + 1 then 1
             else 0)
          in
          Val (old +. (float_of_int factor) *. c)
      )oct)
    in

    (match oct with
     | Top ->
       let oct = top_of_size vars in
       adjust oct
     | Matrix oct -> adjust oct
     | Bot -> Bot)

  let adjust_variables oct vars k l c =
    let adjust oct = Matrix (oct_mapi (fun i j elt ->
        if (j = 2*k && i = 2*l) || (j = 2*l+1 && i = 2*k+1) then
          Val c
        else if (j = 2*l && i = 2*k) || (j = 2*k+1 && i = 2*l+1) then
          Val (-.c)
        else Infinity) oct) in
    match oct with
    | Top ->
      let oct = top_of_size vars in
      adjust oct
    | Matrix inner ->
      adjust inner
    | Bot -> Bot

  let constraints oct =
    match oct with
    | Top -> "Top"
    | Bot -> "Bot"
    | Matrix m ->
      let rec to_string i =
        if i >= size m then ""
        else let (lower, upper) = projection oct i in
          Printf.sprintf "v%d ∈ [%s,%s]\n" i (elt_to_string lower)
            (elt_to_string upper) ^ to_string (i+1)
      in to_string 0
  let to_string_matrix oct =
    match oct with
    | Top -> "Top"
    | Bot -> "Bot"
    | Matrix m ->
      Array.fold_left
        (fun s inner -> s ^ "[" ^ (Array.fold_left (fun s elt -> s ^ (elt_to_string elt) ^ "; ") "" inner) ^ "]\n") "" m

  let isSimple _ = false
end
