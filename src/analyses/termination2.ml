open OctagonDomain
open Prelude.Ana
open Analyses


let variables : (int, string * int) Hashtbl.t = Hashtbl.create 0
class variableVisitor (_: fundec)= object(self)
  inherit nopCilVisitor
  method vvdec var =
    (match var.vtype with
     (* only add variables to the hashtable *)
     | TInt _ ->
       (* print_endline (Printf.sprintf "storing variable %s" var.vname); *)
       Hashtbl.add variables var.vid (var.vname, Hashtbl.length variables)
     | _ -> ());
    SkipChildren
end
let size = ref 0

module Spec : Analyses.Spec =
struct
  include Analyses.DefaultSpec

  let name = "term2"
  module D = ArrayOctagon
  module C = ArrayOctagon
  module G = Lattice.Unit

  let init () = size := Hashtbl.length variables

  let negate_elt = function
    | Infinity -> Infinity
    | Val f -> Val (-. f)

  let join_inv op (l1, u1) (l2, u2) =
    let join_elts a b =
      match a, b with
      | Infinity, _ | _, Infinity -> Infinity
      | Val a, Val b -> Val (op a b)
    in
    (join_elts l1 l2, join_elts u1 u2)

  let add_inv a b = join_inv (+.) a b
  let sub_inv a b = join_inv (-.) a b

  let const_to_float = function
    | CInt64 (i, _, _) -> Some (Int64.to_float i)
    | CReal (f, _, _) -> Some f
    | _ -> None

  let rec evaluate_exp oct = function
    | Const (CInt64 (i, _, _)) -> (Val (Int64.to_float i), Val (Int64.to_float i))
    | Const (CReal (f, _, _)) -> (Val f, Val f)
    | Lval (Var var, _) ->
      if not (Hashtbl.mem variables var.vid) then
        (Infinity, Infinity)
      else
        let _, index = Hashtbl.find variables var.vid in
        D.projection oct index
    | UnOp (Neg, exp, _) ->
      let (lower, upper) = evaluate_exp oct exp in
      (negate_elt upper, negate_elt lower)
    | BinOp (op, expl, expr, _) ->
      (let a, b = evaluate_exp oct expl, evaluate_exp oct expr in
       match op with
       | PlusA -> add_inv a b
       | MinusA -> sub_inv a b
       | _ -> (Infinity, Infinity))
    | _ -> (Infinity, Infinity)


  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : D.t =
    (* print_oct ctx.local |> print_endline; *)
    (* print_endline "after"; *)
    let var_amount = Hashtbl.length variables in
    let host, _ = lval in
    (match host with
     | Var lval ->
       print_string ("assigning " ^ lval.vname ^ " = ");
       let _ = Cilfacade.p_expr rval in

       print_endline "before";
       print_endline (D.to_string_matrix ctx.local);
       let oct =
         (if not (Hashtbl.mem variables lval.vid) then ctx.local
          else
            let _, index = Hashtbl.find variables lval.vid in
              begin match rval with
                | BinOp (op, (Lval(Var v, _)), Const c, _)
                | BinOp (op, Const c, (Lval(Var v, _)), _) ->
                  (match const_to_float c with
                   | None -> ctx.local
                   | Some c ->
                     let c = if op = PlusA then c else -.c in
                     if v.vid = lval.vid then
                       D.adjust_variable ctx.local (Hashtbl.length variables) index c
                     else if not (Hashtbl.mem variables v.vid) then ctx.local
                     else
                       let _, right_index = Hashtbl.find variables v.vid in
                       D.adjust_variables ctx.local (Hashtbl.length variables) index right_index c)
                | Lval (Var v, _) ->
                  if v.vid <> lval.vid then
                    let _, index2 = Hashtbl.find variables v.vid in
                    let temp = D.set_constraint ctx.local (Some (true, index2), true, index, true, (Val 0.0)) var_amount in
                    D.set_constraint temp (Some (false, index2), false, index, true, (Val 0.0)) var_amount
                  else ctx.local
                | exp ->
                  print_endline "evaluating expr";
                  if M.tracing then M.tracel "oct" "Exp: %a\n" d_plainexp rval;
                  let (lower, upper) = evaluate_exp ctx.local exp in
                  (* print_endline (Printf.sprintf "to boundaries [%s, %s]" (elt_to_string lower) (elt_to_string upper)); *)
                  D.set_var_bounds ctx.local index (lower, upper) (Hashtbl.length variables)
              end
         )
       in oct
     | Mem _ -> ctx.local)

  let branch ctx (exp:exp) (tv:bool) : D.t =
    print_endline "before";
    D.to_string_matrix ctx.local |> print_endline;
    print_string "guard with expression ";
    let _ = Cilfacade.p_expr exp in
    Printf.printf "tv = %B\n" tv;

    let oct = begin
      match exp with
      | BinOp (binop, Lval (Var v, _), Const (CInt64 (i, _, _)), _) ->
        if not (Hashtbl.mem variables v.vid) then ctx.local
        else let i = match binop with
            | Lt -> Int64.sub i Int64.one
            | Gt -> Int64.add i Int64.one
            | _ -> i
          in
          let ineq = match binop with
            | Lt | Le -> true
            | Gt | Ge -> false
            | _ -> true (* TODO *)
          in
          let (_, index) = Hashtbl.find variables v.vid in
          D.set_constraint ctx.local
            (None, true, index, ineq, Val (Int64.to_float i))
            (Hashtbl.length variables)
      | _ -> ctx.local
    end
    in D.strong_closure oct

  let body ctx (f:fundec) : D.t =
    ctx.local

  let return ctx (exp:exp option) (f:fundec) : D.t =
    ctx.local

  let enter ctx (lval: lval option) (f:varinfo) (args:exp list) : (D.t * D.t) list =
    [ctx.local,ctx.local]

  let combine ctx (lval:lval option) fexp (f:varinfo) (args:exp list) (au:D.t) : D.t =
    au

  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    ctx.local

  let startstate v = D.top_of_size !size
  let otherstate v = D.top_of_size !size
  let exitstate  v = D.top_of_size !size
end


let _ =
  Cilfacade.register_preprocess Spec.name (new variableVisitor);
  MCP.register_analysis (module Spec : Spec)
