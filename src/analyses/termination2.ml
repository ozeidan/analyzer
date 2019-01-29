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
       Hashtbl.add variables var.vid (var.vname, Hashtbl.length variables)
     | _ -> ());
    SkipChildren
end

module Spec : Analyses.Spec =
struct
  include Analyses.DefaultSpec

  let name = "term2"
  module D = ArrayOctagon
  module C = ArrayOctagon
  module G = Lattice.Unit

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
    let host, _ = lval in
    (match host with
     | Var info ->
       (if not (Hashtbl.mem variables info.vid) then ()
        else
          let _, index = Hashtbl.find variables info.vid in
          let inv = evaluate_exp ctx.local rval in
          D.set_equality ctx.local index inv (Hashtbl.length variables)
       )
     | Mem _ -> ());
    ctx.local

  let branch ctx (exp:exp) (tv:bool) : D.t =
    let doc = Cilfacade.p_expr exp in
    Prelude.Ana.fprint Pervasives.stdout 80 doc;
    ctx.local

  let body ctx (f:fundec) : D.t =
    ctx.local

  let return ctx (exp:exp option) (f:fundec) : D.t =
    (* (match exp with *)
    (* | None -> () *)
    (* | Some exp -> *)
    (*   let doc = Cilfacade.p_expr exp in *)
    (*   print_endline "XXX"; *)
    (*   Prelude.Ana.fprint Pervasives.stdout 80 doc); *)
    ctx.local

  let enter ctx (lval: lval option) (f:varinfo) (args:exp list) : (D.t * D.t) list =
    [ctx.local,ctx.local]

  let combine ctx (lval:lval option) fexp (f:varinfo) (args:exp list) (au:D.t) : D.t =
    au

  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    ctx.local

  let startstate v = D.top ()
  let otherstate v = D.bot ()
  let exitstate  v = D.bot ()
end

let _ =
  Cilfacade.register_preprocess Spec.name (new variableVisitor);
  MCP.register_analysis (module Spec : Spec)
