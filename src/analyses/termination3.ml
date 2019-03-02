open OctagonMapDomain
open Prelude.Ana
open Analyses
module INV = IntDomain.Interval32
module BV = Basetype.Variables

module Spec : Analyses.Spec =
struct
  include Analyses.DefaultSpec

  let name = "octagon"
  module D = MapOctagon
  module C = MapOctagon
  module G = Lattice.Unit

  let rec evaluate_exp oct = function
    | Const (CInt64 (i, _, _)) -> INV.of_int i
    | Lval (Var var, _) -> MapOctagon.projection var oct
    | UnOp (Neg, exp, _) ->
      INV.neg (evaluate_exp oct exp)
    | BinOp (op, expl, expr, _) ->
      let operation = (match op with
          | PlusA -> INV.add
          | MinusA -> INV.sub
          | Mult -> INV.mul
          | Div -> INV.div
          | Lt -> INV.lt
          | Gt -> INV.gt
          | Le -> INV.le
          | Ge -> INV.ge
          | Eq -> INV.eq
          | Ne -> INV.ne
          | _ -> fun _ _ -> INV.top ())
      in
      operation (evaluate_exp oct expl) (evaluate_exp oct expr)
    | _ -> INV.top ()

  let assign ctx (lval:lval) (rval:exp) : D.t =
    let lhost, _ = lval in

    let oct =
      (match lhost with
       | Var lval ->
         print_string ("assigning " ^ lval.vname ^ " = ");
         let _ = Cilfacade.p_expr rval in

         print_endline "before";
         MapOctagon.print_oct ctx.local |> print_endline;
         print_endline "after";

         (match rval with
          | BinOp(PlusA, Lval(Var(var), _), Const(CInt64 (integer, _, _)), _) ->
            if (BV.compare lval var) = 0
            then MapOctagon.adjust var integer ctx.local
            else
              let oct = MapOctagon.erase lval ctx.local in
              MapOctagon.set_constraint (lval, Some(false, var), true, integer)
                (MapOctagon.set_constraint (lval, Some(false, var), false, integer) oct)
          | exp ->
            let oct = MapOctagon.erase lval ctx.local in
            let const = evaluate_exp ctx.local exp in
            if not (INV.is_top const) then
              MapOctagon.set_constraint (lval, None, true, INV.maximal const |> Option.get)
              (MapOctagon.set_constraint (lval, None, false, INV.minimal const |> Option.get)
              oct)
            else ctx.local
         )
       | Mem _ -> ctx.local)
    in
    let oct = MapOctagon.strong_closure oct in
    MapOctagon.print_oct oct |> print_endline; oct


  let branch ctx (exp:exp) (tv:bool) : D.t =
    print_string "guard with expression ";
    let _ = Cilfacade.p_expr exp in
    Printf.printf "tv = %B\n" tv;
    print_endline ("evaluates to " ^ (INV.short 0 (evaluate_exp ctx.local exp)));

    let eval = (evaluate_exp ctx.local exp) in
    let skip =
      if INV.is_bool eval
      then begin
        let eval_bool = INV.to_bool eval |> BatOption.get in
        eval_bool <> tv
      end
      else false
    in

    (* TODO: should return bot *)
    if skip
    then ctx.local
    else begin
      print_endline "before";
      MapOctagon.print_oct ctx.local |> print_endline;
      print_endline "after";

      let normalize = function
        | BinOp(Lt, l, Const(CInt64 (integer, a, b)), c) ->
          BinOp(Le, l, Const(CInt64 (Int64.sub integer Int64.one, a, b)), c)
        | BinOp(Gt, l, Const(CInt64 (integer, a, b)), c) ->
          BinOp(Ge, l, Const(CInt64 (Int64.add integer Int64.one, a, b)), c)
        | _ -> exp
      in
      let negate exp =
        match exp with
        | BinOp(Le, a, b, c) ->
          BinOp(Gt, a, b, c) |> normalize
        | BinOp(Ge, a, b, c) ->
          BinOp(Lt, a, b, c) |> normalize
        | _ -> exp
      in
      let exp = normalize exp in
      let exp = if tv then exp else negate exp in

      let oct = (match exp with
          | BinOp(cmp, lexp, Const(CInt64 (integer, _, _)), _)
            when cmp = Ge || cmp = Le ->
            (let upper = (cmp = Le) in
             match lexp with
             | BinOp(op, Lval(Var v1, _), Lval(Var v2, _), _) when op = PlusA || op = MinusA ->
               let sign = (op = PlusA) in
               MapOctagon.set_constraint (v1, Some (sign, v2), upper, integer) ctx.local
             | Lval(Var v, _) ->
               MapOctagon.set_constraint (v, None, upper, integer) ctx.local
             | _ -> ctx.local)
          | BinOp(Eq, BinOp(op, Lval(Var v1, _), Lval(Var v2, _), _),
                  Const(CInt64 (integer, _, _)), _)
            when op = PlusA || op = MinusA ->
            let sign = (op = PlusA) in
            MapOctagon.set_constraint (v1, Some(sign, v2), true, integer)
              (MapOctagon.set_constraint (v1, Some(sign, v2), false, integer) ctx.local)
          | _ -> ctx.local)
      in
      print_endline "before closure"; MapOctagon.print_oct oct |> print_endline;
      let oct = MapOctagon.meet oct ctx.local |> MapOctagon.strong_closure
      in MapOctagon.print_oct oct |> print_endline; oct
    end

  let body ctx (f:fundec) : D.t =
    ctx.local

  let return ctx (exp:exp option) (f:fundec) : D.t =
    (*   Prelude.Ana.fprint Pervasives.stdout 80 doc); *)
    ctx.local

  let enter ctx (lval: lval option) (f:varinfo) (args:exp list) : (D.t * D.t) list =
    [ctx.local,ctx.local]

  let combine ctx (lval:lval option) fexp (f:varinfo) (args:exp list) (au:D.t) : D.t =
    au

  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    ctx.local

  let startstate v = D.top ()
  let otherstate v = D.top ()
  let exitstate  v = D.top ()
end


let _ =
  (* Cilfacade.register_preprocess Spec.name (new variableVisitor); *)
  MCP.register_analysis (module Spec : Spec)
