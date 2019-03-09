open Analyses
open Prelude.Ana
open OctagonMapDomain
module INV = IntDomain.Interval32
module BV = Basetype.Variables

module Spec : Analyses.Spec =
struct
  include Analyses.DefaultSpec

  let name = "octagon"
  module D = MapOctagonBot
  module C = D
  module G = Lattice.Unit

  let print_oct oct =
    Prelude.Ana.sprint D.pretty oct

  let evaluate_sums oct exp =
    let match_exp = function
      | BinOp(Mult, Lval(Var(var), _), Const(CInt64 (c, _, _)), _)
      | BinOp(Mult, Const(CInt64 (c, _, _)), Lval(Var(var), _), _) ->
        Some (c, var)
      | Lval(Var(var), _) ->
        Some (Int64.one, var)
      | _ -> None
    in

    let inv_length inv =
      match INV.minimal inv, INV.maximal inv with
      | None, _ | _, None ->
        None
      | Some a, Some b ->
        Some (Int64.sub b a)
    in

    let min inv1 inv2 =
      match inv_length inv1, inv_length inv2 with
      (* can't happen *)
      | None, None -> inv1
      | Some _, None -> inv1
      | None, Some _ -> inv2
      | Some l, Some r ->
        if Int64.compare l r = 1
        then inv2
        else inv1
    in

    match exp with
    | BinOp(op, expl, expr, _) when op = PlusA || op = MinusA ->
      begin match match_exp expl, match_exp expr with
      | None, _ | _, None -> None
      | Some(cl, varl), Some(cr, varr) ->
        let cr = if op = PlusA then cr else Int64.neg cr in
        let cl, cr = INV.of_int cl, INV.of_int cr in
        let varSum = D.projection varl (Some (true, varr)) oct in
        let varDif1 = D.projection varl (Some (false, varr)) oct in
        let varDif2 = D.projection varr (Some (false, varl)) oct in
        let varl = D.projection varl None oct in
        let varr = D.projection varr None oct in
        let candidates = [
          INV.add (INV.mul cl varl) (INV.mul cr varr);
          INV.add (INV.mul cl varSum) (INV.mul (INV.sub cr cl) varr);
          INV.add (INV.mul cr varSum) (INV.mul (INV.sub cl cr) varl);
          INV.add (INV.mul cl varDif1) (INV.mul (INV.add cl cr) varr);
          INV.add (INV.mul cr varDif2) (INV.mul (INV.add cl cr) varl);
        ] in
        List.iter
          (fun inv -> INV.short 0 inv |> print_endline)
          candidates;
        let return = (List.fold_left min (INV.top ()) candidates) in
        let () = print_endline ("returning interval: " ^ INV.short 0 return) in
        Some return end
    | _ -> None

  let rec evaluate_exp oct exp =
    match evaluate_sums oct exp with
    | Some inv -> inv
    | None ->
      begin
        match exp with
        | Const (CInt64 (i, _, _)) -> INV.of_int i
        | Lval (Var var, _) -> D.projection var None oct
        | UnOp (Neg, exp, _) ->
          INV.neg (evaluate_exp oct exp)
        | BinOp (op, expl, expr, _) ->
          let op = (match op with
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
          op (evaluate_exp oct expl) (evaluate_exp oct expr)
        | _ -> INV.top ()
      end


  let assign ctx (lval:lval) (rval:exp) : D.t =
    let lhost, _ = lval in
    let oct =
      (match lhost with
       | Var lval ->
         print_string ("assigning " ^ lval.vname ^ " = ");
         let _ = Cilfacade.p_expr rval in

         print_endline "before";
         print_oct ctx.local |> print_endline;
         print_endline "after";

         (match rval with
          | BinOp(PlusA, Lval(Var(var), _), Const(CInt64 (integer, _, _)), _) ->
            if (BV.compare lval var) = 0
            then D.adjust var integer ctx.local
            else
              let oct = D.erase lval ctx.local in
              D.set_constraint (lval, Some(false, var), true, integer)
                (D.set_constraint (lval, Some(false, var), false, integer) oct)
          | exp ->
            let const = evaluate_exp ctx.local exp in
            let () = print_endline ("evaluated to " ^ INV.short 0 const) in
            let oct = D.erase lval ctx.local in
            if not (INV.is_top const) then
              D.set_constraint (lval, None, true, INV.maximal const |> Option.get)
                (D.set_constraint (lval, None, false, INV.minimal const |> Option.get)
                   oct)
            else ctx.local
         )
       | Mem _ -> ctx.local)
    in
    let oct = D.strong_closure oct in
    print_oct oct |> print_endline; oct


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
    print_endline "before";
    print_oct ctx.local |> print_endline;

    if skip
    then raise Deadcode
    else begin
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
               D.set_constraint (v1, Some (sign, v2), upper, integer) ctx.local
             | Lval(Var v, _) ->
               D.set_constraint (v, None, upper, integer) ctx.local
             | _ -> ctx.local)
          | BinOp(Eq, BinOp(op, Lval(Var v1, _), Lval(Var v2, _), _),
                  Const(CInt64 (integer, _, _)), _)
            when op = PlusA || op = MinusA ->
            let sign = (op = PlusA) in
            D.set_constraint (v1, Some(sign, v2), true, integer)
              (D.set_constraint (v1, Some(sign, v2), false, integer) ctx.local)
          | _ -> ctx.local)
      in
      print_endline "before closure"; print_oct oct |> print_endline;
      let oct = D.meet oct ctx.local |> D.strong_closure
      in print_oct oct |> print_endline; oct
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
