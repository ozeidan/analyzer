open OctagonDomain
open Prelude.Ana
open Analyses


let variables : (int, string * int) Hashtbl.t = Hashtbl.create 0
class variableVisitor (_: fundec)= object(self)
  inherit nopCilVisitor
  method vvdec var =
    (match var.vtype with
     (* only add variables to the hashtable *)
       (* TODO: make distinction more precise *)
     | TInt _ | TFloat _ ->
       Hashtbl.add variables var.vid (var.vname, Hashtbl.length variables)
     | _ -> ());
      SkipChildren
end

module Spec : Analyses.Spec =
struct
  include Analyses.DefaultSpec

  let name = "term2"
  module D = ArrayOctagon
  module C = D
  module G = Lattice.Unit

  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : D.t =
    let host, _ = lval in
    (match host with
    | Var info ->
      (if not (Hashtbl.mem variables info.vid) then ()
      else
        let _, index = Hashtbl.find variables info.vid in
        Printf.printf "setting variable %s\n" info.vname;
        match rval with
        | Const (CInt64 (i, _, _)) -> D.set_equality ctx.local index (D.elt_of_float (Int64.to_float i)) (Hashtbl.length variables)
        | Const (CReal (f, _, _)) -> D.set_equality ctx.local index (D.elt_of_float f) (Hashtbl.length variables)
        | _ -> ()
     )
    | Mem _ -> ());
    ctx.local

  let branch ctx (exp:exp) (tv:bool) : D.t =
    let doc = Cilfacade.p_expr exp in
    print_endline "XXX";
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
