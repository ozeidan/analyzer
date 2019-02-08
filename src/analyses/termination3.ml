open OctagonMapDomain
open Prelude.Ana
open Analyses
module INV = IntDomain.Interval32

module Spec : Analyses.Spec =
struct
  include Analyses.DefaultSpec

  let name = "term3"
  module D = MapOctagon
  module C = MapOctagon
  module G = Lattice.Unit



  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : D.t =
    (* let lhost, _ = lval in *)
    (* (match lhost with *)
    (*  | Var info -> *)
    (*    (match rval with *)
    (*    | const(cint64 (i, _, _)) -> *)
    (*      mapoctagon.set_constraint (info, none, inv.of_int i) ctx.local *)
    (*    | _ -> ctx.local) *)
    (*  | Mem _ -> ctx.local) *)
    ctx.local

  let branch ctx (exp:exp) (tv:bool) : D.t =
    ctx.local

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
