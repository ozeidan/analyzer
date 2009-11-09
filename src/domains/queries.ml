include Cil
include Pretty 

module ID = IntDomain.FlatPureIntegers
module LS = SetDomain.ToppedSet (Lval.CilLval) (struct let topname = "All" end)
module PS = SetDomain.ToppedSet (Exp.LockingPattern) (struct let topname = "All" end)

module ES_r = SetDomain.ToppedSet (Exp.Exp) (struct let topname = "All" end)
module ES = 
struct 
  include ES_r
  include Lattice.StdCousot 
  let bot = ES_r.top
  let top = ES_r.bot
  let leq x y = ES_r.leq y x
  let join = ES_r.meet
  let meet = ES_r.join
end

type t = ExpEq of exp * exp 
       | EqualSet of exp
       | MayPointTo of exp
       | ReachableFrom of exp
       | PerElementLock of exp
       | Regions of exp  
       | SingleThreaded       (* result is "boolean" in `Int form *)
       | CurrentThreadId      (* currently "main" -> `Int 1; "other" -> `Top *)
       | TheAnswerToLifeUniverseAndEverything

type result = [
    | `Top
    | `Int of ID.t
    | `LvalSet of LS.t
    | `ExprSet of ES.t
    | `PerElemLock of PS.t
    | `Bot
    ] 
      
module Result: Lattice.S with type t = result = 
struct 
  type t = result

  let name () = "query result domain"

  let bot () = `Bot
  let is_bot x = x = `Bot
  let bot_name = "Bottom"
  let top () = `Top
  let is_top x = x = `Top
  let top_name = "Unknown"

  let equal x y = 
    match (x, y) with
      | (`Top, `Top) -> true
      | (`Bot, `Bot) -> true
      | (`Int x, `Int y) -> ID.equal x y
      | (`LvalSet x, `LvalSet y) -> LS.equal x y
      | (`ExprSet x, `ExprSet y) -> ES.equal x y
      | (`PerElemLock x, `PerElemLock y) -> PS.equal x y
      | _ -> false

  let hash (x:t) =
    match x with
      | `Int n -> ID.hash n
      | `LvalSet n -> LS.hash n
      | `ExprSet n -> ES.hash n
      | `PerElemLock n -> PS.hash n
      | _ -> Hashtbl.hash x

  let compare x y = 
    let constr_to_int x = match x with
        | `Bot -> 0
        | `Int _ -> 1
        | `LvalSet _ -> 3
        | `ExprSet _ -> 4
        | `PerElemLock _ -> 5
        | `Top -> 100
    in match x,y with
      | `Int x, `Int y -> ID.compare x y
      | `LvalSet x, `LvalSet y -> LS.compare x y
      | `ExprSet x, `ExprSet y -> ES.compare x y
      | `PerElemLock x, `PerElemLock y -> PS.compare x y
      | _ -> Pervasives.compare (constr_to_int x) (constr_to_int y)

  let pretty_f s () state = 
    match state with
      | `Int n ->  ID.pretty () n
      | `LvalSet n ->  LS.pretty () n
      | `ExprSet n ->  ES.pretty () n
      | `PerElemLock n ->  PS.pretty () n
      | `Bot -> text bot_name
      | `Top -> text top_name

  let rec short w state = 
    match state with
      | `Int n ->  ID.short w n
      | `LvalSet n ->  LS.short w n
      | `ExprSet n ->  ES.short w n
      | `PerElemLock n ->  PS.short w n
      | `Bot -> bot_name
      | `Top -> top_name

  let isSimple x = 
    match x with
      | `Int n ->  ID.isSimple n
      | `LvalSet n ->  LS.isSimple n
      | `ExprSet n ->  ES.isSimple n
      | `PerElemLock n ->  PS.isSimple n
      | _ -> true

  let toXML_f sf state =
    match state with
      | `Int n -> ID.toXML n
      | `LvalSet n -> LS.toXML n
      | `ExprSet n -> ES.toXML n
      | `PerElemLock n -> PS.toXML n
      | `Bot -> Xml.Element ("Leaf", ["text",bot_name], [])
      | `Top -> Xml.Element ("Leaf", ["text",top_name], [])

  let pretty () x = pretty_f short () x
  let toXML s = toXML_f short s

  let leq x y =
    match (x,y) with
      | (_, `Top) -> true
      | (`Top, _) -> false
      | (`Bot, _) -> true
      | (_, `Bot) -> false
      | (`Int x, `Int y) -> ID.leq x y
      | (`LvalSet x, `LvalSet y) -> LS.leq x y
      | (`ExprSet x, `ExprSet y) -> ES.leq x y
      | (`PerElemLock x, `PerElemLock y) -> PS.leq x y
      | _ -> false

  let join x y = 
    try match (x,y) with 
      | (`Top, _) 
      | (_, `Top) -> `Top
      | (`Bot, x) 
      | (x, `Bot) -> x
      | (`Int x, `Int y) -> `Int (ID.join x y)
      | (`LvalSet x, `LvalSet y) -> `LvalSet (LS.join x y)
      | (`ExprSet x, `ExprSet y) -> `ExprSet (ES.join x y)
      | (`PerElemLock x, `PerElemLock y) -> `PerElemLock (PS.join x y)
      | _ -> `Top
    with IntDomain.Unknown -> `Top

  let meet x y = 
    try match (x,y) with 
      | (`Bot, _) 
      | (_, `Bot) -> `Bot
      | (`Top, x) 
      | (x, `Top) -> x
      | (`Int x, `Int y) -> `Int (ID.meet x y)
      | (`LvalSet x, `LvalSet y) -> `LvalSet (LS.meet x y)
      | (`ExprSet x, `ExprSet y) -> `ExprSet (ES.meet x y)
      | (`PerElemLock x, `PerElemLock y) -> `PerElemLock (PS.meet x y)
      | _ -> `Bot
    with IntDomain.Error -> `Bot

  let widen x y =
    try match (x,y) with 
      | (`Top, _) 
      | (_, `Top) -> `Top
      | (`Bot, x) 
      | (x, `Bot) -> x
      | (`Int x, `Int y) -> `Int (ID.widen x y)
      | (`LvalSet x, `LvalSet y) -> `LvalSet (LS.widen x y)
      | (`ExprSet x, `ExprSet y) -> `ExprSet (ES.widen x y)
      | (`PerElemLock x, `PerElemLock y) -> `PerElemLock (PS.widen x y)
      | _ -> `Top    
    with IntDomain.Unknown -> `Top
  
  let narrow x y =
    match (x,y) with 
      | (`Int x, `Int y) -> `Int (ID.narrow x y)
      | (`LvalSet x, `LvalSet y) -> `LvalSet (LS.narrow x y)
      | (`ExprSet x, `ExprSet y) -> `ExprSet (ES.narrow x y)
      | (`PerElemLock x, `PerElemLock y) -> `PerElemLock (PS.narrow x y)
      | (x,_) -> x
end