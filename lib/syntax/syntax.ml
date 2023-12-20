type pos = Lexing.position * Lexing.position

type var = string

type binop = Plus | Minus | Mult | Div | Mod | Eq | NEq | Lt | Le | Gt | Ge | BAnd | BOr

let string_of_binop o = 
  match o with 
    | Plus -> "(+)"
    | Minus -> "(-)"
    | Mult -> "(*)"
    | Div -> "(/)"
    | Mod -> "(!)"
    | Eq -> "(=)"
    | NEq -> "(<>)"
    | Lt -> "(<)"
    | Le -> "(<=)"
    | Gt -> "(>)"
    | Ge -> "(>=)"
    | BAnd -> "(&&)" 
    | BOr -> "(||)"


type vkind = KVar | In | Out

type vtype = Integer | Boolean | Array of vtype

type 'a iexpr = { info : 'a; expr : 'a expr }
and 'a expr = 
  | ETrue
  | EFalse
  | IntCst of Z.t 
  | Var of var
  | Array of var * 'a iexpr
  | ArrayLength of var
  | Neg of 'a iexpr
  | BNot of 'a iexpr
  | Binop of 'a iexpr * binop * 'a iexpr

type 'a ilval = { info : 'a; lval : 'a lval}
and 'a lval = 
  | LValVar of var 
  | LValArray of var * 'a iexpr

type 'a iformula = { info : 'a; formula : 'a formula}
and 'a formula =
  | True
  | False
  | LVar of var
  | LIntCst of Z.t
  | LApp of string * ('a iformula) list 
  | Not of 'a iformula
  | And of 'a iformula * 'a iformula
  | Or of 'a iformula * 'a iformula
  | Impl of 'a iformula * 'a iformula
  | Forall of (var * vtype) list * 'a iformula
  | Exists of (var * vtype) list * 'a iformula

type ('a,'b) istmt = {info : pos; stmt : ('a,'b) stmt}
and ('a,'b) stmt = 
  | Skip
  | Assign of 'a ilval * 'a iexpr
  | Assert of 'b iformula
  | Seq of ('a,'b) istmt * ('a,'b) istmt
  | Ite of 'a iexpr * ('a,'b) istmt * ('a,'b) istmt option
  | While of 'a iexpr * ('b iformula) option * 'a iexpr option * ('a,'b) istmt

type state = string

type ('a,'b) transition = {
  guard : ('a iexpr) option;
  body : ('a,'b) istmt;
  target : state;
  ensures : 'b iformula;
}

type ('a,'b) behavior = {
  source : state;
  invariant : 'b iformula;
  transitions : (('a,'b) transition) list;
}


(* type environment = 
  {
    variables : (string * vtype) list;
    inputs : (string * vtype) list;
    output : (string * vtype) list
  } *)

type environment = (string * (vkind * vtype)) list

type ('a,'b) process = {
  name : string;
  states : state list;
  env : environment;
  requires : 'b iformula; 
  ensures : 'b iformula;
  behaviors : (('a,'b) behavior) list;
}

let updates (_ : ('a,'b) istmt) : var list = []
(*  match s with
  | Skip -> []
  | Assign ({lval=LValVar x;_},_) -> [ x ]
  | Assign ({lval=LValArray (_,_);_}, _) -> []
  | Assert _ -> []
  | Seq (s1, s2) -> updates s1 @ updates s2
  | Ite (_, s1, Some s2) -> updates s1 @ updates s2
  | Ite (_, s1, None) -> updates s1
  | While (_, _, _, s) -> updates s
*)

(* ****** *)

type laexpr =
  | LATrue
  | LAFalse
  | LACst of Z.t
  | LAVar of var
  | LAArray of var * (laexpr * laexpr) list * laexpr
  | LAArrayLength of var
  | LANeg of laexpr
  | LANot of laexpr
  | LABinop of  laexpr * binop * laexpr
  | LAFunction of string * laexpr list

let  laexpr_of_aexpr (_ : 'a expr) : laexpr = LATrue
 (* match e with
  | ETrue _ -> LATrue
  | EFalse _ -> LAFalse
  | IntCst (n,_) -> LACst n
  | Var (x,_) -> LAVar x
  | Array (x, e, _) -> LAArray (x, [], laexpr_of_aexpr e)
  | ArrayLength (x,_) -> LAArrayLength x
  | Neg (e,_) -> LANeg (laexpr_of_aexpr e)
  | BNot (e,_) -> LANot (laexpr_of_aexpr e)
  | Binop (e1, o,e2,_) -> LABinop (laexpr_of_aexpr e1, o, laexpr_of_aexpr e2)
 *)
let formula_of_bexpr (_ : 'a expr) : 'a formula = True
(*  match e with
  | ETrue _ -> True
  | EFalse _ -> False
  | Var (x,_) -> LVar x
  | Binop (e1, BAnd, e2,_) -> And (formula_of_bexpr e1, formula_of_bexpr e2)
  | Binop (e1, BOr, e2,_) -> Or (formula_of_bexpr e1, formula_of_bexpr e2)
  | BNot (b,_) -> Not (formula_of_bexpr b)
  | _ -> failwith "not a boolean expression"*)

(* let basic expressions instead of laexpression (arrays) *)
(* do it when building formulas *)
(* doesn't occur in syntax *)

(* assign array -> assign *)
(* more generally, left value *)
(* Ajouter définition de méthodes + paramètres dans les processus *)
