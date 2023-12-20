open Syntax
open TypedSyntax
(* open Why3.Term
   open Why3.Ident
   open Why3.Ty *)
(* open Format  *)

open VerproMonad.Monad
open VerproMonad.MonadOption
open MonadSyntax (M)

type why3_type = 
  | Why3Unit
  | Why3Int 
  | Why3Bool 
  | Why3Ref of why3_type
  | Why3Array of why3_type

type why3_formula = 
  | WFTrue 
  | WFFalse 
  | WFVar of string 
  | WFNot of why3_formula 
  | WFAnd of why3_formula * why3_formula 
  | WFOr of why3_formula * why3_formula 
  | WFForall of (var * why3_type) list * why3_formula 
  | WFExists of (var * why3_type) list * why3_formula
  
type why3_term = 
  | WUnit
  | WTrue 
  | WFalse 
  | WInt of Z.t
  | WVar of string 
  | WNeg of why3_term 
  | WNot of why3_term
  | WBinop of why3_term * binop * why3_term 
  | WArray of string * why3_term
  | WAssert of why3_formula
  | WArrayLength of string
  | WAssign of why3_lval *  why3_term
  | WSeq of why3_term *  why3_term
  | WIte of why3_term * why3_term *  why3_term option 
  | WWhile of why3_term  * why3_formula option * why3_term option *  why3_term
and why3_lval = WLVar of string | WLArray of string * why3_term


type why3_function = 
  {
    fun_id : string;
    fun_params : (string * why3_type) list;
    fun_requires : why3_formula;
    fun_ensures : why3_formula;
    fun_body :  why3_term
  }

let rec translate_type (t : vtype) : why3_type = 
  match t with 
  | Integer -> Why3Ref Why3Int
  | Boolean -> Why3Ref Why3Bool 
  | Array vt -> Why3Array (translate_type vt)

let rec translate_expression (e : 'a iexpr) :  why3_term = 
  let e = e.expr in
  match e with  
  | ETrue -> WTrue
  | EFalse -> WFalse 
  | IntCst c -> WInt c
  | Var x -> WVar x
  | Array (x,e) -> WArray (x, translate_expression e)
  | ArrayLength x -> WArrayLength x
  | Neg e -> WNeg (translate_expression e)
  | BNot e -> WNeg (translate_expression e)
  | Binop (e1,o,e2) -> 
      WBinop(translate_expression e1, o, translate_expression e2)

(* 
| LValVar of var 
  | LValArray of var * 'a iexpr
   *)

let translate_lval (lv : 'a ilval) : why3_lval = 
  let lv = lv.lval in
  match lv with 
    | LValVar x -> WLVar x 
    | LValArray (x,e) -> WLArray (x, translate_expression e) 

let translate_formula (_f : 'b iformula) : why3_formula = WFTrue

let rec translate_statement (s : ('a,'b) istmt) :  why3_term = 
  let s = s.stmt in
    match s with 
    | Skip -> WUnit
    | Assign(lv,e) ->
        WAssign (translate_lval lv, translate_expression e)
    | Assert f -> WAssert (translate_formula f)
    | Seq (s1, s2) -> WSeq (translate_statement s1, translate_statement s2)
    | Ite (e, s1, s2) -> 
      WIte (translate_expression e, translate_statement s1, 
        M.fmap translate_statement s2)
    | While (e, f, e0, s) ->
        WWhile (translate_expression e, 
          M.fmap translate_formula f, M.fmap translate_expression e0, 
          translate_statement s)

let formula_of_expr (_e :'a iexpr) : why3_formula = 
    WFTrue
  
exception No_Such_State of string

let get_state_invariant (p : ('a, 'b) process) (s : state) : 'b iformula =
    try (List.find (fun t -> t.source = s) p.behaviors).invariant
    with _ -> raise (No_Such_State s)

let translate_transition (p : ('a,'b) process) (src : state) (t : ('a,'b) transition) :  why3_function = 
  let name = src^"_"^t.target in
  let inv_src  = translate_formula (get_state_invariant p src) in 
  let inv_tgt = translate_formula (get_state_invariant p t.target) in
  {
        fun_id = name ;
        fun_params = 
          List.map (fun (x,(_,z)) -> (x, translate_type z)) p.env;
        fun_requires = 
        begin
          let f = M.fmap (fun x -> WFAnd (formula_of_expr x, inv_src)) t.guard in
          match f with None -> inv_src | Some f -> WFAnd (f, inv_src) 
        end;
        fun_ensures = WFAnd (translate_formula t.ensures, inv_tgt);
        fun_body = translate_statement t.body
      }

let translate_behavior (p :('a, 'b) process)  (b : ('a, 'b) behavior) : why3_function list= 
  List.map (translate_transition p b.source) b.transitions

let translate_process (p : ('a,'b) process) : why3_function list = 
  List.flatten (List.map (translate_behavior p) p.behaviors)

  type ('a,'b) behavior = {
    source : state;
    invariant : 'b iformula;
    transitions : (('a,'b) transition) list;
  }




let rec pp_type out t =
  match t with
  | Boolean -> Format.pp_print_string out "bool"
  | Integer -> Format.pp_print_string out "int"
  | Array t -> Format.fprintf out "(%a) array" pp_type t



let comma out () = Format.fprintf out "; "
let pp_semi out (x, vt) = Format.fprintf out "%s : %a" x pp_type vt

let rec pp_formula out (f : info_node iformula) =
  let _pos = f.info and f = f.formula in
  match f with
  | True -> Format.pp_print_string out "true"
  | False -> Format.pp_print_string out "false"
  | LVar x -> Format.pp_print_string out x
  | LIntCst z -> Format.pp_print_string out (Z.to_string z)
  | LApp (f, l) ->
      Format.fprintf out "%s(%a)" f
        (Format.pp_print_list ~pp_sep:comma pp_formula)
        l
  | Not f -> Format.fprintf out "not (%a)" pp_formula f
  | And (f1, f2) -> Format.fprintf out "%a /\\ %a" pp_formula f1 pp_formula f2
  | Or (f1, f2) -> Format.fprintf out "%a \\/ %a" pp_formula f1 pp_formula f2
  | Impl (f1, f2) -> Format.fprintf out "%a -> %a" pp_formula f1 pp_formula f2
  | Forall (l, f) ->
      Format.fprintf out "forall %a.%a"
        (Format.pp_print_list ~pp_sep:comma pp_semi)
        l pp_formula f
  | Exists (l, f) ->
      Format.fprintf out "exists %a.%a"
        (Format.pp_print_list ~pp_sep:comma pp_semi)
        l pp_formula f

let rec pp_expression out (e : info_node iexpr) =
  let _pos = e.info and e = e.expr in
  match e with
  | ETrue -> Format.pp_print_string out "true"
  | EFalse -> Format.pp_print_string out "false"
  | IntCst z -> Format.pp_print_string out (Z.to_string z)
  | Var x -> Format.pp_print_string out x
  | Array (x, e) -> Format.fprintf out "%s[%a]" x pp_expression e
  | ArrayLength x -> Format.fprintf out "%s.length" x
  | Neg e -> Format.fprintf out "-%a" pp_expression e
  | BNot e -> Format.fprintf out "not %a" pp_expression e
  | Binop (e1, op, e2) ->
      Format.fprintf out "%a %s %a" pp_expression e1 (string_of_binop op)
        pp_expression e2
(*
   | Skip
   | Assign of 'a ilval * 'a iexpr
   | Assert of 'b iformula
   | Seq of ('a,'b) istmt * ('a,'b) istmt
   | Ite of 'a iexpr * ('a,'b) istmt * ('a,'b) istmt option
   | While of 'a iexpr * ('b iformula) option * 'a iexpr option * ('a,'b) istmt *)
(*
     type 'a ilval = { info : 'a; lval : 'a lval}
     and 'a lval =
       | LValVar of var
       | LValArray of var * 'a iexpr *)

let rec pp_stmt out (s : (info_node, info_node) istmt) =
  let _pos = s.info and s = s.stmt in
  match s with
  | Skip -> failwith "skip"
  | Assign (lv, e) -> (
      match lv.lval with
      | LValVar x -> Format.fprintf out "%s := %a" x pp_expression e
      | LValArray (x, e) -> Format.fprintf out "%s := %a" x pp_expression e)
  | Assert _f -> failwith "assert"
  | Seq (s1, s2) -> Format.fprintf out "%a; %a" pp_stmt s1 pp_stmt s2
  | Ite (e, s1, Some s2) ->
      Format.fprintf out "if %a then %a else %a" pp_expression e pp_stmt s1
        pp_stmt s2
  | Ite (e, s1, None) ->
      Format.fprintf out "if %a then %a" pp_expression e pp_stmt s1
  | While (e, f, v, s) ->
      let f =
        match f with
        | Some f -> f
        | None ->
            { info = { position = _pos; vtype = Boolean }; formula = True }
      in
      let v =
        match v with
        | Some v -> v
        | None -> { info = { position = _pos; vtype = Boolean }; expr = ETrue }
      in
      Format.fprintf out "while %a %a %a %a done" pp_expression e pp_formula f
        pp_expression v pp_stmt s

(* type why3Function = {
  wf_name : string;
  wf_env : environment;
  wf_requires : info_node iformula;
  wf_ensures : info_node iformula;
  wf_body : (info_node, info_node) istmt;
} *)

(* let pp_pair_semi out (p : string * (vkind * vtype)) =
  Format.fprintf out "(%s : %a)" (fst p) pp_type (snd (snd p))

let pp_params out (env : environment) =
  Format.fprintf out "%a" (Format.pp_print_list ~pp_sep:comma pp_pair_semi) env *)

(* let pp_function out (f : why3Function) =
  Format.fprintf out "let %s %a : () requires {%a} ensures {%a} = %a" f.wf_name
    pp_params f.wf_env pp_formula f.wf_requires pp_formula f.wf_ensures pp_stmt
    f.wf_body *)

(* exception No_Such_State of string *)
(*
let get_state_invariant (p : (info_node, info_node) process) (s : state) :
    info_node iformula =
  try (List.find (fun t -> t.source = s) p.behaviors).invariant
  with _ -> raise (No_Such_State s)

let formula_of_expr (e : info_node iexpr) : info_node iformula =
  { info = { position = e.info.position; vtype = Boolean }; formula = True }

let transition_to_function (p : (info_node, info_node) process) (source : state)
    (t : (info_node, info_node) transition) : why3Function =
  let name = source ^ "_" ^ t.target in
  let req1 = get_state_invariant p source in
  let requires =
    match t.guard with
    | None -> req1
    | Some req2 ->
        {
          info = { position = req1.info.position; vtype = Boolean };
          formula = And (req1, formula_of_expr req2);
        }
  in
  let ensures =
    {
      info = { position = req1.info.position; vtype = Boolean };
      formula = And (t.ensures, get_state_invariant p t.target);
    }
  in
  {
    wf_name = name;
    wf_env = p.env;
    wf_requires = requires;
    wf_ensures = ensures;
    wf_body = t.body;
  }

let behavior_to_functions (p : (info_node, info_node) process)
    (b : (info_node, info_node) behavior) : why3Function list =
  List.map (transition_to_function p b.source) b.transitions

let process_to_functions (p : (info_node, info_node) process) :
    why3Function list =
  List.flatten (List.map (behavior_to_functions p) p.behaviors)

*)

(* let behavior_to_functions (env : environment) (p :(info_node, info_node) behavior) : why3Function list =  *)

(* let process_to_functions (p : (info_node, info_node) process) = *)
(* let pp_process out  *)

(* let pp_transition out (t : (info_node,info_node) transition) =
   match *)

(* let mk_method (id : string) (l : (string * vtype) list) (stmt : (info_node, info_node) istmt) =  *)

(* let translate_type (t : vtype) : ty =
     match t with
       | Boolean -> ty_bool
       | Integer -> ty_int
       | Array (_t) -> ty_bool

   let translate_formula (env : environment) (f : 'a iformula) : term =
     let e = List.map (fun (x,(_vk,vt)) -> (x, create_vsymbol (id_fresh x) (translate_type vt))) env in
     let rec aux (f : 'a iformula) =
       let _pos = f.info and f = f.formula in
         match f with
           | True -> t_true
           | False -> t_false
           | LVar x ->
             begin try
               let z = List.assoc x e in t_var z
             with _ -> raise (No_Such_Symbol x) end
           | LIntCst c ->
           | _ -> t_true
           in aux f *)

