open Syntax

open VerproMonad.Monad
open VerproMonad.MonadOption

open MonadSyntax(M)

exception No_Such_Symbol of string 
  exception TypeError 

type info_node = {
  position : pos;
  vtype : vtype
}

let mk_info_node p vt = {position = p; vtype = vt}
let mk_iexpr p vt e = {info = mk_info_node p vt; expr=e}
let mk_ilval p vt lv = {info = mk_info_node p vt; lval=lv}
let mk_iformula p vt f = {info = mk_info_node p vt; formula=f}

let rec check_expression (env : environment) (e : pos iexpr) : info_node iexpr = 
  let loc = e.info and e = e.expr in
    match e with 
      | ETrue -> mk_iexpr loc Boolean ETrue
      | EFalse -> mk_iexpr loc Boolean EFalse
      | IntCst c -> mk_iexpr loc Integer (IntCst c)
      | Var x -> 
        begin try
          mk_iexpr loc (snd (List.assoc x env)) (Var x)
        with _ -> raise (No_Such_Symbol x) end
      | Array (x,e) -> 
          begin try 
            let e' = check_expression env e in 
            mk_iexpr loc (snd (List.assoc x env)) (Array (x,e'))
          with _ -> raise TypeError
        end
      | ArrayLength (x) ->
        begin try 
          mk_iexpr loc Integer (ArrayLength (x))
        with _ -> raise TypeError
        end
      |   Neg e -> mk_iexpr loc Boolean (Neg (check_expression env e))
      |   BNot e -> 
          mk_iexpr loc Boolean (BNot (check_expression env e))
      | Binop(e1,o,e2) -> 
          let e1' = check_expression env e1
          and e2' = check_expression env e2 in
          mk_iexpr loc Boolean (Binop (e1', o, e2'))
and check_lval (env : environment) (lv : pos ilval) : info_node ilval = 
  let pos = lv.info and lv = lv.lval in
    match lv with 
      | LValVar x ->  
        begin try
          let (_, vt) = List.assoc x env in 
          {info = {position = pos; vtype = vt}; lval = LValVar x}
        with _ -> raise (No_Such_Symbol x)
        end
      | LValArray (x,e) ->  
        begin try
          let (_, vt) = List.assoc x env in 
          {info = {position = pos; vtype = vt}; lval = LValArray (x,check_expression env e)}
        with _ -> raise (No_Such_Symbol x)
        end

let rec check_formula (env : environment) 
  (f :  pos iformula) : info_node iformula = 
    let pos = f.info and f = f.formula in
  begin match f with 
    | True -> {info = {position = pos; vtype=Boolean}; formula = True}  
     | False -> {info = {position = pos; vtype=Boolean};formula = False}
    | LVar x -> 
      begin try 
      let (_, vt) = List.assoc x env in 
      {info = {position = pos; vtype=vt}; formula = LVar x}
      with _ -> raise (No_Such_Symbol x)
      end
    | LIntCst n -> {info = {position = pos; vtype=Integer}; formula = LIntCst n} 
    | LApp (id,l) -> {info = {position = pos; vtype=Boolean}; formula = LApp (id,List.map (check_formula env) l)}
    | Not f -> {info={position= pos;vtype=Boolean}; formula = Not (check_formula env f)}
    | And (f1, f2) -> {info={position = pos; vtype=Boolean}; formula = And (check_formula env f1, check_formula env f2)}
    | Or (f1, f2) -> {info={position = pos; vtype=Boolean}; formula = Or (check_formula env f1, check_formula env f2)}
    | Impl (f1, f2) -> {info={position = pos; vtype=Boolean}; formula = Impl (check_formula env f1, check_formula env f2)}
    | Forall (l, f) -> {info={position = pos; vtype=Boolean}; formula = Forall (l, check_formula env f)}
    | Exists (l, f) -> {info={position = pos; vtype=Boolean}; formula = Exists (l, check_formula env f)}
  end 

    (* | False -> {position = pos; formula = False}
    | LVar x -> {position = pos; formula = LVar x}
    | LIntCst n -> {position = pos; formula = LIntCst n}
    | LApp (id,l) -> {position = pos; formula = LApp (id,List.map (check_expression env) l)}
    (* | LPredicate (id, l) -> {position = pos; formula = LPredicate (id, List.map (check_expression env) l)}  *)
    | Not f -> {position = pos; formula = Not (check_formula env f)}
    | And (f1, f2) -> {position = pos; formula = And (check_formula env f1, check_formula env f2)}
    | Or (f1, f2) -> {position = pos; formula = Or (check_formula env f1, check_formula env f2)}
    | Impl (f1, f2) -> {position = pos; formula = Impl (check_formula env f1, check_formula env f2)}
    | Forall (l, f) -> {position = pos; formula = Forall (l, check_formula env f)}
    | Exists (l, f) -> {position = pos; formula = Exists (l, check_formula env f)}
end *)
let rec check_stmt (env : environment) (s : (pos,pos) istmt) : (info_node, info_node) istmt =
  let pos = s.info and s = s.stmt in 
  match s with 
  | Skip -> {info = pos; stmt = Skip}
  | Assign (lv, e) -> 
      let lv = check_lval env lv in 
      let e = check_expression env e in
      {info = pos; stmt = Assign (lv, e)}
  | Assert (f) -> 
      let f = check_formula env f in 
      {info = pos; stmt = Assert(f)}
  | Seq (s1,s2) -> 
      let s1 = check_stmt env s1 
      and s2 = check_stmt env s2 in
      { info = pos; stmt = Seq (s1, s2)}
  | Ite (e,s1,s2) -> 
      let e = check_expression env e in
      let s1 = check_stmt env s1 in
      let s2 = M.fmap (check_stmt env) s2 in
        {info = pos; stmt = Ite (e, s1, s2)}         
  | While (e, f, v, s) ->
    let e = check_expression env e in
    let f = M.fmap (check_formula env) f in
    let v = M.fmap (check_expression env) v in
    let s = check_stmt env s in 
    {info = pos; stmt=While (e, f,v, s)}


let check_transition (env : environment) (t : (pos,pos) transition) : (info_node,info_node) transition = 
    {
      guard = M.fmap (check_expression env) t.guard;
      body = check_stmt env t.body;
      target = t.target;
      ensures = check_formula env t.ensures
    }

let check_behavior (env : environment) (b : (pos, pos) behavior) : (info_node,info_node) behavior =
    {
      source = b.source;
      invariant = check_formula env b.invariant;
      transitions = List.map (check_transition env) b.transitions
    }
(* 
    type ('a,'b) process = {
      name : string;
      states : state list;
      env : environment;
      requires : 'b iformula; 
      ensures : 'b iformula;
      behaviors : (('a,'b) behavior) list;
    } *)

    let check_process (env : environment) (p : (pos,pos) process) : (info_node,info_node) process = 
      {
        name = p.name;
        states = p.states;
        env = p.env;
        requires = check_formula env p.requires;
        ensures = check_formula env p.ensures;
        behaviors = List.map (check_behavior env) p.behaviors
      }