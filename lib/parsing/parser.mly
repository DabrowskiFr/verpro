%{
    open VerproSyntax.Syntax 

    type declaration =
  | State of state list
  | Input of (string * vtype) list
  | Output of (string * vtype) list
  | Variable of (string * vtype) list

%}

%token <Z.t> INT 
%token <string> ID 
%token EOF
%token LPAREN RPAREN LBRACE RBRACE LSQBRACE RSQBRACE  
%token ASSIGN SEMICOLON COMMA COLUMN DOT
%token PLUS MINUS MULT DIV MOD
%token EQ NEQ LT GT LE GE
%token BNOT BAND BOR
%token TRUE FALSE 
%token NOT OR AND IMP
%token FORALL EXISTS
%token BTRUE BFALSE
%token SKIP IF THEN ELSE END WHILE DO DONE
%token INVARIANT VARIANT ASSERT
%token PROCESS GOTO WHEN OTHERWISE REQUIRES ENSURES
%token STATE INPUT OUTPUT VARIABLE
%token INTEGER BOOLEAN
%token <string> LENGTH

%nonassoc LT GT LE GE EQ NEQ
%left AND OR IMP
%left BAND BOR
%left PLUS MINUS MULT DIV MOD
%left SEMICOLON
%left DOT
%nonassoc UNARY

%start <(pos,pos) VerproSyntax.Syntax.process>  process

%% 

let process :=
    | PROCESS; id = ID; d = list(declaration); 
        r = requires ; e = ensures; b = list(behavior); END; EOF;
        { 
            let env = 
                List.flatten 
                      (List.filter_map (
                        fun x -> match x with 
                            | Input l -> Some (List.map (fun (x,vt) -> (x, (In, vt))) l)
                            | Output l -> Some (List.map (fun (x,vt) -> (x, (Out, vt))) l)
                            | Variable l -> Some (List.map (fun (x,vt) -> (x, (KVar, vt))) l)
                            | State _ -> None ) d);
                 in 
                {
                name = id; 
                states  =
                    List.flatten 
                     (List.filter_map (fun x -> match x with State x -> Some x | _ -> None) d); 
                env = env;
                requires = r; 
                ensures = e; 
                behaviors=b } }


let declaration := 
    | ~ = preceded(STATE, separated_nonempty_list(COMMA, ID)); <State>
    | ~ = preceded(INPUT, separated_nonempty_list(COMMA, mapping)); <Input>
    | ~ = preceded(OUTPUT, separated_nonempty_list(COMMA, mapping)); <Output>
    | ~ = preceded(VARIABLE, separated_nonempty_list(COMMA, mapping)); <Variable>

let requires := preceded(REQUIRES, delimited(LBRACE, formula, RBRACE))

let ensures := preceded(ENSURES, delimited (LBRACE, formula, RBRACE))

let invariant := preceded(INVARIANT, delimited (LBRACE, formula, RBRACE))

let variant := preceded(VARIANT, delimited (LBRACE, expr, RBRACE))

let behavior :=
    | id = ID; COLUMN; f = invariant; 
        l = list(transition); o = option(defaulttransition);
        { {source = id; invariant = f; 
            transitions = match o with Some o -> l@[o] | None -> l} }

let transition := 
    | WHEN; b = expr; DO; s = stmt; GOTO; id=ID; e = ensures;
        { {guard = Some b; body = s; target = id; ensures = e}}

let defaulttransition :=
    | OTHERWISE; DO; s = stmt; GOTO; id = ID; e = ensures;
        { {guard = None; body = s; target = id; ensures = e}}

let expr :=
    | BFALSE; {{info = $loc;expr=EFalse}}
    | BTRUE; {{info = $loc;expr=ETrue}}
    | e = preceded(MINUS, expr); %prec UNARY {{info = $loc;expr= Neg e}}
    | e = preceded(BNOT, expr); %prec UNARY {{info = $loc;expr= BNot e}}
    | n = INT; {{info = $loc;expr= IntCst n}}
    | id = ID; {{info = $loc;expr= Var id}}
    | id = ID; e = delimited(LSQBRACE, expr, RSQBRACE) ; {{info = $loc;expr= Array(id,e)}}
    | id = LENGTH; {{info = $loc;expr= ArrayLength id}}
    | expr1 = expr; o=binop; expr2 = expr; {{info = $loc;expr= Binop (expr1,o,expr2)}}

(* why not to have expressions in formulas *)

let formula :=
    | TRUE; {{info = $loc; formula=True}}
    | FALSE; {{info = $loc; formula=False}}
    | n = INT; {{info = $loc;formula= LIntCst n}}
    | id = ID; {{info = $loc;formula= LVar id}}
    | p = ID; l = plist(formula ); {{info= $loc; formula = LApp(p,l)}}
     | expr1 = formula; o=binop; expr2 = formula; (* x = true -> expr as formula *)
        {{info = $loc;formula = LApp (string_of_binop o, [expr1;expr2])}}
    | f = preceded(NOT, formula); %prec UNARY {{info = $loc; formula = Not f}}
    | f1 = formula; AND; f2=formula; {{info = $loc; formula = And(f1,f2)}}
    | f1 = formula; OR; f2=formula; {{info = $loc; formula = Or(f1,f2)}}
    | f1 = formula; IMP; f2=formula; {{info = $loc; formula = Impl(f1,f2)}}
    | FORALL; l = separated_list(COMMA, mapping); DOT; f = formula; 
    {{info = $loc; formula = Forall(l,f)}}
    | EXISTS; l = separated_list(COMMA, mapping); DOT; f = formula; 
    {{info = $loc; formula = Exists(l,f)}}

let lval :=
    | id = ID; {{info = $loc; lval=LValVar id}}
    | id = ID; e = delimited(LSQBRACE, expr,RSQBRACE); {{info = $loc; lval= LValArray(id,e)}}

let stmt :=
    | SKIP; { {info = $loc; stmt=Skip} }
    | lv = lval; expr = preceded(ASSIGN, expr); {{info = $loc; stmt=Assign(lv,expr) }} 
    | f = preceded(ASSERT, delimited(LBRACE, formula, RBRACE)); {{info = $loc;stmt=Assert f}}
    | (s1, s2) = separated_pair(stmt,SEMICOLON,stmt); 
        {{info = $loc; stmt=Seq(s1,s2)}}
    | IF; b = expr; THEN; s1 = stmt; ELSE; s2 = stmt; END; 
    {{info= $loc; stmt = Ite(b, s1, Some s2)}}
    | IF; b = expr; THEN; s1 = stmt; END; 
    {{info = $loc; stmt = Ite(b,s1, None)}}
    | WHILE; b = expr; DO; f = option(invariant); e = option(variant); s=stmt; DONE; 
        {{info= $loc; stmt= While (b, f, e,s)}}

let vtype := 
    | INTEGER; { Integer }
    | BOOLEAN; { Boolean }

let binop == 
    | PLUS;  { Plus }
    | MINUS; { Minus }
    | MULT;  { Mult }
    | DIV;   { Div }
    | MOD;   { Mod }
    | EQ;    { Eq }
    | NEQ;   { NEq }
    | LT;    { Lt }
    | GT;    { Gt }
    | LE;    { Le }
    | GE;    { Ge }
    | BAND;  { BAnd }
    | BOR;   { BOr }

let mapping := separated_pair (ID, COLUMN, vtype)

let plist(X) == delimited(LPAREN, separated_list(COMMA,X), RPAREN)
