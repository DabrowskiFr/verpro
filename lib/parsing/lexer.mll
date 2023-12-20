{
    open Lexing
    open Parser
    exception SyntaxError of (position * position) * string

    let next_line lexbuf =
        let pos = lexbuf.lex_curr_p in
            lexbuf.lex_curr_p <-
                { pos with pos_bol = lexbuf.lex_curr_pos;
                    pos_lnum = pos.pos_lnum + 1
                }
    let pos_range lexbuf = 
        let sp = lexeme_start_p lexbuf and ep = lexeme_end_p lexbuf in 
        sp,ep
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let id = (alpha) (alpha|digit|'_')*
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let pos = (['1'-'9'] ('_'|digit)*)
let int = '-'? (pos | '0')
let length = id '.' "length"


rule read_token = parse
    | "("           { LPAREN }
    | ")"           { RPAREN }
    | "{"           { LBRACE }
    | "}"           { RBRACE }
    | "["           { LSQBRACE }
    | "]"           { RSQBRACE }
    | "="           { EQ }
    | "<>"          { NEQ }
    | "<"           { LT }
    | ">"           { GT}
    | "<="          { LE }
    | ">= "         { GE }
    | ":="          { ASSIGN }
    | ":"           { COLUMN }
    | ";"           { SEMICOLON }
    | ","           { COMMA }
    | "+"           { PLUS }
    | "-"           { MINUS }
    | "*"           { MULT }
    | "/"           { DIV }
    | "%"           { MOD }
    | "not"         { NOT }
    | "/\\"         { AND }
    | "\\/"         { OR }
    | "!"           { BNOT }
    | "&&"          { BAND }
    | "||"          { BOR }
    | "->"          { IMP }
    | "True"        { TRUE }
    | "False"       { FALSE }
    | "true"        { BTRUE }
    | "false"       { BFALSE}
    | "forall"      { FORALL }
    | "exists"      { EXISTS}
    | "."           { DOT }
    | "skip"        { SKIP }
    | "if"          { IF }
    | "then"        { THEN }
    | "else"        { ELSE }
    | "end"         { END }
    | "while"       { WHILE }
    | "do"          { DO }
    | "done"        { DONE }
    | "invariant"   { INVARIANT }
    | "variant"     { VARIANT }
    | "assert"      { ASSERT }
    | "goto"        { GOTO }
    | "process"     { PROCESS }
    | "when"        { WHEN }
    | "otherwise"   { OTHERWISE }
    | "requires"    { REQUIRES }
    | "ensures"     { ENSURES }
    | "state"       { STATE }
    | "input"       { INPUT }
    | "output"      { OUTPUT }
    | "var"         { VARIABLE }
    | "int"         { INTEGER }
    | "bool"        { BOOLEAN }
    | length        { LENGTH (List.hd (String.split_on_char '.' (Lexing.lexeme lexbuf))) }
    | id            { ID (Lexing.lexeme lexbuf) }
    | whitespace    { read_token lexbuf }
    | int           { INT (Z.of_string (Lexing.lexeme lexbuf |> String.split_on_char '_' |> String.concat ""))}
    | newline { next_line lexbuf; read_token lexbuf }
    | eof { EOF }
    | _ {raise (SyntaxError (pos_range lexbuf, "Lexer - Illegal character: " ^ Lexing.lexeme lexbuf)) }