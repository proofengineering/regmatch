{
  open Parser

  exception Error of string
}

rule token = parse
| '|'
    { PLUS }
| '*'
    { STAR }
| ['a'-'z'] as c
    { CHAR c }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| eof
    { EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }
