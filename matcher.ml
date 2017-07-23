open Accept

let rec string_of_regexp r =
match r with
| Regexp_zero -> "[zero]"
| Regexp_unit -> "[unit]"
| Regexp_char c -> Printf.sprintf "%c" c
| Regexp_plus (r1, r2) ->
  let s1 = string_of_regexp r1 in
  let s2 = string_of_regexp r2 in
  Printf.sprintf "(%s|%s)" s1 s2
| Regexp_times (r1, r2) ->
  let s1 = string_of_regexp r1 in
  let s2 = string_of_regexp r2 in
  Printf.sprintf "(%s%s)" s1 s2
| Regexp_star r ->
  let s = string_of_regexp r in
  Printf.sprintf "(%s*)" s

(* the name of the file which contains the expressions *)
let r = Sys.argv.(1)
let s = Sys.argv.(2)

let char_list_of_string s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let main () =
  let buf = Lexing.from_string r in
  try
    let re = Parser.main Lexer.token buf in
    (*Printf.printf "%s\n" (string_of_regexp re)*)
    let mt = accept (re, char_list_of_string s) in
    Printf.printf "%b\n" mt
  with
  | Lexer.Error msg ->
      Printf.eprintf "%s%!" msg
  | Parser.Error ->
      Printf.eprintf "At offset %d: syntax error.\n%!" (Lexing.lexeme_start buf)

let _ = main ()
