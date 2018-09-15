%{
Require Import RegExp.regexp.
Require Import Ascii.
%}

%token<ascii> CHAR
%token LPAREN RPAREN STAR PLUS TIMES
%token EOF

%left PLUS
%left STAR
%left TIMES

%type<re ascii> regexp
%start<re ascii> main

%%

main: r = regexp EOF { r }

regexp:
| c = CHAR { re_char c }
| LPAREN r = regexp RPAREN { r }
| r1 = regexp PLUS r2 = regexp { re_plus r1 r2 }
| r = regexp STAR { re_star r }
| r1 = regexp TIMES r2 = regexp { re_times r1 r2 }
