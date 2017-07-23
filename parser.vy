%{ Require Import regexp. %}

%token<a> CHAR
%token LPAREN RPAREN STAR PLUS TIMES
%token EOF

%left PLUS
%left STAR
%left TIMES

%type<regexp> regexp
%start<regexp> main

%%

main: r = regexp EOF { r }

regexp:
| c = CHAR { regexp_char c }
| LPAREN r = regexp RPAREN { r }
| r1 = regexp PLUS r2 = regexp { regexp_plus r1 r2 }
| r = regexp STAR { regexp_star r }
| r1 = regexp TIMES r2 = regexp { regexp_times r1 r2 }
