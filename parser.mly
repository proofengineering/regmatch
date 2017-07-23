%{ open Accept %}

%token <char> CHAR
%token LPAREN RPAREN STAR PLUS TIMES
%token EOF

%nonassoc LPAREN CHAR

%left PLUS
%left STAR
%left TIMES

%start main
%type <Accept.regexp> main

%%

main: r = regex EOF { r }

regex:
| c = CHAR { Regexp_char c }
| LPAREN r = regex RPAREN { r }
| r1 = regex PLUS r2 = regex { Regexp_plus (r1, r2) }
| r = regex STAR { Regexp_star r }
| r1 = regex r2 = regex { Regexp_times (r1, r2) } %prec TIMES
