%{ open Accept %}

%token <char> CHAR
%token LPAREN RPAREN STAR PLUS TIMES
%token EOF

%nonassoc LPAREN CHAR

%left PLUS
%left STAR
%left TIMES

%start main
%type <char Accept.re> main

%%

main: r = regexp EOF { r }

regexp:
| c = CHAR { Re_char c }
| LPAREN r = regexp RPAREN { r }
| r1 = regexp PLUS r2 = regexp { Re_plus (r1, r2) }
| r = regexp STAR { Re_star r }
| r1 = regexp r2 = regexp { Re_times (r1, r2) } %prec TIMES
