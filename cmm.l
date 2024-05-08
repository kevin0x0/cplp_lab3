%top {
#include <stdlib.h>
#include "mycc.h"
#include "cmm.tab.h"
#include "utils.h"
}

%option yylineno

INT_HEX 0x[A-Fa-f0-9]+
INT_OCT 0[0-7]*
INT_DEC [1-9][0-9]*
FLOAT   [0-9]+\.[0-9]+
FLOATE  [0-9]+(\.[0-9]+)?[Ee][+\-]?[0-9]+
TINT    int
TFLOAT  float
STRUCT  struct
RETURN  return
WHILE   while
IF      if
ELSE    else

SEMI    ;
COMMA   ,
DOT     \.

ASSIGN  =
ADD     \+
SUB     \-
MUL     \*
DIV     \/
MOD     \%
AND     &&
OR      \|\|
NOT     !

LP      \(
RP      \)
LB      \[
RB      \]
LC      \{
RC      \}

EQ      ==
NE      !=
LT      <
LE      <=
GT      >
GE      >=

ID      [A-Za-z_][A-Za-z0-9_]*

SPACE   [ \t\n\r]*
COMMENT \/\*([^\*]|\*[^\/])\*\/|\/\/[^\n\r]
ERROR   .
%%

{INT_HEX} { yylval.cst = pstate_appendcst(parser_state, cst_create_int(yylineno, strtoll(yytext + 2, NULL, 16))); return INT; }
{INT_OCT} { yylval.cst = pstate_appendcst(parser_state, cst_create_int(yylineno, strtoll(yytext, NULL, 8))); return INT; }
{INT_DEC} { yylval.cst = pstate_appendcst(parser_state, cst_create_int(yylineno, strtoll(yytext, NULL, 10))); return INT; }
{FLOAT}   { yylval.cst = pstate_appendcst(parser_state, cst_create_float(yylineno, strtof(yytext, NULL))); return FLOAT; }
{FLOATE}  { yylval.cst = pstate_appendcst(parser_state, cst_create_float(yylineno, strtof(yytext, NULL))); return FLOAT; }
{TINT}    { yylval.cst = pstate_appendcst(parser_state, cst_create_type(yylineno, BTYPE_INT)); return TYPE; }
{TFLOAT}  { yylval.cst = pstate_appendcst(parser_state, cst_create_type(yylineno, BTYPE_FLOAT)); return TYPE; }

{STRUCT}  { return STRUCT; }
{RETURN}  { return RETURN; }
{WHILE}   { return WHILE; }
{IF}      { return IF; }
{ELSE}    { return ELSE; }

{SEMI}    { return SEMI; }
{COMMA}   { return COMMA; }
{DOT}     { return DOT; }
{ASSIGN}  { return ASSIGN; }

{ADD}     { return ADD; }
{SUB}     { return SUB; }
{MUL}     { return MUL; }
{DIV}     { return DIV; }
{AND}     { return AND; }
{OR}      { return OR; }
{NOT}     { return NOT; }

{EQ}      { return EQ; }
{NE}      { return NE; }
{LT}      { return LT; }
{LE}      { return LE; }
{GT}      { return GT; }
{GE}      { return GE; }

{LP}      { return LP; }
{RP}      { return RP; }
{LB}      { return LB; }
{RB}      { return RB; }
{LC}      { return LC; }
{RC}      { return RC; }

{ID}      { char* str = strtbl_newstring(parser_state->strtbl, yytext);
            utils_oom_ifnull(str);
            yylval.string = strtbl_stringid(parser_state->strtbl, str);
            return ID; }

{SPACE}   {}
{COMMENT} {}
{ERROR}   { mycc_error("A", yylineno, "mysterious character '%s'", yytext); }


