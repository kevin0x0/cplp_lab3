%{
#include <stdint.h>
#include "mycc.h"

extern int yylineno;
int yylex(void);

%}

%define parse.error verbose

%union {
  Cst* cst;
  StringId string;
}

%token <cst>    INT     "integer"
%token <cst>    FLOAT   "floating number"
%token <string> ID      "identifier"
%token <cst>    TYPE    "type name"
%token <cst>    SEMI    ";"
%token <cst>    COMMA   ","
%token <cst>    ASSIGN  "="
%token <cst>    EQ      "=="
%token <cst>    NE      "!="
%token <cst>    LE      "<="
%token <cst>    LT      "<"
%token <cst>    GE      ">="
%token <cst>    GT      ">"
%token <cst>    ADD     "+"
%token <cst>    SUB     "-"
%token <cst>    MUL     "*"
%token <cst>    DIV     "/"
%token <cst>    AND     "&&"
%token <cst>    OR      "||"
%token <cst>    DOT     "."
%token <cst>    NOT     "!"
%token <cst>    LP      "("
%token <cst>    RP      ")"
%token <cst>    LB      "["
%token <cst>    RB      "]"
%token <cst>    LC      "{"
%token <cst>    RC      "}"
%token <cst>    STRUCT  "struct"
%token <cst>    RETURN  "return"
%token <cst>    IF      "if"
%token <cst>    ELSE    "else"
%token <cst>    WHILE   "while"

%type <cst>     Program ExtDefList ExtDef ExtDecList
%type <cst>     Specifier StructSpecifier
%type <string>  OptTag Tag
%type <cst>     VarDec FunDec VarList ParamDec CompSt
%type <cst>     StmtList Stmt DefList Def DecList Dec Exp Args

%right          ASSIGN
%left           OR
%left           AND
%left           LE LT GE GT NE EQ
%left           ADD SUB
%left           MUL DIV
%right          NOT
%left           LP RP RB LB DOT
%nonassoc       ELSE



%%

Program : ExtDefList                              { $$ = $1; parser_state->program = $1; }
        | error                                   { $$ = parser_state->noattrtokennode.error; }
        ;

ExtDefList : ExtDef ExtDefList                    { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, $2)); }
           |                                      { $$ = NULL; }
           ;

ExtDef : Specifier ExtDecList SEMI                { $$ = pstate_appendcst(parser_state, cst_create_extdefdec(yylineno, $1, $2)); }
       | Specifier SEMI                           { $$ = pstate_appendcst(parser_state, cst_create_extdefdec(yylineno, $1, NULL)); }
       | Specifier FunDec CompSt                  { $$ = pstate_appendcst(parser_state, cst_create_extdeffunc(yylineno, $1, $2, $3)); }
       | error SEMI                               { $$ = parser_state->noattrtokennode.error; }
       ;

ExtDecList : VarDec                               { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, NULL)); }
           | VarDec COMMA ExtDecList              { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, $3)); }
           ;


Specifier : TYPE                                  { $$ = $1; }
          | StructSpecifier                       { $$ = $1; }
          ;

StructSpecifier : STRUCT OptTag LC DefList RC     { $$ = pstate_appendcst(parser_state, cst_create_structdef(yylineno, $2, $4)); }
                | STRUCT Tag                      { $$ = pstate_appendcst(parser_state, cst_create_structtype(yylineno, $2)); } 
                ;

OptTag : ID                                       { $$ = $1; }
       |                                          { $$ = parser_state->dummyname; }
       ;

Tag : ID                                          { $$ = $1; }
    ;

VarDec : ID                                       { $$ = pstate_appendcst(parser_state, cst_create_id(yylineno, $1)); }
       | VarDec LB INT RB                         { $$ = pstate_appendcst(parser_state, cst_create_decarr(yylineno, $1, ((CstInt*)($3))->val)); }
       ;

FunDec : ID LP VarList RP                         { $$ = pstate_appendcst(parser_state, cst_create_funcdec(yylineno, $1, $3)); }
       | ID LP RP                                 { $$ = pstate_appendcst(parser_state, cst_create_funcdec(yylineno, $1, NULL)); }
       ;

VarList : ParamDec COMMA VarList                  { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, $2)); }
        | ParamDec                                { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, NULL)); }
        ;

ParamDec : Specifier VarDec                       { $$ = pstate_appendcst(parser_state, cst_create_param(yylineno, $1, $2)); }
    ;


CompSt : LC DefList StmtList RC                   { $$ = pstate_appendcst(parser_state, cst_create_stmtcomp(yylineno, $2, $3)); }
       ;

StmtList : Stmt StmtList                          { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, $2)); }
         |                                        { $$ = NULL; }
         ;  

Stmt : Exp SEMI                                   { $$ = pstate_appendcst(parser_state, cst_create_stmtexpr(yylineno, $1)); }
     | CompSt                                     { $$ = $1; }
     | RETURN Exp SEMI                            { $$ = pstate_appendcst(parser_state, cst_create_stmtreturn(yylineno, $2)); }
     | IF LP Exp RP Stmt                          { $$ = pstate_appendcst(parser_state, cst_create_stmtif(yylineno, $3, $5, NULL)); }
     | IF LP Exp RP Stmt ELSE Stmt                { $$ = pstate_appendcst(parser_state, cst_create_stmtif(yylineno, $3, $5, $7)); }
     | WHILE LP Exp RP Stmt                       { $$ = pstate_appendcst(parser_state, cst_create_stmtwhile(yylineno, $3, $5)); }
     | error SEMI                                 { $$ = parser_state->noattrtokennode.error; }
     ;


DefList : Def DefList                             { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, $2)); }
        |                                         { $$ = NULL; }
        ;

Def : Specifier DecList SEMI                      { $$ = pstate_appendcst(parser_state, cst_create_def(yylineno, $1, $2)); }
    ;

DecList : Dec                                     { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, NULL)); }
        | Dec COMMA DecList                       { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, $3)); }
        ;

Dec : VarDec                                      { $$ = pstate_appendcst(parser_state, cst_create_dec(yylineno, $1, NULL)); }
    | VarDec ASSIGN Exp                           { $$ = pstate_appendcst(parser_state, cst_create_dec(yylineno, $1, $3)); }
    ;


Exp : Exp ASSIGN Exp                              { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_ASSIGN, $1, $3)); }
    | Exp AND Exp                                 { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_AND, $1, $3)); }
    | Exp OR Exp                                  { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_OR, $1, $3)); }
    | Exp LE Exp                                  { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_LE, $1, $3)); } 
    | Exp LT Exp                                  { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_LT, $1, $3)); } 
    | Exp GE Exp                                  { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_GE, $1, $3)); } 
    | Exp GT Exp                                  { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_GT, $1, $3)); } 
    | Exp NE Exp                                  { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_NE, $1, $3)); } 
    | Exp EQ Exp                                  { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_EQ, $1, $3)); } 
    | Exp ADD Exp                                 { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_ADD, $1, $3)); }
    | Exp SUB Exp                                 { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_SUB, $1, $3)); }
    | Exp MUL Exp                                 { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_MUL, $1, $3)); }
    | Exp DIV Exp                                 { $$ = pstate_appendcst(parser_state, cst_create_bin(yylineno, CSTOP_DIV, $1, $3)); }
    | LP Exp RP                                   { $$ = $2; }
    | SUB Exp                                     { $$ = pstate_appendcst(parser_state, cst_create_pre(yylineno, CSTOP_NEG, $2)); }
    | NOT Exp                                     { $$ = pstate_appendcst(parser_state, cst_create_pre(yylineno, CSTOP_NOT, $2)); }
    | Exp LP Args RP                              { $$ = pstate_appendcst(parser_state, cst_create_call(yylineno, $1, $3)); }
    | Exp LP RP                                   { $$ = pstate_appendcst(parser_state, cst_create_call(yylineno, $1, NULL)); }
    | Exp LB Exp RB                               { $$ = pstate_appendcst(parser_state, cst_create_index(yylineno, $1, $3)); }
    | Exp DOT ID                                  { $$ = pstate_appendcst(parser_state, cst_create_dot(yylineno, $1, $3)); }
    | ID                                          { $$ = pstate_appendcst(parser_state, cst_create_id(yylineno, $1)); }
    | INT                                         { $$ = $1; }
    | FLOAT                                       { $$ = $1; }
    ;

Args : Exp COMMA Args                             { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, $3)); }
     | Exp                                        { $$ = pstate_appendcst(parser_state, cst_create_list(yylineno, $1, NULL)); }
     ;


%% 
