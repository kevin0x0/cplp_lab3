/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_CMM_TAB_H_INCLUDED
# define YY_YY_CMM_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    INT = 258,                     /* "integer"  */
    FLOAT = 259,                   /* "floating number"  */
    ID = 260,                      /* "identifier"  */
    TYPE = 261,                    /* "type name"  */
    SEMI = 262,                    /* ";"  */
    COMMA = 263,                   /* ","  */
    ASSIGN = 264,                  /* "="  */
    EQ = 265,                      /* "=="  */
    NE = 266,                      /* "!="  */
    LE = 267,                      /* "<="  */
    LT = 268,                      /* "<"  */
    GE = 269,                      /* ">="  */
    GT = 270,                      /* ">"  */
    ADD = 271,                     /* "+"  */
    SUB = 272,                     /* "-"  */
    MUL = 273,                     /* "*"  */
    DIV = 274,                     /* "/"  */
    AND = 275,                     /* "&&"  */
    OR = 276,                      /* "||"  */
    DOT = 277,                     /* "."  */
    NOT = 278,                     /* "!"  */
    LP = 279,                      /* "("  */
    RP = 280,                      /* ")"  */
    LB = 281,                      /* "["  */
    RB = 282,                      /* "]"  */
    LC = 283,                      /* "{"  */
    RC = 284,                      /* "}"  */
    STRUCT = 285,                  /* "struct"  */
    RETURN = 286,                  /* "return"  */
    IF = 287,                      /* "if"  */
    ELSE = 288,                    /* "else"  */
    WHILE = 289                    /* "while"  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 12 "cmm.y"

  Cst* cst;
  StringId string;

#line 103 "cmm.tab.h"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;


int yyparse (void);


#endif /* !YY_YY_CMM_TAB_H_INCLUDED  */
