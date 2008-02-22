(* $Id: transf.mll,v 1.10 2008-02-22 16:40:20 uid562 Exp $ *)

{ open Lexing;;
  let idx = Buffer.create 5
}

rule main = parse
    "\\begin{syntax}" {
      print_string "\\begin{syntax}";
      syntax lexbuf }
  | "\\@" {
      print_string "@";
      main lexbuf }
  | _ {
      print_char (lexeme_char lexbuf 0); main lexbuf }
  | eof {
      () }

and syntax = parse
    "\\end{syntax}" {
      print_string "\\end{syntax}";
      main lexbuf }
  | ";" ([^ '\n']* as s) '\n' [' ''\t']* '|' {
      print_string "& \\textrm{";
      print_string s;
      print_string "} \\alt{}";
      syntax lexbuf }
  | ";" ([^ '\n']* as s) '\n' [' ''\t']* '\\' [' ''\t']* '\n' {
      print_string "& \\textrm{";
      print_string s;
      print_string "} \\sep{}";
      syntax lexbuf }
  | ";" ([^ '\n']* as s) '\n' {
      print_string "& \\textrm{";
      print_string s;
      print_string "} \\newl{}";
      syntax lexbuf }
  | "@" {
      print_string "}";
      main lexbuf }
  | '\'' {
      print_string "\\term{";
      Buffer.clear idx;
      inquote lexbuf }
  | '"' {
      print_string "\\term{";
      Buffer.clear idx;
      indoublequote lexbuf }
  | "below" { print_string "\\below"; syntax lexbuf }
  | "epsilon" { print_string "\\emptystring"; syntax lexbuf }
  | ['A'-'Z''a'-'z''-'] + {
      print_string "\\nonterm{";
      print_string (lexeme lexbuf);
      print_string"}";
      syntax lexbuf }
  | '\\' ['a'-'z''A'-'Z'] + {
      print_string (lexeme lexbuf);
      syntax lexbuf }
  | ['_' '^'] _ {
      print_string (lexeme lexbuf);
      syntax lexbuf }
  | "*" { print_string "\\repetstar{}"; syntax lexbuf }
  | "+" { print_string "\\repetplus{}"; syntax lexbuf }
  | "?" { print_string "\\repetone{}"; syntax lexbuf }
  | "(" { print_string "\\lparen{}"; syntax lexbuf }
  | ")" { print_string "\\rparen{}"; syntax lexbuf }
  | "::=" { print_string "\\is{}"; syntax lexbuf }
  | "|" { print_string "\\orelse{}"; syntax lexbuf }
  | "\\" { print_string "\\sep{}"; syntax lexbuf }
  | "{" { print_string "\\notimplemented"; check_rq lexbuf }
  | "}" { print_string "}"; syntax lexbuf }
  | _ {
      print_char (lexeme_char lexbuf 0);
      syntax lexbuf }

and inquote = parse
    ['A'-'Z' 'a'-'z' '0'-'9'] as c {
      print_char c;
      Buffer.add_char idx c;
      inquote lexbuf }
  | '\'' {
      print_string ("}{" ^ Buffer.contents idx ^ "}");
      Buffer.clear idx;
      syntax lexbuf }
  | _ {
      print_string "\\char";
      print_int (int_of_char (lexeme_char lexbuf 0));
      inquote lexbuf }

and indoublequote = parse
    ['A'-'Z' 'a'-'z' '0'-'9'] as c {
      print_char c;
      Buffer.add_char idx c;
      indoublequote lexbuf }
  | '"' {
      print_string ("}{" ^ Buffer.contents idx ^ "}");
      Buffer.clear idx;
      syntax lexbuf }
  | _ {
      print_string "\\char";
      print_int (int_of_char (lexeme_char lexbuf 0));
      indoublequote lexbuf }
and check_rq = parse
  | "[" { print_string "["; inbrack lexbuf }
  | "" { print_string "{"; syntax lexbuf }
and inbrack = parse
    "]" { print_string "]{"; syntax lexbuf }
  | _  { print_char (lexeme_char lexbuf 0);
           inbrack lexbuf }
