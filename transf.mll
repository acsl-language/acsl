{ open Lexing;;
  let idx = Buffer.create 5
  let full_kw = Buffer.create 5

  let modern = ref false

  let check = ref false

  let defined = Hashtbl.create 17

  let used = Hashtbl.create 17

  let current_non_terminal = ref ("", ("",-1))

  let current_file = ref ""

  let current_line = ref 1

  let set_file f = current_file := f; current_line:=1

  let non_terminal s =
    current_non_terminal:=(s,(!current_file,!current_line))

  let builtin_rule s =
    Hashtbl.add defined s ["",-1];
    Hashtbl.add used s ["",-1]

(* Cf ISO C standard, annex A.2 *)
  let c_grammar =
    [ "primary-expression"; "generic-selection"; "generic-assoc-list";
      "generic-association"; "postfix-expression"; "argument-expression-list";
      "unary-expression"; "unary-operator"; "cast-expression"; 
      "multiplicative-expression"; "additive-expression";
      "shift-expression"; "relational-expression"; "equality-expression";
      "AND-expression"; "exclusive-OR-expression"; "inclusive-OR-expression";
      "logical-AND-expression"; "logic-OR-expression"; "conditional-expression";
      "assignment-expression"; "assignment-operator"; "expression";
      "constant-expression";
      "declaration"; "declaration-specifiers"; "init-declarator-list";
      "init-declarator"; "storage-class-specifier"; "type-specifier";
      "struct-or-union-specifier"; "struct-or-union";
      "struct-declaration-list"; "struct-declaration";
      "struct-declarator-list"; "struct-declarator"; "enum-specifier";
      "enumerator-list"; "enumerator"; "atomic-type-specifier";
      "type-qualifier"; "function-specifier"; "alignment-specifier";
      "declarator"; "direct-declarator"; "pointer"; "type-qualifier-list";
      "parameter-type-list"; "parameter-list"; "parameter-declaration";
      "identifier-list"; "type-name"; "abstract-declarator";
      "direct-abstract-declarator"; "typedef-name"; "initializer";
      "initializer-list"; "designation"; "designator-list"; "designator";
      "static_assert-declaration";
      "statement"; "labeled-statement"; "compound-statement"; "block-item-list";
      "block-item"; "expression-statement"; "selection-statement";
      "iteration-statement"; "jump-statement";
      "translation-unit"; "external-declaration"; "function-definition";
      "declaration-list" ]

  let () =
    List.iter
      (fun s -> builtin_rule ("C-" ^ s); builtin_rule ("ghost-" ^ s)) c_grammar

  let add_defined () =
    let non_term, loc = !current_non_terminal in
    if non_term <> "" then begin
      let l =
        try Hashtbl.find defined non_term with Not_found -> []
      in
      Hashtbl.add defined non_term (loc::l);
      current_non_terminal := ("",loc)
    end

  let add_used () =
    let non_term, loc = !current_non_terminal in
    if non_term <> "" then begin
      let l =
        try Hashtbl.find used non_term
        with Not_found -> []
      in
      Hashtbl.replace used non_term (loc::l);
      current_non_terminal := ("", loc)
    end

  let print_error d is is_not (f,l) =
    Printf.printf
      "File %s, Line %d: Non-terminal %s is %s but never %s\n%!"
      f l d is is_not

  let result () =
    let has_err = ref false in
    Hashtbl.iter
      (fun d l -> if not (Hashtbl.mem  used d) then begin
        has_err:=true;
        List.iter (print_error d "defined" "used") l
      end)
      defined;
    Hashtbl.iter
      (fun d l -> if not (Hashtbl.mem  defined d) then begin
        has_err:=true;
        List.iter (print_error d "used" "defined") l
      end)
      used;
    if !has_err then exit 1

  let print_string s = if not !check then print_string s
  let print_char c = if not !check then print_char c

  let escape_keyword s =
    let buf = Buffer.create 5 in
    String.iter
      (function
           c when ('A' <= c && c <= 'Z') ||
                  ('a' <= c && c <= 'z') ||
                  ('0' <= c && c <= '9')
             -> Buffer.add_char buf c
         | c -> Buffer.add_string buf
             (Printf.sprintf "\\char%d" (int_of_char c))) s;
    Buffer.contents buf

  let make_keyword () =
    let keyword = Buffer.contents full_kw in
    let index = Buffer.contents idx in
    print_string "\\addspace";
    if not !check then begin
      if !modern then
        Printf.printf
          "\\lstinline$%s$" keyword
      else
        Printf.printf "\\texttt{%s}" (escape_keyword keyword);
      if index <> "" then
        Printf.printf "\\indextt%s{%s}"
          (if keyword.[0] = '\\' then "bs" else "") index;
    end;
    print_string "\\spacetrue";
    Buffer.clear idx;
    Buffer.clear full_kw

}

rule main = parse
    "\\begin{syntax}" {
      print_string "\\begin{syntax}";
      syntax lexbuf }
  | "\\@" {
      print_string "@";
      main lexbuf }
  | "\n" { incr current_line; print_char '\n'; main lexbuf }
  | _ {
      print_char (lexeme_char lexbuf 0); main lexbuf }
  | eof {
      () }

and syntax = parse
    "\\end{syntax}" {
      add_used ();
      print_string "\\end{syntax}";
      main lexbuf }
  | ";" ([^ '\n']* as s) '\n' [' ''\t']* '|' {
      add_used ();
      incr current_line;
      print_string "& \\textrm{";
      print_string s;
      print_string "} \\alt{}";
      syntax lexbuf }
  | ";" ([^ '\n']* as s) '\n' [' ''\t']* '\\' [' ''\t']* '\n' {
      add_used ();
      incr current_line; incr current_line;
      print_string "& \\textrm{";
      print_string s;
      print_string "} \\sep{}";
      syntax lexbuf }
  | ";" ([^ '\n']* as s) '\n' {
      add_used ();
      incr current_line;
      print_string "& \\textrm{";
      print_string s;
      print_string "} \\newl{}";
      syntax lexbuf }
  | "@" {
      add_used ();
      print_string "}";
      main lexbuf }
  | '\'' {
      add_used ();
      Buffer.clear idx;
      Buffer.clear full_kw;
      inquote lexbuf }
  | '"' {
      Buffer.clear idx;
      Buffer.clear full_kw;
      indoublequote lexbuf }
  | "below" { add_used (); print_string "\\below"; syntax lexbuf }
  | "epsilon" { add_used (); print_string "\\emptystring"; syntax lexbuf }
  | ['A'-'Z''a'-'z''-'] + {
      add_used ();
      let s = lexeme lexbuf in
      non_terminal s;
      print_string "\\nonterm{";
      print_string s;
      print_string "}";
      check_nonterm_note lexbuf }
  | '\\' ['a'-'z''A'-'Z'] + {
      add_used ();
      print_string (lexeme lexbuf);
      syntax lexbuf }
  | ['_' '^'] _ {
      add_used ();
      print_string (lexeme lexbuf);
      syntax lexbuf }
  | "*" { add_used (); print_string "\\repetstar{}"; syntax lexbuf }
  | "+" { add_used (); print_string "\\repetplus{}"; syntax lexbuf }
  | "?" { add_used (); print_string "\\repetone{}"; syntax lexbuf }
  | "(" { add_used (); print_string "\\lparen{}"; syntax lexbuf }
  | ")" { add_used (); print_string "\\rparen{}"; syntax lexbuf }
  | "::=" { add_defined (); print_string "\\is{}"; syntax lexbuf }
  | "|" { add_used (); print_string "\\orelse{}"; syntax lexbuf }
  | "\\" { add_used (); print_string "\\sep{}"; syntax lexbuf }
  | "{" { add_used (); 
          print_string "\\begin{notimplementedenv}";
          check_implementation_note lexbuf }
  | "}" { print_string "\\end{notimplementedenv}"; syntax lexbuf }
  | "\n" { incr current_line; print_char '\n'; syntax lexbuf }
  | _ {
      print_char (lexeme_char lexbuf 0);
      syntax lexbuf }

and inquote = parse
    ['A'-'Z' 'a'-'z' '0'-'9' '?'] as c {
      Buffer.add_char full_kw c;
      Buffer.add_char idx c;
      inquote lexbuf }
  | '\'' {
      make_keyword ();
      syntax lexbuf }
  | '_' {
      Buffer.add_char full_kw '_';
      Buffer.add_string idx "\\_";
      inquote lexbuf
    }
  | _ as c {
      Buffer.add_char full_kw c;
      inquote lexbuf }

and indoublequote = parse
    ['A'-'Z' 'a'-'z' '0'-'9' '?'] as c {
      Buffer.add_char full_kw c;
      Buffer.add_char idx c;
      indoublequote lexbuf }
  | '"' {
      make_keyword();
      syntax lexbuf }
  | '_' {
      Buffer.add_char full_kw '_';
      Buffer.add_string idx "\\_";
      indoublequote lexbuf
    }
  | _ as c {
      Buffer.add_char full_kw c;
      indoublequote lexbuf }
and check_implementation_note = parse
  | "[" { print_string "["; implementation_note lexbuf }
  | "" { syntax lexbuf }
and implementation_note = parse
    "]" { print_string "]"; syntax lexbuf }
  | _  { print_char (lexeme_char lexbuf 0);
           implementation_note lexbuf }
and check_nonterm_note = parse
  | "[" { print_string "{"; nonterm_note lexbuf }
  | ""  { print_string "{}"; syntax lexbuf }
and nonterm_note = parse
    "]" { print_string "}"; syntax lexbuf }
  | _  { print_char (lexeme_char lexbuf 0);
           nonterm_note lexbuf }

{

  let () = Arg.parse
    [ "-modern", Arg.Set modern, "set modern style"; 
      "-check", Arg.Set check, "check grammar coherence";
      "-builtin",
      Arg.String builtin_rule, "<s> : consider s as a valid non-terminal"
    ]
    (fun f ->
      set_file f;
       let cin = open_in f in
       let lb = from_channel cin in
       main lb;
       close_in cin)
    "transf [-modern|-check] file";
    if !check then result ();
    exit 0

}
