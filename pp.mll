
{
  open Lexing

  let color = ref false
  let in_utf8 = ref false

  let unrecognized = ref 0

  let utf8 = function
    | ">=" -> "\\ensuremath{\\geq}"
    | "<=" -> "\\ensuremath{\\leq}"
    | ">" -> "\\ensuremath{>}"
    | "<" -> "\\ensuremath{<}"
    | "!=" -> "\\ensuremath{\\not\\equiv}"
    | "==" -> "\\ensuremath{\\equiv}"
    | "==>" -> "\\ensuremath{\\Longrightarrow}"
    | "<==>" -> "\\ensuremath{\\Longleftrightarrow}"
    | "&&" -> "\\ensuremath{\\land}"
    | "||" -> "\\ensuremath{\\lor}"
    | "!" -> "\\ensuremath{\\neg}"
    | s ->
        Format.eprintf "Cannot convert symbol %s to utf8\n" s;
        unrecognized:= 2; s

  let in_comment = ref false
  let in_slashshash = ref false

  let c_keywords =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [
	"auto"; "assert"; "break"; "case"; "continue"; "new";
	"default"; "do"; "else"; "for"; "goto"; "if";
	"return"; "switch"; "while";
	"class" ; "interface" ;
	"public" ; "private" ; "static" ; "struct" ;
	"typedef"; "union";
	"throws" ; "extends" ; "implements" ; "reads" ;
	"requires"; "assumes" ; "invariant"; "representation";
	"loop" ; "variant" ; "data" ; "strong" ;
	"ensures" ; "breaks"; "continues"; "returns"; "assigns"; "modifiable" ; "signals" ;
	"logic" ; "type" ; "predicate" ; "axiom";
	"exit_behavior" ; "behavior" ; "model"; "ghost"; "terminates";
        "disjoint_behaviors"; "complete_behaviors";
      ];
    h

  let bs_keywords =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s "")
      [
	"valid"; "valid_range"; "lambda" ; "sum" ; "match" ;
	"base_addr" ; "strlen" ; "max" ; "block_length" ;
	"initialized" ; "specified" ;
	"null" ;
	"old";
	"fresh"; "from";
	"nothing";
	"result";
	"let" ; "at";
      ];
    List.iter (fun (s,t) -> Hashtbl.add h s t)
      [
	"forall", "\\ensuremath{\\forall}";
        "exists", "\\ensuremath{\\exists}";
      ];
    h

  let c_types =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [
	"char"; "const"; "double"; "enum"; "extern";
	"float"; "int"; "long"; "register";
	"short"; "signed"; "static"; "struct";
	"typedef"; "union"; "unsigned"; "void"; "volatile"
      ];
    h

  let is_c_keyword s = Hashtbl.mem c_keywords s
  let is_c_keytype s = Hashtbl.mem c_types s
  let bs_keyword s = Hashtbl.find bs_keywords s


  let print_ident =
    let print_ident_char c =
      if c = '_' then print_string "\\_{}" else print_char c
    in
    String.iter print_ident_char

  let begin_tt () =
    print_string "\\begin{flushleft}\\ttfamily\\upshape\\parindent 0pt\n"

  let end_tt () = print_string "\\end{flushleft}"

}

let space = [' ' '\t']
let ident = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*
let beamerspec = ['0'-'9' '-' ',']+
let beameraction = "uncover" | "visible" | "invisible" | "only" | "onslide"

rule ctt = parse
  | "\\0"  { print_string "\\verb|\\0|"; ctt lexbuf }
  | '{'  { print_string "\\{"; ctt lexbuf }
  | '}'  { print_string "\\}"; ctt lexbuf }
  | '#'  { print_string "\\verb|#|"; ctt lexbuf }
  | '_'  { print_string "\\_{}"; ctt lexbuf }
  | '&'  { print_string "\\&{}"; ctt lexbuf }
  | '%'  { print_string "\\%{}"; ctt lexbuf }
  | '\n' { if !in_slashshash then begin
	     print_string "\\end{slshape}";
	     in_slashshash := false ; in_comment := false
	   end;
	   print_string "~\\\\\n"; ctt lexbuf }
  | "&&" as s
      { print_string (if !in_utf8 then utf8 s else "\\&\\&{}"); ctt lexbuf }
  | (">=" | "<=" | ">" | "<" | "!=" | "=="
    | "||" | "!"
    | "==>" | "<==>") as s
      { print_string (if !in_utf8 then utf8 s else s); ctt lexbuf }
  | "\\end{c}" { () }
  | "\\emph{" [^'}''\n']* '}' { print_string (lexeme lexbuf); ctt lexbuf }
  | "\\" beameraction "<" beamerspec ">"
      { print_string (lexeme lexbuf); ctt lexbuf
      }
  | "/*@"
      { print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
	print_string "/*@";
	ctt lexbuf }
  | "/*"
      { print_string "\\begin{slshape}\\rmfamily";
        if !color then print_string "\\color{darkgreen}";
        print_string "/*";
	in_comment := true;
	ctt lexbuf }
  | "*/" { print_string "{}*/\\end{slshape}";
	   in_comment := false;
	   ctt lexbuf }
  | "//@"
      { in_slashshash := true;
	print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
	print_string "//@";
	ctt lexbuf }
  | "//"
      { in_comment := true;
	if !in_slashshash then
          print_string "\\rmfamily"
        else
          print_string "\\begin{slshape}\\rmfamily";
        if !color then print_string "\\color{darkgreen}";
        print_string "//";
        in_slashshash := true;
	ctt lexbuf }
  | eof  { () }
  | '-'  { print_string "$-$"; ctt lexbuf }
  | "::" { print_string ":\\hspace*{-0.1em}:"; ctt lexbuf }
  | " "  { print_string "~"; ctt lexbuf }
  | "\t"  { print_string "~~~~~~~~"; ctt lexbuf } (* tab is 8 spaces *)
  | "[" (ident as s) "]"
      { if !in_comment then print_string "{\\ttfamily " else print_string "[";
	print_ident s;
	if !in_comment then print_string "}" else print_string "]";
	ctt lexbuf
      }
  | ident as s
	{ if not !in_comment && is_c_keyword s then
	      begin
		print_string "\\textbf{"; print_ident s;
		print_string "}"
	      end
	  else (* if is_c_keytype s then begin
		  print_string "{\\color{black}"; print_string s;
		  print_string "}"
		  end else *)
              print_ident s;
	  ctt lexbuf
	}
  | "\\" (ident as s)
      { if not !in_comment then
	  try
	    let t = bs_keyword s in
	    if !in_utf8 && t <> "" then print_string t else
	      begin
		print_string "\\textbf{\\char'134 "; print_ident s;
		print_string "}"
	      end
	  with Not_found -> print_string (lexeme lexbuf)
	else
          print_string (lexeme lexbuf);
	ctt lexbuf
      }
  | _
      { print_string (lexeme lexbuf); ctt lexbuf }

and pp = parse
  | "\\begin{c}" space* "\n"
      { begin_tt (); ctt lexbuf; end_tt (); pp lexbuf }
  | "é" { print_string "\\'e"; pp lexbuf }
  | "è" { print_string "\\`e"; pp lexbuf }
  | "à" { print_string "\\`a"; pp lexbuf }
  | "â" { print_string "\\^a"; pp lexbuf }
  | "ê" { print_string "\\^e"; pp lexbuf }
  | "î" { print_string "\\^{\\i}"; pp lexbuf }
  | "ï" { print_string "\\\"{\\i}"; pp lexbuf }
  | "û" { print_string "\\^u"; pp lexbuf }
  | "ù" { print_string "\\`u"; pp lexbuf }
  | "ö" { print_string "\\\"o"; pp lexbuf }
  | "ô" { print_string "\\^o"; pp lexbuf }
  | eof
      { () }
  | _
      { print_string (lexeme lexbuf); pp lexbuf }

{

  let tex_files = ref []
  let c_files = ref []

  let () = Arg.parse
    [
      "-color", Arg.Set color, "print in color" ;
      "-utf8", Arg.Set in_utf8, "use math symbols" ;
      "-c", Arg.String (fun f ->
			      c_files := f :: !c_files), "read C file <f>" ;
    ]
    (fun f -> tex_files := f :: !tex_files)
    "pp [options] file..."


  let () =
    List.iter (fun f ->
		 let cin = open_in f in
		 let lb = from_channel cin in
		 pp lb; close_in cin)
      !tex_files;
    List.iter (fun f ->
		 let cin = open_in f in
		 let lb = from_channel cin in
		 begin_tt ();
		 ctt lb;
		 end_tt ();
		 close_in cin)
      !c_files;
    exit !unrecognized

}
