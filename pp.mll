
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
	"default"; "do"; "else"; "for"; "goto"; "if"; "then" ; 
	"return"; "switch"; "while";
	"class" ; "interface" ; "ensures";
	"public" ; "private" ; "static" ; "struct" ;
	"typedef"; "union";
	"throws" ; "extends" ; "implements" ; "reads" ;
	"requires"; "assumes" ; "invariant"; "representation";
	"decreases" ; "loop" ; "variant" ; "data" ; "strong" ;
	"breaks"; "continues"; "returns"; "assigns";
        "modifiable" ; "signals" ; "global";
	"logic" ; "type" ; "predicate" ; "axiom"; "lemma" ;
	"axiomatic" ; "inductive" ;
	"exit_behavior" ; "behavior" ; "model"; "ghost"; "terminates";
        "disjoint"; "behaviors"; "complete";
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
	"let" ; "at"; "true"; "false"; "numof"
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
    print_string "\\begin{flushleft}\\ttfamily\\upshape\\begin{latexonly}\
                  \\parindent 0pt\\end{latexonly}\n"

  let end_tt () = print_string "\\end{flushleft}"

  let cout = ref []

  let seen_files = Hashtbl.create 7

  let seen_file s =
    Hashtbl.mem seen_files s || (Hashtbl.add seen_files s (); false)

  let c_output s =
    let filename = Str.regexp "[a-zA-Z_0-9.-]+" in
    try
      let pos = ref 0 in
      while true do
        let _ = Str.search_forward filename s !pos in
        let file = Str.matched_string s in
        let flag = if seen_file file then Open_append else Open_trunc in
        pos:=Str.match_end () + 1;
        try
          cout:=
            (open_out_gen [Open_wronly; flag; Open_creat] 0o644 file) :: !cout
        with Sys_error s ->
          Printf.eprintf "Warning: could not open file %s:\n%s\n" file s
      done;
    with Not_found -> ()

  let out_c_lexeme s =
    List.iter (fun x -> output_string x s) !cout

  let close_c_output () =
    List.iter (fun x -> flush x; close_out x) !cout;
    cout := []
}

let space = [' ' '\t']
let ident = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*
let filename = ['a'-'z' 'A'-'Z' '_' '0'-'9' '.' '-']+
let beamerspec = ['0'-'9' '-' ',''a'-'z''@']+
let beameraction = "uncover" | "visible" | "invisible" | "only" | "onslide" | "action"

let c_files =
  (space* '[' space* filename (space* ',' space* filename)* space* ']')? space*

rule ctt = parse
  | "\\0"  { print_string "\\verb|\\0|"; out_c_lexeme "\\0"; ctt lexbuf }
      (* At last, one use of trigraphs: it let us insert raw braces in
         the latex output
       *)
  | "??<" { print_string "{"; ctt lexbuf }
  | "??>" { print_string "}"; ctt lexbuf }
  | '{'  { print_string "\\{"; out_c_lexeme "{"; ctt lexbuf }
  | '}'  { print_string "\\}"; out_c_lexeme "}"; ctt lexbuf }
  | '#'  { print_string "\\verb|#|"; out_c_lexeme "#"; ctt lexbuf }
  | '_'  { print_string "\\_{}"; out_c_lexeme "_"; ctt lexbuf }
  | '&'  { print_string "\\&{}"; out_c_lexeme "&"; ctt lexbuf }
  | '%'  { print_string "\\%{}"; out_c_lexeme "%"; ctt lexbuf }
  | '\n' { if !in_slashshash then begin
	     print_string "\\end{slshape}";
	     in_slashshash := false ; in_comment := false
	   end;
	   print_string "~\\\\\n";
           out_c_lexeme "\n";
           ctt lexbuf }
  | "&&" as s
      { print_string (if !in_utf8 then utf8 s else "\\&\\&{}");
        out_c_lexeme s;
        ctt lexbuf }
  | (">=" | "<=" | ">" | "<" | "!=" | "=="
    | "||" | "!"
    | "==>" | "<==>") as s
      { print_string (if !in_utf8 then utf8 s else s);
        out_c_lexeme s; ctt lexbuf }
  | "\\end{c}" { () }
  | "\\emph{" [^'}''\n']* as s '}' { print_string (lexeme lexbuf);
                                     out_c_lexeme s;
                                     ctt lexbuf }
  | "\\" beameraction "<" beamerspec ">"
      { print_string (lexeme lexbuf); ctt lexbuf }
  | "/*@"
      { print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
	print_string "/*@";
        out_c_lexeme "/*@";
	ctt lexbuf }
  | "/*"
      { print_string "\\begin{slshape}\\rmfamily";
        if !color then print_string "\\color{darkgreen}";
        print_string "/*";
        out_c_lexeme "/*";
	in_comment := true;
	ctt lexbuf }
  | "*/" { print_string "{}*/\\end{slshape}";
	   in_comment := false;
           out_c_lexeme "*/";
	   ctt lexbuf }
  | "//@"
      { in_slashshash := true;
	print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
	print_string "//@";
        out_c_lexeme "//@";
	ctt lexbuf }
  | "//"
      { in_comment := true;
	if !in_slashshash then
          print_string "\\rmfamily"
        else
          print_string "\\begin{slshape}\\rmfamily";
        if !color then print_string "\\color{darkgreen}";
        print_string "//";
        out_c_lexeme "//";
        in_slashshash := true;
	ctt lexbuf }
  | "//" space* "NOPP-BEGIN" space* "\n"  { nopp lexbuf }
  | eof  { () }
  | '-'  { print_string "$-$"; out_c_lexeme "-"; ctt lexbuf }
  | "::" { print_string ":\\hspace*{-0.1em}:"; out_c_lexeme "::"; ctt lexbuf }
  | " "  { print_string "~"; out_c_lexeme " "; ctt lexbuf }
  | "\t"  { print_string "~~~~~~~~"; out_c_lexeme "\t"; ctt lexbuf }
      (* tab is 8 spaces *)
  | "[" (ident as s) "]"
      { if !in_comment then print_string "{\\ttfamily " else print_string "[";
	print_ident s;
	if !in_comment then print_string "}" else print_string "]";
	out_c_lexeme (lexeme lexbuf);
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
          out_c_lexeme s;
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
        out_c_lexeme (lexeme lexbuf);
	ctt lexbuf
      }
  | _
      { print_string (lexeme lexbuf); out_c_lexeme (lexeme lexbuf); ctt lexbuf }

and nopp = parse
    "//" space* "NOPP-END" space* "\n" { ctt lexbuf }
  | eof { () }
  | _ { nopp lexbuf}

and pp = parse
  | "\\begin{c}" (c_files as s) "\n"
      { c_output s; begin_tt (); ctt lexbuf;
        end_tt (); close_c_output(); pp lexbuf }
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
