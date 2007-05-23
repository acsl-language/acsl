
{
  open Lexing 

  let color = ref false
   
  let in_comment = ref false
  let in_slashshash = ref false

  let ocaml_keywords = 
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [ 
	"fun"; "match"; "with"; "begin"; 
	"end"; "try"; "as"; "let"; "rec"; "in";
	"function"; "if"; "private"; "then"; "else"; "sig"; "val"; 
	"type"; "module";
	"while"; "do"; "done"; "for"; "struct"; "to"; "raise"
      ];
    h

  let coq_keywords = 
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [ 
	"Inductive"; "Fixpoint" ; "Definition" ; "Lemma" ;
	"forall" ; "exists" ; "match" ; "with" ; "end" ; "as" ;
	"if" ; "then" ; "else" ;
      ];
    h

  let c_keywords = 
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [ 
	"auto"; "break"; "case"; "continue"; "new";
	"default"; "do"; "else"; "for"; "goto"; "if";
	"return"; "switch"; "while"; 
	"class" ; "interface" ; 
	"public" ; "private" ; "static" ; 
	"throws" ; "extends" ; "implements" ; "reads" ;
	"requires"; "invariant"; "representation";
	"ensures" ; "assigns"; "modifiable" ; "signals" ;
	"logic" ; "type" ; "predicate" ; "axiom";
	"normal_behavior" ; "behavior" ; "model";
      ];
    h

  let bs_keywords = 
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [ 
	"valid"; "forall"; "old" ; "fresh" ; "nothing" ; "result"
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

  let is_ocaml_keyword s = Hashtbl.mem ocaml_keywords s
  let is_coq_keyword s = Hashtbl.mem coq_keywords s
  let is_c_keyword s = Hashtbl.mem c_keywords s 
  let is_c_keytype s = Hashtbl.mem c_types s 
  let is_bs_keyword s = Hashtbl.mem bs_keywords s 

  let print_ident =
    let print_ident_char c = 
      if c = '_' then print_string "\\_{}" else print_char c
    in
    String.iter print_ident_char

}

let space = [' ' '\t']
let ident = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*
let beamerspec = ['0'-'9' '-' ',']+
let beameraction = "uncover" | "visible" | "invisible" | "only" | "onslide"

rule ktt = parse
  | '{'  { print_string "\\{"; ktt lexbuf }
  | '}'  { print_string "\\}"; ktt lexbuf }
  | '#'  { print_string "\\diese{}"; ktt lexbuf }
  | '_'  { print_string "\\_{}"; ktt lexbuf }
  | '&'  { print_string "\\&{}"; ktt lexbuf }
  | '%'  { print_string "\\%{}"; ktt lexbuf }
  | '\n' { if !in_slashshash then begin
	     print_string "\\end{slshape}"; 
	     in_slashshash := false ; in_comment := false
	   end;
	   print_string "~\\\\\n"; ktt lexbuf }
(*
  | ">=" { print_string "\\ensuremath{\\geq}"; ktt lexbuf }
  | "<=" { print_string "\\ensuremath{\\leq}"; ktt lexbuf }
  | ">" { print_string "\\ensuremath{>}"; ktt lexbuf }
  | "<" { print_string "\\ensuremath{<}"; ktt lexbuf }
  | "<>" { print_string "\\ensuremath{\\neq}"; ktt lexbuf }
  | "==" { print_string "\\ensuremath{=}"; ktt lexbuf }
  | "->" { print_string "\\ensuremath{\\rightarrow}"; ktt lexbuf }
  | "==>" { print_string "\\ensuremath{\\Rightarrow}"; ktt lexbuf }
  | "<==>" { print_string "\\ensuremath{\\Leftrightarrow}"; ktt lexbuf }
*)
  | "\\end{c}" { () }
  | "\\emph{" [^'}''\n']* '}' { print_string (lexeme lexbuf); ktt lexbuf }
  | "\\" beameraction "<" beamerspec ">" 
      { print_string (lexeme lexbuf); ktt lexbuf 
      }
  | "/*@" 
      { print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
	print_string "/*@"; 
	ktt lexbuf }
  | "/*" 
      { print_string "\\begin{slshape}\\rmfamily\\color{darkgreen}/*"; 
	in_comment := true;
	ktt lexbuf }
  | "*/" { print_string "*/\\end{slshape}"; 
	   in_comment := false;
	   ktt lexbuf }
  | "//@" 
      { in_slashshash := true; 
	print_string "\\begin{slshape}";
	if !color then print_string "\\color{blue}";
	print_string "/*@"; 
	ktt lexbuf }
  | "//" 
      { in_comment := true; 
	in_slashshash := true; 
	print_string "//\\begin{slshape}\\rmfamily\\color{darkgreen}";
	ktt lexbuf }
  | eof  { () }
  | '-'  { print_string "$-$"; ktt lexbuf }
  | "'a" { print_string "\\ensuremath{\\alpha}"; ktt lexbuf }
  | "::" { print_string ":\\hspace*{-0.1em}:"; ktt lexbuf }
  | " "  { print_string "~"; ktt lexbuf }
  | "[" (ident as s) "]" 
      { if !in_comment then print_string "{\\ttfamily " else print_string "[";
	print_ident s;
	if !in_comment then print_string "}" else print_string "]";
	ktt lexbuf
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
	  ktt lexbuf 
	}
  | "\\" (ident as s)
      { if not !in_comment && is_bs_keyword s then 
	    begin
	      print_string "\\textbf{\\char'134 "; print_ident s;
	      print_string "}"
	    end 
	else
            print_string (lexeme lexbuf);
	ktt lexbuf 
      }
  | _   
      { print_string (lexeme lexbuf); ktt lexbuf }

and coqtt = parse
  | "\\end{coq}" { () }
  | '{'  { print_string "\\{"; coqtt lexbuf }
  | '}'  { print_string "\\}"; coqtt lexbuf }
  | '\n' { print_string "~\\\\\n"; coqtt lexbuf }
  | ">=" { print_string "\\ensuremath{\\geq}"; coqtt lexbuf }
  | "<=" { print_string "\\ensuremath{\\leq}"; coqtt lexbuf }
  | ">" { print_string "\\ensuremath{>}"; coqtt lexbuf }
  | "<" { print_string "\\ensuremath{<}"; coqtt lexbuf }
  | "<>" { print_string "\\ensuremath{\\neq}"; coqtt lexbuf }
  | "->" { print_string "\\ensuremath{\\rightarrow}"; coqtt lexbuf }
  | "forall" { print_string "\\ensuremath{\\forall}"; coqtt lexbuf }
  | "exists" { print_string "\\ensuremath{\\exists}"; coqtt lexbuf }
  | "/\\" { print_string "\\ensuremath{\\land}"; coqtt lexbuf }
  | "\\/" { print_string "\\ensuremath{\\lor}"; coqtt lexbuf }
  | '_'  { print_string "\\_{}"; coqtt lexbuf }
  | '|'  { print_string "\\textbf{|}"; coqtt lexbuf }
  | "=>"  { print_string "\\ensuremath{\\Rightarrow}"; coqtt lexbuf }
  | "Z"  { print_string "\\ensuremath{\\mathbb{Z}}"; coqtt lexbuf }
  | "\\" beameraction "<" beamerspec ">" 
      { print_string (lexeme lexbuf); coqtt lexbuf 
      }
  | "(*" 
      { print_string "\\begin{slshape}\\color{darkgreen}(*"; 
	in_comment := true;
	coqtt lexbuf }
  | "*)" { print_string "*)\\end{slshape}"; 
	   in_comment := false;
	   coqtt lexbuf }
  | eof  { () }
  | " "  { print_string "~"; coqtt lexbuf }
  | "[" (ident as s) "]" 
      { if !in_comment then print_string "{\\ttfamily ";
	print_ident s;
	if !in_comment then print_string "}";
	coqtt lexbuf
      }
  | ident as s
      { if not !in_comment && is_coq_keyword s then 
	    begin
	      print_string "\\textbf{"; print_ident s;
	      print_string "}"
	    end 
	else 
            print_ident s;
	coqtt lexbuf 
      }
  | _   { print_string (lexeme lexbuf); coqtt lexbuf }

and pp = parse
  | "\\begin{c}" space* "\n" 
      { print_string "\\begin{flushleft}\\ttfamily\\parindent 0pt\n"; 
	ktt lexbuf;
	print_string "\\end{flushleft}";
	pp lexbuf }
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
  let f = Sys.argv.(1)
  (*let () = slides := (String.length f > 6 && String.sub f 0 7 = "slides-")*)
  let cin = open_in f
  let lb = from_channel cin
  let _ = pp lb
}
