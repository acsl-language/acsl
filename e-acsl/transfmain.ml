(* $Id: transfmain.ml,v 1.1 2007-05-29 08:23:19 uid562 Exp $ *)

let main() =
  let lexbuf = Lexing.from_channel stdin in
  print_string "% automatically generated DO NOT EDIT\n";
  Transf.main lexbuf; flush stdout; exit 0;;

Printexc.print main ();;
