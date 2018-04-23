type token =
  | VAR of (string)
  | IMPL
  | AND
  | OR
  | NOT
  | PROOF
  | COMMA
  | OPEN
  | CLOSE
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.tree
