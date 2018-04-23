type token =
  | VAR of (string)
  | IMPL
  | AND
  | OR
  | NOT
  | OPEN
  | CLOSE
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.tree
