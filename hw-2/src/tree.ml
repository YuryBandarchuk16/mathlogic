type op = Conj | Disj | Impl | Comma | Proof;;

type tree = 
	| Binop of op * tree * tree
        | Neg of tree
        | Var of string;;
