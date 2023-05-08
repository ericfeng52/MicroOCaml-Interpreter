open MicroCamlTypes
open Utils
open TokenTypes

(* Provided functions - DO NOT MODIFY *)

(* Matches the next token in the list, throwing an error if it doesn't match the given token *)
let match_token (toks: token list) (tok: token) =
  match toks with
  | [] -> raise (InvalidInputException(string_of_token tok))
  | h::t when h = tok -> t
  | h::_ -> raise (InvalidInputException(
      Printf.sprintf "Expected %s from input %s, got %s"
        (string_of_token tok)
        (string_of_list string_of_token toks)
        (string_of_token h)))

(* Matches a sequence of tokens given as the second list in the order in which they appear, throwing an error if they don't match *)
let match_many (toks: token list) (to_match: token list) =
  List.fold_left match_token toks to_match

(* Return the next token in the token list as an option *)
let lookahead (toks: token list) = 
  match toks with
  | [] -> None
  | h::t -> Some h

(* Return the token at the nth index in the token list as an option*)
let rec lookahead_many (toks: token list) (n: int) = 
  match toks, n with
  | h::_, 0 -> Some h
  | _::t, n when n > 0 -> lookahead_many t (n-1)
  | _ -> None

(* Part 2: Parsing expressions *)

(*Let block*)
let rec parse_expr toks = 
  match lookahead toks with 
    | Some Tok_Let -> parse_let toks
    | _ -> parse_expr2 toks
  
(*HELPER FUNCTIONS START*)
(*Helper function that parses tok_id*)
and parse_ID_helper toks = 
match lookahead toks with
| Some (Tok_ID value) -> let tokenID = match_token toks (Tok_ID value) in (tokenID, value)
| _ -> failwith "helperfunction failure"

(*Parse_or helper function*)
and parse_or_helper toks expr1 = 
  match lookahead toks with
    | Some Tok_Or -> 
      (*Match with the or token*)
      let tok_or = match_token toks Tok_Or in 
      let (tok_expr2, expr2) = parse_or tok_or in (tok_expr2, Binop(Or, expr1, expr2))
    | _ -> (toks, expr1)

(*Parse_and helper function*)
and parse_and_helper toks expr1 = 
  match lookahead toks with
    | Some Tok_And -> 
      (*Match with the and token*)
      let tok_and = match_token toks Tok_And in 
      let (tok_expr2, expr2) = parse_and tok_and in (tok_expr2, Binop(And, expr1, expr2))
    | _ -> (toks, expr1)

(*Recursive helper for parse_let*)
and let_recursive_helper toks = 
  match lookahead toks with
    | Some (Tok_ID id) -> (toks, false)
    | Some Tok_Rec -> let tok_rec = match_token toks Tok_Rec in (tok_rec, true)
    | _ -> raise (InvalidInputException "Parser Fail")

(*Parse equality helper function*)
and parse_equality_helper toks expr1 = 
  match lookahead toks with
    | Some Tok_NotEqual ->
      let (tok_equalityoperator, op) = parse_equalityoperator_helper toks in 
      let (tok_equalityexpr, expr2) = parse_equality tok_equalityoperator in
        (tok_equalityexpr, Binop (op, expr1, expr2))
    | Some Tok_Equal -> 
      let (tok_equalityoperator, op) = parse_equalityoperator_helper toks in 
      let (tok_equalityexpr, expr2) = parse_equality tok_equalityoperator in
        (tok_equalityexpr, Binop (op, expr1, expr2))
    | _ -> (toks, expr1) 

(*Equality operator helper*)
and parse_equalityoperator_helper toks = 
  match lookahead toks with 
    | Some Tok_NotEqual -> let tok_notequal = match_token toks Tok_NotEqual in (tok_notequal, NotEqual) 
    | Some Tok_Equal -> let tok_equal = match_token toks Tok_Equal in (tok_equal, Equal) 
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

    (*Parse_relational helper*)
and parse_relational_helper toks expr1 = 
match lookahead toks with
  | Some Tok_Less | Some Tok_Greater | Some Tok_LessEqual | Some Tok_GreaterEqual -> 
    let (tok_relationaloperator, op) = parse_RO_helper toks in 
    let (tok_relationalexpression, expr2) = parse_relational tok_relationaloperator in
      (tok_relationalexpression, Binop (op, expr1, expr2))
  | _ -> (toks, expr1) 

(*Helper for relational_helper*)
and parse_RO_helper toks = 
match lookahead toks with 
  | Some Tok_Greater -> 
    let tok_greater = match_token toks Tok_Greater in 
      (tok_greater, Greater) 
  | Some Tok_Less -> 
    let tok_less = match_token toks Tok_Less in 
      (tok_less, Less) 
  | Some Tok_GreaterEqual ->
    let tok_greaterequal = match_token toks Tok_GreaterEqual in 
      (tok_greaterequal, GreaterEqual)  
  | Some Tok_LessEqual ->
    let tok_lessequal = match_token toks Tok_Less in 
      (tok_lessequal, LessEqual)  
  (*If the tokens don't fit the grammar, raise an exception*)
  | _ -> raise (InvalidInputException "Parser Fail")

(*Parse_additive helper*)
and parse_additive_next toks expr1 = 
match lookahead toks with
  | Some Tok_Add | Some Tok_Sub -> 
    let (tok_additiveoperator, op) = parse_AO_helper toks in 
    let (tok_additivexpression, expr2) = parse_additive tok_additiveoperator in
      (tok_additivexpression, Binop (op, expr1, expr2))
  | _ -> (toks, expr1) 

(*Helper for parse_additive*)
and parse_AO_helper toks = 
match lookahead toks with 
  | Some Tok_Sub -> let tok_sub = match_token toks Tok_Sub in (tok_sub, Sub) 
  | Some Tok_Add -> let tok_add = match_token toks Tok_Add in (tok_add, Add) 
  (*If the tokens don't fit the grammar, raise an exception*)
  | _ -> raise (InvalidInputException "Parser Fail")

(*Parse_multiplicative helper*)
and parse_multiplicative_helper toks expr1 = 
match lookahead toks with
  | Some Tok_Mult | Some Tok_Div -> 
    let (tok_multoperator, op) = parse_MO_helper toks in 
    let (tok_multexpression, expr2) = parse_multiplicative tok_multoperator in
      (tok_multexpression, Binop (op, expr1, expr2))
  | _ -> (toks, expr1) 

(*Helper for multip_helper*)
and parse_MO_helper toks = 
match lookahead toks with 
  | Some Tok_Div-> let tok_div = match_token toks Tok_Div in (tok_div, Div)
  | Some Tok_Mult-> let tok_mult = match_token toks Tok_Mult in (tok_mult, Mult)  
  (*If the tokens don't fit the grammar, raise an exception*)
  | _ -> raise (InvalidInputException "Parser Fail")

(*Helper for parse_concat*)
and parse_concat_helper toks expr1 = 
match lookahead toks with
  | Some Tok_Concat -> 
    let tok_concatonation = match_token toks Tok_Concat in
    let (tok_concatexpr, expr2) = parse_concat tok_concatonation in (tok_concatexpr, Binop (Concat, expr1, expr2))
  | _ -> (toks, expr1) 

(*Parse_functioncall helper*)
and parse_functioncall_helper toks expr1 = 
  match lookahead toks with
    (*ALL OF THESE MATCHES SHOULD KICK TO PRIMARY EXPRESSION*)
    | Some (Tok_Bool _) ->
      let (tok_primaryexpr, expr2) = parse_primaryexpr toks in 
      (tok_primaryexpr, FunctionCall (expr1, expr2))
    | Some (Tok_Int _) ->
      let (tok_primaryexpr, expr2) = parse_primaryexpr toks in 
      (tok_primaryexpr, FunctionCall (expr1, expr2))
    | Some (Tok_ID _) ->
      let (tok_primaryexpr, expr2) = parse_primaryexpr toks in 
      (tok_primaryexpr, FunctionCall (expr1, expr2))
    | Some (Tok_String _) ->
      let (tok_primaryexpr, expr2) = parse_primaryexpr toks in 
      (tok_primaryexpr, FunctionCall (expr1, expr2))
    | Some Tok_LParen ->
      let (tok_primaryexpr, expr2) = parse_primaryexpr toks in 
        (tok_primaryexpr, FunctionCall (expr1, expr2))
    | _ -> (toks, expr1)

(*END HELPER METHODS*)

(*If Block*)
and parse_expr2 toks =
  match lookahead toks with
  | Some Tok_If -> parse_if toks
  | _ -> parse_expr3 toks

(*If the token doesn't match with Fun, it has to be Or*)
and parse_expr3 toks =
  match lookahead toks with
  | Some Tok_Fun -> parse_function toks
  | _ -> parse_or toks

(*Let block, LetExpr -> let Recursion Tok_ID = Expr in Expr*)
and parse_let toks = 
  match lookahead toks with 
    | Some Tok_Let -> 
      let tok_let = match_token toks Tok_Let in
      let (tok_recursion, rec_function) = let_recursive_helper tok_let in 
      let (tok_id, id) = parse_ID_helper tok_recursion in 
      let tok_equal = match_token tok_id Tok_Equal in
      let (tok_expr1, expr1) = parse_expr tok_equal in 
      let tok_in = match_token tok_expr1 Tok_In in 
      let (tok_expr2, expr2) = parse_expr tok_in in 
        (tok_expr2, Let (id, rec_function, expr1, expr2))
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

(*Function block, FunctionExpr -> fun Tok_ID -> Expr*)
and parse_function toks = 
  match lookahead toks with 
    | Some Tok_Fun -> 
      let tok_function = match_token toks Tok_Fun in 
      let (tok_id, id) = parse_ID_helper tok_function in 
      let tok_arrow = match_token tok_id (Tok_Arrow) in 
      let (tok_expr, expr) = parse_expr tok_arrow in 
        (tok_expr, Fun (id, expr))
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

(*If block, IfExpr -> if Expr then Expr else Expr*)
and parse_if toks = 
  match lookahead toks with 
    | Some Tok_If -> 
      (*If match*)
      let tok_if = match_token toks Tok_If in 
      let (tok_expr1, expr1) = parse_expr tok_if in
      (*Then match*)
      let tok_then = match_token tok_expr1 Tok_Then in 
      let (tok_expr2, expr2) = parse_expr tok_then in
      (*Else match*)
      let tok_else = match_token tok_expr2 Tok_Else in 
      let (tok_expr3, expr3) = parse_expr tok_else in 
        (tok_expr3, If (expr1, expr2, expr3))
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

(* Or block, OrExpr -> AndExpr || OrExpr | AndExpr*)
and parse_or toks = 
  match lookahead toks with 
    (*Stuff that comes before the or*)
    | Some Tok_Not 
    | Some (Tok_Bool _)  -> let (tok_expr, expr) = parse_and toks in parse_or_helper tok_expr expr
    | Some (Tok_Int _) -> let (tok_expr, expr) = parse_and toks in parse_or_helper tok_expr expr
    | Some (Tok_ID _) -> let (tok_expr, expr) = parse_and toks in parse_or_helper tok_expr expr
    | Some (Tok_String _) -> let (tok_expr, expr) = parse_and toks in parse_or_helper tok_expr expr
    | Some Tok_LParen -> let (tok_expr, expr) = parse_and toks in parse_or_helper tok_expr expr
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

  (*And block, AndExpr -> EqualityExpr && AndExpr | EqualityExpr*)
and parse_and toks =
  match lookahead toks with
    (*Stuff that comes before the or*)
    | Some Tok_Not -> let (tok_expr, expr) = parse_equality toks in parse_and_helper tok_expr expr
    | Some (Tok_Bool _) -> let (tok_expr, expr) = parse_equality toks in parse_and_helper tok_expr expr
    | Some (Tok_Int _) -> let (tok_expr, expr) = parse_equality toks in parse_and_helper tok_expr expr
    | Some (Tok_ID _) -> let (tok_expr, expr) = parse_equality toks in parse_and_helper tok_expr expr
    | Some (Tok_String _) -> let (tok_expr, expr) = parse_equality toks in parse_and_helper tok_expr expr
    | Some Tok_LParen -> let (tok_expr, expr) = parse_equality toks in parse_and_helper tok_expr expr
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

(* Equality block, EqualityExpr -> RelationalExpr EqualityOperator EqualityExpr | RelationalExpr *)
and parse_equality toks = 
  match lookahead toks with 
  | Some Tok_Not -> let (tok_expr, expr) = parse_relational toks in parse_equality_helper tok_expr expr
  | Some (Tok_Bool _) -> let (tok_expr, expr) = parse_relational toks in parse_equality_helper tok_expr expr
  | Some (Tok_Int _) -> let (tok_expr, expr) = parse_relational toks in parse_equality_helper tok_expr expr
  | Some (Tok_ID _) -> let (tok_expr, expr) = parse_relational toks in parse_equality_helper tok_expr expr
  | Some (Tok_String _) -> let (tok_expr, expr) = parse_relational toks in parse_equality_helper tok_expr expr
  | Some Tok_LParen -> let (tok_expr, expr) = parse_relational toks in parse_equality_helper tok_expr expr
  (*If the tokens don't fit the grammar, raise an exception*)
  | _ -> raise (InvalidInputException "Parser Fail")


(*Relational Expr, RelationalExpr -> AdditiveExpr RelationalOperator RelationalExpr | AdditiveExpr*)
and parse_relational toks = 
  match lookahead toks with 
  | Some Tok_Not -> let (tok_relationalexpr, expr) = parse_additive toks in parse_relational_helper tok_relationalexpr expr
  | Some (Tok_Bool _) -> let (tok_relationalexpr, expr) = parse_additive toks in parse_relational_helper tok_relationalexpr expr 
  | Some (Tok_Int _) -> let (tok_relationalexpr, expr) = parse_additive toks in parse_relational_helper tok_relationalexpr expr
  | Some (Tok_ID _) -> let (tok_relationalexpr, expr) = parse_additive toks in parse_relational_helper tok_relationalexpr expr
  | Some (Tok_String _) -> let (tok_relationalexpr, expr) = parse_additive toks in parse_relational_helper tok_relationalexpr expr
  | Some Tok_LParen -> let (tok_relationalexpr, expr) = parse_additive toks in parse_relational_helper tok_relationalexpr expr
  (*If the tokens don't fit the grammar, raise an exception*)
  | _ -> raise (InvalidInputException "Parser Fail")

(*Additive Expr, AdditiveExpr -> MultiplicativeExpr AdditiveOperator AdditiveExpr | MultiplicativeExpr
AdditiveOperator -> + | -*)
and parse_additive toks = 
  match lookahead toks with 
  | Some Tok_Not -> let (tok_multiplicativeexpr, expr) = parse_multiplicative toks in parse_additive_next tok_multiplicativeexpr expr
  | Some (Tok_Bool _) -> let (tok_multiplicativeexpr, expr) = parse_multiplicative toks in parse_additive_next tok_multiplicativeexpr expr
  | Some (Tok_Int _) -> let (tok_multiplicativeexpr, expr) = parse_multiplicative toks in parse_additive_next tok_multiplicativeexpr expr
  | Some (Tok_ID _) -> let (tok_multiplicativeexpr, expr) = parse_multiplicative toks in parse_additive_next tok_multiplicativeexpr expr
  | Some (Tok_String _) -> let (tok_multiplicativeexpr, expr) = parse_multiplicative toks in parse_additive_next tok_multiplicativeexpr expr
  | Some Tok_LParen -> let (tok_multiplicativeexpr, expr) = parse_multiplicative toks in parse_additive_next tok_multiplicativeexpr expr
  (*If the tokens don't fit the grammar, raise an exception*)
  | _ -> raise (InvalidInputException "Parser Fail")

(*Mult Expr MultiplicativeExpr -> ConcatExpr MultiplicativeOperator MultiplicativeExpr | ConcatExpr*)
and parse_multiplicative toks = 
  match lookahead toks with 
  | Some Tok_Not -> let (tok_multexpr, expr1) = parse_concat toks in parse_multiplicative_helper tok_multexpr expr1 
  | Some (Tok_Bool _) -> let (tok_multexpr, expr1) = parse_concat toks in parse_multiplicative_helper tok_multexpr expr1
  | Some (Tok_Int _) -> let (tok_multexpr, expr1) = parse_concat toks in parse_multiplicative_helper tok_multexpr expr1
  | Some (Tok_ID _) -> let (tok_multexpr, expr1) = parse_concat toks in parse_multiplicative_helper tok_multexpr expr1
  | Some (Tok_String _) -> let (tok_multexpr, expr1) = parse_concat toks in parse_multiplicative_helper tok_multexpr expr1
  | Some Tok_LParen -> let (tok_multexpr, expr1) = parse_concat toks in parse_multiplicative_helper tok_multexpr expr1
  (*If the tokens don't fit the grammar, raise an exception*)
  | _ -> raise (InvalidInputException "Parser Fail")

(*Concat Expr, UnaryExpr ^ ConcatExpr | UnaryExpr*)
and parse_concat toks = 
  match lookahead toks with 
  | Some Tok_Not -> let (tok_unaryexpr, expr) = parse_unary toks in parse_concat_helper tok_unaryexpr expr
  | Some (Tok_Bool _) -> let (tok_unaryexpr, expr) = parse_unary toks in parse_concat_helper tok_unaryexpr expr
  | Some (Tok_Int _) -> let (tok_unaryexpr, expr) = parse_unary toks in parse_concat_helper tok_unaryexpr expr
  | Some (Tok_ID _) -> let (tok_unaryexpr, expr) = parse_unary toks in parse_concat_helper tok_unaryexpr expr
  | Some (Tok_String _) -> let (tok_unaryexpr, expr) = parse_unary toks in parse_concat_helper tok_unaryexpr expr
  | Some Tok_LParen -> let (tok_unaryexpr, expr) = parse_unary toks in parse_concat_helper tok_unaryexpr expr
  (*If the tokens don't fit the grammar, raise an exception*)
  | _ -> raise (InvalidInputException "Parser Fail")

(*Unary Expr, UnaryExpr -> not UnaryExpr | FunctionCallExpr*)
and parse_unary toks = 
  match lookahead toks with
    (*Match the parameter*)
    | Some (Tok_Bool _) -> parse_functioncall toks
    | Some (Tok_Int _) -> parse_functioncall toks
    | Some (Tok_ID _) -> parse_functioncall toks
    | Some (Tok_String _) -> parse_functioncall toks
    | Some Tok_LParen -> parse_functioncall toks
    (*Match the not after the arrow*)
    | Some Tok_Not -> let tok_not = match_token toks Tok_Not in 
      let (tok_unarexpr, expr) = parse_unary tok_not in (tok_unarexpr, Not (expr))
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

(*FunctionCallExpr, FunctionCallExpr -> PrimaryExpr PrimaryExpr | PrimaryExpr*)
and parse_functioncall toks = 
  match lookahead toks with
    | Some (Tok_Bool _) -> let (tok_primaryexpr, expr) = parse_primaryexpr toks in parse_functioncall_helper tok_primaryexpr expr
    | Some (Tok_Int _) -> let (tok_primaryexpr, expr) = parse_primaryexpr toks in parse_functioncall_helper tok_primaryexpr expr
    | Some (Tok_ID _) -> let (tok_primaryexpr, expr) = parse_primaryexpr toks in parse_functioncall_helper tok_primaryexpr expr
    | Some (Tok_String _) -> let (tok_primaryexpr, expr) = parse_primaryexpr toks in parse_functioncall_helper tok_primaryexpr expr
    | Some Tok_LParen -> let (tok_primaryexpr, expr) = parse_primaryexpr toks in parse_functioncall_helper tok_primaryexpr expr
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

(*PrimaryExpr, PrimaryExpr -> Tok_Int | Tok_Bool | Tok_String | Tok_ID | ( Expr )*)
and parse_primaryexpr toks = 
  match lookahead toks with
      (*Match Boolean*)
    | Some Tok_Bool boolean -> let tok_boolean = match_token toks (Tok_Bool boolean) in (tok_boolean, Value (Bool boolean))
      (*Match Int*)
    | Some Tok_Int value -> let tok_value = match_token toks (Tok_Int value) in (tok_value, Value (Int value))
      (*Match ID*)
    | Some Tok_ID tag -> let tok_id = match_token toks (Tok_ID tag) in (tok_id, ID tag)
      (*Match String*)
    | Some Tok_String str -> let tok_string = match_token toks (Tok_String str) in (tok_string, Value (String str))
      (*Match Left and Right Parens*)
    | Some Tok_LParen -> let tok_leftparen = match_token toks Tok_LParen in
      (*Match for contents in between parens*)
      let (tok_expressioninbetween, expr) = parse_expr tok_leftparen in 
      let tok_rightparen = match_token tok_expressioninbetween Tok_RParen in (tok_rightparen, expr)
    (*If the tokens don't fit the grammar, raise an exception*)
    | _ -> raise (InvalidInputException "Parser Fail")

(* Part 3: Parsing mutop *)
let rec parse_mutop toks = 
  match lookahead toks with
    (*Match with def*)
  | Some Tok_Def -> let tok_def = match_token toks Tok_Def in
    let (tok_id, id) = parse_ID_helper tok_def in
    let tok_equal = match_token tok_id Tok_Equal in
    let (tok_expr, expr) = parse_expr tok_equal in
    let tok_doublesemi = match_token tok_expr Tok_DoubleSemi in
    (tok_doublesemi, Def (id, expr))
    (*Match with doublesemi*)
  | Some Tok_DoubleSemi -> let tok = match_token toks Tok_DoubleSemi in (tok, NoOp)
  | _ -> let (tok_expr, expr) = parse_expr toks in
    let tok_doublesemi = match_token tok_expr Tok_DoubleSemi in
    (tok_doublesemi, Expr (expr))
    

