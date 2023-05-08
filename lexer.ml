open TokenTypes

(* Part 1: Lexer - IMPLEMENT YOUR CODE BELOW *)

(*Equality and parens*)
let tok_lparen = Str.regexp "("
let tok_rparen = Str.regexp ")"
let tok_equal = Str.regexp "="
let tok_notequal = Str.regexp "<>"
let tok_greater = Str.regexp ">"
let tok_less = Str.regexp "<"
let tok_greaterequal = Str.regexp ">="
let tok_lessequal = Str.regexp "<="

(*Logic*)
let tok_or = Str.regexp "||"
let tok_and = Str.regexp "&&"
let tok_not = Str.regexp "not"
let tok_if = Str.regexp "if"
let tok_then = Str.regexp "then"
let tok_else = Str.regexp "else"

(*Math*)
let tok_add = Str.regexp "+"
let tok_sub = Str.regexp "-"
let tok_mult = Str.regexp "*"
let tok_div = Str.regexp "/"
let tok_concat = Str.regexp {|\^|}

(*Keywords and such*)
let tok_let = Str.regexp "let"
let tok_def = Str.regexp "def"
let tok_in = Str.regexp "in"
let tok_rec = Str.regexp "rec"
let tok_fun = Str.regexp "fun"
let tok_arrow = Str.regexp "->"
let tok_doublesemi = Str.regexp ";;"

(*Weird Tokens*)
let whitespaceregex = Str.regexp "[\t\n ]"
let tok_true = Str.regexp "true"
let tok_false = Str.regexp "false"
let tok_intnormal = Str.regexp "[0-9]+"
let tok_int_parens = Str.regexp "(-[0-9]+)"
let tok_string = Str.regexp "\"[^\"]*\""
let tok_stringid = Str.regexp "[a-zA-Z][a-zA-Z0-9]*"


let tokenize input = 
    (*Recursive tokenizing on the str*)
    let rec tokenize_helper curr_index str = 
        if curr_index >= String.length str then [] 

        else if (Str.string_match tok_equal str curr_index) then
            Tok_Equal::(tokenize_helper (curr_index + 1) str)

        else if (Str.string_match tok_notequal str curr_index) then
            Tok_NotEqual::(tokenize_helper (curr_index + 2) str)

        else if (Str.string_match tok_greater str curr_index) then
            Tok_Greater::(tokenize_helper (curr_index + 1) str)

        else if (Str.string_match tok_less str curr_index) then
            Tok_Less::(tokenize_helper (curr_index + 1) str)

        else if (Str.string_match tok_greaterequal str curr_index) then
            Tok_GreaterEqual::(tokenize_helper (curr_index + 2) str)

        else if (Str.string_match tok_lessequal str curr_index) then
            Tok_LessEqual::(tokenize_helper (curr_index + 2) str)

        else if (Str.string_match tok_or str curr_index) then
            Tok_Or::(tokenize_helper (curr_index + 2) str)

        else if (Str.string_match tok_and str curr_index) then
            Tok_And::(tokenize_helper (curr_index + 2) str)

        else if (Str.string_match tok_not str curr_index) then
            Tok_Not::(tokenize_helper (curr_index + 3) str)

        else if (Str.string_match tok_if str curr_index) then
            Tok_If::(tokenize_helper (curr_index + 2) str)

        else if (Str.string_match tok_then str curr_index) then
            Tok_Then::(tokenize_helper (curr_index + 4) str)

        else if (Str.string_match tok_else str curr_index) then
            Tok_Else::(tokenize_helper (curr_index + 4) str)

        else if (Str.string_match tok_arrow str curr_index) then
            Tok_Arrow::(tokenize_helper (curr_index + 2) str)
            
        else if (Str.string_match tok_add str curr_index) then
            Tok_Add::(tokenize_helper (curr_index + 1) str)

        else if (Str.string_match tok_sub str curr_index) then
            Tok_Sub::(tokenize_helper (curr_index + 1) str)

        else if (Str.string_match tok_mult str curr_index) then
            Tok_Mult::(tokenize_helper (curr_index + 1) str)

        else if (Str.string_match tok_div str curr_index) then
            Tok_Div::(tokenize_helper (curr_index + 1) str)

        else if (Str.string_match tok_concat str curr_index) then
            Tok_Concat::(tokenize_helper (curr_index + 1) str)

        else if (Str.string_match tok_let str curr_index) then
            Tok_Let::(tokenize_helper (curr_index + 3) str)  

        else if (Str.string_match tok_def str curr_index) then
            Tok_Def::(tokenize_helper (curr_index + 3) str) 

        else if (Str.string_match tok_in str curr_index) then
            Tok_In::(tokenize_helper (curr_index + 2) str)

        else if (Str.string_match tok_rec str curr_index) then
            Tok_Rec::(tokenize_helper (curr_index + 3) str)

        else if (Str.string_match tok_fun str curr_index) then
            Tok_Fun::(tokenize_helper (curr_index + 3) str)

        (*Boolean Tokens*)
        else if (Str.string_match tok_true str curr_index) then
            (Tok_Bool true)::(tokenize_helper (curr_index + 4) str) 

        else if (Str.string_match tok_false str curr_index) then
            (Tok_Bool false)::(tokenize_helper (curr_index + 5) str)

        (*Int Tokens*)
        else if (Str.string_match tok_intnormal str curr_index) then
            let temp = Str.matched_string str in 
                (Tok_Int (int_of_string temp))::(tokenize_helper (curr_index + (String.length temp)) str)

        else if (Str.string_match tok_int_parens str curr_index) then
            let temp = Str.matched_string str in let strlen = String.length temp in
            let integer = String.sub temp 1 (strlen - 2) in
                (Tok_Int (int_of_string integer))::(tokenize_helper (curr_index + strlen) str)

        (*String Tokens*)
        else if (Str.string_match tok_string str curr_index) then
            let temp = Str.matched_string str in let strlen = String.length temp in
                (Tok_String (String.sub temp 1 (strlen - 2)))::(tokenize_helper (curr_index + strlen) str)

        else if (Str.string_match tok_stringid str curr_index) then
            let temp = Str.matched_string str in let strlen = String.length temp in
                (Tok_ID temp)::(tokenize_helper (curr_index + strlen) str)

            else if (Str.string_match tok_lparen str curr_index) then
                Tok_LParen::(tokenize_helper (curr_index + 1) str)
    
            else if (Str.string_match tok_rparen str curr_index) then
                Tok_RParen::(tokenize_helper (curr_index + 1) str)
        
        (*Double Semi and Whitespace Checks*)
        else if (Str.string_match tok_doublesemi str curr_index) then
            Tok_DoubleSemi::(tokenize_helper (curr_index+2) str)

        else if (Str.string_match whitespaceregex str curr_index) then
            tokenize_helper (curr_index+1) str
        else 
            raise (InvalidInputException "Lexing error")

    in tokenize_helper 0 input;;