open MicroCamlTypes
open Utils

exception TypeError of string
exception DeclareError of string
exception DivByZeroError 

(* Provided functions - DO NOT MODIFY *)

(* Adds mapping [x:v] to environment [env] *)
let extend env x v = (x, ref v)::env

(* Returns [v] if [x:v] is a mapping in [env]; uses the
   most recent if multiple mappings for [x] are present *)
let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then !value else lookup t x

(* Creates a placeholder mapping for [x] in [env]; needed
   for handling recursive definitions *)
let extend_tmp env x = (x, ref (Int 0))::env

(* Updates the (most recent) mapping in [env] for [x] to [v] *)
let rec update env x v =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then (value := v) else update t x v
        
(* Part 1: Evaluating expressions *)

(* Evaluates MicroCaml expression [e] in environment [env],
   returning a value, or throwing an exception on error *)
   let rec update env x v =
    match env with
    | [] -> raise (DeclareError ("Unbound variable " ^ x))
    | (var, value)::t -> if x = var then (value := v) else update t x v
          
  (* Part 1: Evaluating expressions *)
  
  (* Evaluates MicroCaml expression [e] in environment [env],
     returning a value, or throwing an exception on error *)
  let rec eval_expr env e = 
    match e with

    (*Return the value that was piped in*)
    |Value value -> value

    (*An identifier evaluates to whatever value it is mapped to by the environment. 
    Should raise a DeclareError if the identifier has no binding*)
    |ID id -> lookup env id

    (*The unary not operator operates only on booleans and produces a Bool containing
    the negated value of the contained expression*)
    |Not var -> let var' = match (eval_expr env var) with
      |Bool true -> Bool false
      |Bool false -> Bool true
      |_-> raise (TypeError("Type error")) in var' 

    (*Arithmetic operators work on integers; if either argument evaluates to a 
    non-Int, a TypeError should be raised. An attempt to divide by zero should 
    raise a DivByZeroError exception*)
    |Binop (Add,e1,e2) -> let e1' = match (eval_expr env e1) with
      |Int firstInt -> firstInt (*Make sure firstInt is type int*)
      |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
      |Int secondInt -> secondInt (*Make sure firstInt is type int*)
      |_-> raise (TypeError("Type error")) in let e3 = e1' + e2' in (Int (e3))
  
    |Binop (Sub,e1,e2) -> let e1' = match (eval_expr env e1) with
      |Int firstInt -> firstInt (*Make sure firstInt is type int*)
      |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
      |Int secondInt -> secondInt (*Make sure firstInt is type int*)
      |_-> raise (TypeError("Type error")) in let e3 = e1' - e2' in (Int (e3))
  
    |Binop (Mult,e1,e2) -> let e1' = match (eval_expr env e1) with
      |Int firstInt -> firstInt (*Make sure firstInt is type int*)
      |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
      |Int secondInt -> secondInt (*Make sure firstInt is type int*)
      |_-> raise (TypeError("Type error")) in let e3 = e1' * e2' in (Int (e3))
  
    (*Divide by zero case to account for*)
    |Binop(Div,e1,e2) -> let e1' = match (eval_expr env e1) with
      |Int firstInt -> firstInt (*Make sure firstInt is type int*)
      |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
      |Int secondInt -> let flag = (secondInt == 0) in if flag then raise (DivByZeroError) else secondInt
      |_-> raise (TypeError("Type error")) in let e3 = e1' / e2' in (Int (e3))
    
    (*Binary Operators*)
    |Binop(Greater, e1, e2) -> let e1' = match (eval_expr env e1) with
        |Int firstInt -> firstInt
        |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
        |Int secondInt -> secondInt
        |_-> raise (TypeError("Type error")) in let e3 = e1' > e2' in (Bool (e3))
  
    |Binop(Less, e1, e2) -> let e1' = match (eval_expr env e1) with
        |Int firstInt -> firstInt
        |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
        |Int secondInt -> secondInt
        |_-> raise (TypeError("Type error")) in let e3 = e1' < e2' in (Bool (e3))

    |Binop(GreaterEqual, e1, e2) -> let e1' = match (eval_expr env e1) with
        |Int firstInt -> firstInt
        |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
        |Int secondInt -> secondInt
        |_-> raise (TypeError("Type error")) in let e3 = ((e1' > e2') && (e1' == e2')) in (Bool (e3))

    |Binop(LessEqual, e1, e2) -> let e1' = match (eval_expr env e1) with
        |Int firstInt -> firstInt
        |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
        |Int secondInt -> secondInt
        |_-> raise (TypeError("Type error")) in let e3 = ((e1' < e2') && (e1' == e2')) in (Bool (e3))
  
    (*For concat, make sure both expressions are strings*)
    |Binop(Concat, e1, e2) -> let e1' = match (eval_expr env e1) with
        |String firstStr -> firstStr
        |_-> raise (TypeError("Type error")) in let e2' = match (eval_expr env e2) with
        |String secondStr -> secondStr
        |_-> raise (TypeError("Type error")) in let e3 = (e1' ^ e2') in (String (e3)) 
    
    (*3 cases, Ints, Strings, and Booleans for equal and notequal*)
    |Binop(Equal, e1, e2) -> 
      let e3 = match (eval_expr env e1), (eval_expr env e2) with 
        |(Int firstInt, Int secondInt) -> if firstInt == secondInt then (Bool (true)) else (Bool (false))
        |(String firstString, String secondString) -> if firstString == secondString then (Bool (true)) else (Bool (false))
        |(Bool firstBool, Bool secondBool) -> if ((firstBool == true && secondBool == true) || (firstBool == false && secondBool == false)) 
          then (Bool (true)) else (Bool (false))
        |_-> raise (TypeError("Type error")) in e3

    |Binop(NotEqual, e1, e2)-> 
      let e3 = match (eval_expr env e1), (eval_expr env e2) with 
        |(Int firstInt, Int secondInt) -> if firstInt != secondInt then (Bool (true)) else (Bool (false))
        |(String firstString, String secondString) -> if firstString != secondString then (Bool (true)) else (Bool (false))
        |(Bool firstBool, Bool secondBool) -> if ((firstBool == true && secondBool == true) || (firstBool == false && secondBool == false)) 
          then (Bool (false)) else (Bool (true))
        |_-> raise (TypeError("Type error")) in e3

    (*Or and And, have to match bools*)
    |Binop(Or, e1, e2)-> 
      let e3 = match (eval_expr env e1), (eval_expr env e2) with
          | (Bool true, Bool true) -> (Bool (true))
          | (Bool true, Bool false) -> (Bool (true))
          | (Bool false, Bool true) -> (Bool (true))
          | (Bool false, Bool false) -> (Bool (false))
          |_-> raise (TypeError("Type error")) in e3

    |Binop (And, e1, e2)-> 
      let e3 = match (eval_expr env e1), (eval_expr env e2) with
          | (Bool true, Bool true) -> (Bool (true))
          | (Bool true, Bool false) -> (Bool (false))
          | (Bool false, Bool true) -> (Bool (false))
          | (Bool false, Bool false) -> (Bool (false))
          |_-> raise (TypeError("Type error")) in e3

    (*If true return e2 bit if false return e3 bit*)
    |If(e1, e2, e3) -> let e4 = match (eval_expr env e1) with
          |Bool true-> (eval_expr env e2)
          |Bool false-> (eval_expr env e3)
          |_-> raise (TypeError("Type error")) in e4

    (*The let has a boolean indicating whether or not the bound variable is referenced in its own def*)
    |Let(e1, e2, e3, e4) -> if(e2 == true) then 
      let e1' = extend_tmp env e1 in
      let e2' = eval_expr e1' e3 in
      let _ = update e1' e1 e2' in 
      let e3' = eval_expr e1' e4 in e3' 
      else let e1' = eval_expr env e3 in 
      (eval_expr(extend env e1 e1')e4)

    |Fun(e1 ,e2) -> (Closure(env, e1, e2))

    |FunctionCall(e1, e2) -> let e3 = match (eval_expr env e1) with 
      |Closure (env1, e1', e2') -> let e4 = extend env1 e1' (eval_expr env e2) in (eval_expr e4 e2')
      |_-> raise (TypeError("Type error")) in e3

(* Part 2: Evaluating mutop directive *)
let eval_mutop env m = 
  match m with
  |NoOp -> (env, None)
  |Expr(e1) -> let e1' = eval_expr env e1 in (env, Some e1')
  |Def(e1, e2) -> let e3 = extend_tmp env e1 in
                let e2' = eval_expr e3 e2 in
                let _ = update e3 e1 e2' in
                (e3, Some e2')