(*+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*)

(* tipos da linguagem L1 *)

type tipo =
    TyInt
  | TyBool
  | TyFn of tipo * tipo 
  | TyUnit
  | TyRef of tipo
  
type ident = string 

type op = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

(* expressões da linguagem L2 *)
type expr =
  | Num of int
  | Var of ident
  | Bcte of bool
  | Binop of op * expr * expr 
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr 
  
(* Extensões do trabalho *) 
  | Skip
  | New of expr 
  | Asg of expr * expr
  | Dref of expr 
  | Seq of expr * expr
  | Whl of expr * expr
  
(* Ambiente de tipos *) 
type tenv = (ident * tipo) list

(* Valores *) 
type value =
    VNum of int
  | VBool of bool 
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv 
  | VMemoryAddress of int 
  | VUnit
and renv = (ident * value) list 

(* Busca e atualização nos ambientes (polimórficas) *)
let rec lookup a k  =
  match a with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k 
       
let  update a k i = (k,i) :: a  

(* Função que converte tipo para string *)
let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyUnit -> "unit"
  | TyRef t1 -> "(" ^ (ttos t1) ^ " ref)"


(* Função que converte valor para string *)
let rec vtos (v: value) : string =
  match v with
    VNum n -> string_of_int n
  | VBool b -> string_of_bool b 
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"
  | VUnit -> "()"
  | VMemoryAddress n -> ("Adr: " ^ string_of_int n)
  
(* Exceções que não devem ocorrer  *) 
exception BugParser
exception BugTypeInfer 

(* Exceções para usuário *)
exception TypeError of string 


(*++++++++++++++++++++++++++++++++++++++++++*)
(*         		    TYPEINFER               *)
(*++++++++++++++++++++++++++++++++++++++++++*)

let rec typeinfer (tenv:tenv) (e:expr) : tipo =
  match e with
  | Num _ -> TyInt
  | Var x ->
      let x' = lookup tenv x in 
      (match x' with
         Some t -> t
       | None -> raise (TypeError ("Variavel nao declarada:" ^ x)))
  | Bcte _ -> TyBool 
  | Binop(oper,e1,e2) ->  
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in 
      (match (t1,t2) with
         (TyInt, TyInt) -> 
           (match oper with 
              Sum | Sub | Mult         ->  TyInt
            | Eq | Gt | Lt | Geq | Leq ->  TyBool)
       | _ -> raise (TypeError "Pelo menos um dos operandos de operador binário não é do tipo int")) 
  | If(e1,e2,e3) ->
      let t1 = typeinfer tenv e1 in 
      (match t1 with
         TyBool ->
           let t2 = typeinfer tenv e2 in
           let t3 = typeinfer tenv e3
           in if t2 = t3 then t2
           else raise (TypeError "Then/Else com tipos diferentes")
       | _     -> raise (TypeError "Condição de IF não é do tipo bool"))
  | Fn(x,t,e1) ->
      let t1 = typeinfer (update tenv x t) e1
      in TyFn(t,t1)
  | App(e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in 
      (match t1 with
         TyFn(t_in, t_out) ->  
           if t2 = t_in then t_out
           else raise (TypeError "Tipo argumento errado" )
       | _ -> raise (TypeError "Tipo função era esperado"))
  | Let(x,t,e1,e2) ->
      if (typeinfer tenv e1) = t then typeinfer (update tenv x t) e2
      else raise (TypeError "Expr nao é do tipo declarado em Let" )
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let tenv_com_tf = update tenv f tf in
      let tenv_com_tf_tx = update tenv_com_tf x tx in
      if (typeinfer tenv_com_tf_tx e1) = t2
      then typeinfer tenv_com_tf e2
      else raise (TypeError "Tipo da funcao diferente do declarado")
  | LetRec _ -> raise BugParser
  | Skip -> TyUnit
  | New e -> 
      let t = typeinfer tenv e in
      TyRef t
  | Asg(e1,e2) -> 
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyRef t2 -> TyUnit
       | _ -> raise (TypeError ("O tipo da segunda expressão não é o mesmo da primeira.")))
  | Dref e -> 
      let t1 = typeinfer tenv e in
      (match t1 with
         TyRef t2 -> t2
       | _ -> raise (TypeError "A expressão não é uma referência."))
  | Whl(e1,e2) -> 
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in 
      (match t1 with
         TyBool -> 
           (match t2 with 
              TyUnit -> TyUnit
            | _ -> raise (TypeError "A segunda expressão deve ser do tipo Unit."))
       | _ -> raise (TypeError "A primeira expressão deve ser do tipo bool."))
  | Seq(e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyUnit ->
           (match t2 with 
              _ -> t2)
       | _ -> raise (TypeError "A primeira expressão deve ser do tipo Unit."))


let memorySize = 16
let memoryPointer = ref 0
let memory = Array.make memorySize VUnit

let allocMemory () = memoryPointer := !memoryPointer + 1; !memoryPointer - 1
                                                          
let addMemoryValue address value =
  memory.(address) <- value
    
let getMemory (i : int): value =
  memory.(i)
 
(*++++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*)

let rec compute (oper: op) (v1: value) (v2: value) : value =
  match (oper, v1, v2) with
  
    (* operadores aritméticos com números *)
    (Sum,  VNum n1, VNum n2) -> VNum (n1 + n2)
  | (Sub,  VNum n1, VNum n2) -> VNum (n1 - n2)
  | (Mult, VNum n1, VNum n2) -> VNum (n1 * n2) 
                                                
    (* operadores relacionais com números *)
  | (Eq, VNum n1, VNum n2) -> VBool( n1 = n2) 
  | (Gt, VNum n1, VNum n2) -> VBool( n1 > n2)
  | (Lt, VNum n1, VNum n2) -> VBool( n1 < n2)
  | (Geq,VNum n1, VNum n2) -> VBool( n1 >= n2)
  | (Leq,VNum n1, VNum n2) -> VBool( n1 <= n2) 
                                
  | _ -> raise BugTypeInfer


let rec eval (renv:renv) (e:expr) : value =
  match e with
    Num n -> VNum n
               
  | Bcte b -> VBool b  

  | Var x ->
      (match lookup renv x with
         Some v -> v
       | None -> raise BugTypeInfer)
      
  | Binop(oper,e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      compute oper v1 v2 

  | If(e1,e2,e3) ->
      (match eval renv e1 with
         VBool true  -> eval renv e2
       | VBool false -> eval renv e3
       | _ -> raise BugTypeInfer )

  | Fn (x,_,e1) ->  VClos(x,e1,renv)

  | App(e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      (match v1 with
         VClos(x,ebdy,renv') ->
           let renv'' = update renv' x v2
           in eval renv'' ebdy

       | VRclos(f,x,ebdy,renv') ->
           let renv''  = update renv' x v2 in
           let renv''' = update renv'' f v1
           in eval renv''' ebdy
       | _ -> raise BugTypeInfer)

  | Let(x,_,e1,e2) ->
      let v1 = eval renv e1
      in eval (update renv x v1) e2

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv' e2
      
  | LetRec _ -> raise BugParser
                  
(* Extensões do trabalho *) 
  | Skip -> VUnit
    
  | New e -> 
      let address = allocMemory () in
      addMemoryValue address (eval renv e);
      VMemoryAddress address
  | Dref e -> 
      let address = eval renv e in
      (match address with
         VMemoryAddress adr -> 
           getMemory adr
       | _ -> raise BugTypeInfer )
  | Whl(e1,e2) ->  
      let c = eval renv e1  in
      (match c with
         VBool true  -> eval renv (Seq(e2, Whl(e1,e2)))
       | VBool false -> VUnit
       | _ -> raise BugTypeInfer)
  | Seq (e1, e2) ->
      let _ = eval renv e1 in
      eval renv e2
  | Asg (e1, e2) ->
      let x = eval renv e1 in
      let v1 = eval renv e2 in
      (match x with
        VMemoryAddress address ->
          update address v;
          VUnit
        | _ -> raise BugTypeInfer)

  | _ -> raise BugParser
  
(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let v = eval [] e
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg)
   
 (* as exceções abaixo nao podem ocorrer   *)
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"