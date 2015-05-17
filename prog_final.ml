type ide = string;;

type exp =
  Eint of int
| Ebool of bool
| Echar of char
| Empty
| Cons of exp * exp
| Den of ide
| Prod of exp * exp
| Sum of exp * exp
| Diff of exp * exp
| Mod of exp * exp
| Div of exp * exp
| Lessint of exp * exp
| Eqint of exp * exp
| Iszero of exp
| Lesschar of exp * exp
| Eqchar of exp * exp
| Or of exp * exp
| And of exp * exp
| Not of exp
| Ifthenelse of exp * exp * exp
| Let of (ide * exp) list * exp
| Fun of ide list * exp
| Apply of exp * exp list
| Try of exp * ide * exp
| Raise of ide;;

(************************************************************)
(*                        ECCEZIONI                         *)
(************************************************************)


type exp_stack = List of (ide * exp);;
let default_id = "995e599d-2150-49a6-8c57-03e5bd976252";;
let system_stack = ref (["Default",Raise(default_id)]);;

let add_exp l e = system_stack := l @ !system_stack; e;;
let rem_exp l e = system_stack := l; e;;
let nxt_exp l = system_stack := l; !system_stack;;

let rec get_handler id h = match h with
 (a::[]) -> snd a
 |(a::l) -> let name = fst a in if name = id then rem_exp l (snd a)
 else get_handler id (nxt_exp l)
 |_ -> failwith "Unknow error";;

type generic = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y |Z;;
type typ = 
  Tint 
| Tbool
| Tchar
| Tlist of typ
| Tfun of typ list * typ
| Tgen of generic;;

(************************************************************)
(*                           ENVIRONMENT                    *)
(************************************************************)

type eval = None 
          | Int of int 
          | Bool of bool
          | Char of char
          | List of eval * eval
          | VoidList 
          | Funval of efun
and efun = exp;;

(* The function find, given a predicate p: 'a     bool,
a function f : 'a     eval and a list, finds the first element
of the list (if any) that satisfies the predicate. *)
let rec find p f = function
    [] -> None
  | x::l -> if p x then f x else find p f l;;

(* The function bind binds an identifier x to a value v in the given environment. *)
 let rec bind x v = function
    [] -> [(x,v)]
  | (y,v')::l when x=y -> (x,v)::l
  | (y,v')::l -> (y,v')::(bind x v l);;

(* The function applyenv searches the environment for the value bound to the identifier x. *)
let applyenv env x = (find (fun (y,v) -> x=y) (fun (y,v) -> v)) env;;

let emptyenv () = [];;

type env = (ide*eval) list;;

(************************************************************)
(*                       FUNCTIONS                          *)
(************************************************************)
(* type check principale*)
let type_check (x,y) =
  match x with
    | "int" ->
      (match y with 
      | Int(a) -> true
      | _ -> false)
    | "bool" ->
      (match y with 
      | Bool(a) -> true
      | _ -> false)
    | "char" ->
      (match y with 
      | Char(a) -> true
      | _ -> false)
    | "list" ->
      (match y with
      | VoidList -> true
      | List (a,b) -> true
      | _ -> false)
    | _ -> failwith ("invalid type");;

(* multiplicazione *)
let mul (x,y) =
  if type_check ("int",x) && type_check("int",y) 
  then
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a*b)
    | _ -> failwith("error"))
  else failwith ("type error mul");;

(* addizione *)
let add(x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a+b)
    | _ -> failwith("error"))
  else failwith ("type error add");;

(* sottrazione*)
let sub (x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a-b)
    | _ -> failwith("error"))
  else failwith ("type error sub");;

(* modulo *)
let modulo(x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a mod b)
    | _ -> failwith("error"))
  else failwith ("type error mod");;



(* divisione *)
let divisione (x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a / b)
    | _ -> failwith("error"))
  else failwith ("type error div");;

(* lessint *)
let lessint (x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) when Int(a)<Int(b) -> Int(a)
    | (Int(a), Int(b)) -> Int(b)
    | _ -> failwith("error"))
  else failwith ("type error lessint");;

(* eqint *)
let eqint (x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) when Int(a)=Int(b) -> Bool(true)
    | _ -> Bool(false))
  else failwith ("type error eqint");;

(* iszero *)
let iszero x =
  if type_check("int",x) 
  then 
    (match x with
    | Int(a) -> Bool(a=0)
    | _ -> failwith("error"))
  else failwith ("type error iszero");;

(* lesschar *)
let lesschar (x,y) =
  if type_check("char",x) && type_check("char",y) 
  then 
    (match (x,y) with
    | (Char(a), Char(b)) when Char(a)<Char(b) -> Char(a)
    | (Char(a), Char(b)) -> Char(b)
    | _ -> failwith("error"))
  else failwith ("type error lesschar");;

(* eqchar *)
let eqchar (x,y) =
  if type_check("char",x) && type_check("char",y) 
  then 
    (match (x,y) with
    | (Char(a), Char(b)) when Char(a)=Char(b) -> Bool(true)
    | _ -> Bool(false))
  else failwith ("type error eqchar");;

(* or*)
let or_f (x,y) =
  if type_check("bool",x) && type_check("bool",y) 
  then 
    (match (x,y) with
    | (Bool(a), Bool(b)) -> Bool(a || b)
    | _ -> failwith("error"))
  else failwith ("type error or");;

(* and*)
let and_f (x,y) =
  if type_check("bool",x) && type_check("bool",y) 
  then 
    (match (x,y) with
    | (Bool(a), Bool(b)) -> Bool(a && b)
    | _ -> failwith("error"))
  else failwith ("type error and");;

(* not*)
let not_f x =
  if type_check("bool",x) 
  then 
    (match x with
    | Bool(a) -> Bool(not a)
    | _ -> failwith("error"))
  else failwith ("type error not");;


let cons (x,y) = if type_check("list",y)
  then 
    (match (x,y) with
    | (_,VoidList) -> List(x,VoidList)
    | (Int(u),List(z,w)) -> 
        if type_check("int",z)
        then List(Int(u), List(z,w))
        else failwith "type list error"
    | (Bool(u),List(z,w)) ->
        if type_check("bool",z)
        then List(Bool(u),List(z,w))
        else failwith "type list error"
    | (Char(u),List(z,w)) ->
        if type_check("char",z) 
        then List(Char(u),List(z,w))
        else failwith "type list error"
    | _ -> failwith("error"))
  else failwith ("type error");;

exception WrongBindlist;;
let rec bindlist2 (r,il,el) =
  match (il,el) with
    ([],[]) -> r
  | i::il1, e::el1 -> bindlist2((bind i e r), il1, el1)
  | _ -> raise WrongBindlist;;


let rec sem_eager (e:exp) (r:env) = match e with
    | Eint(n) -> (Int(n),Tint)
    | Ebool(b) -> (Bool(b),Tbool)
    | Echar(c) -> (Char(c),Tchar)
    | Empty -> (VoidList,(Tlist(Tgen A)))
    | Cons(a,b) -> let s = cons(fst(sem_eager a r),fst(sem_eager b r))
                   and t = type_inf (Cons(a,b),r)
                   in (s,t)
    | Den(i) -> ((applyenv r i),(type_inf(Den(i),r)))
    | Prod(a,b) -> (mul(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Sum(a,b) -> (add(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Diff(a,b)  -> (sub(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Mod(a,b) -> (modulo(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Div(a,b) -> (divisione(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Lessint(a,b) -> (lessint(fst(sem_eager a r), fst(sem_eager b r)),Tbool)
    | Eqint(a,b) -> (eqint(fst(sem_eager a r), fst(sem_eager b r)), Tbool)
    | Iszero(a) -> (iszero(fst(sem_eager a r)), Tbool)
    | Lesschar(a,b) -> (lesschar(fst(sem_eager a r), fst(sem_eager b r)), Tbool)
    | Eqchar(a,b) -> (eqchar(fst(sem_eager a r), fst(sem_eager b r) ), Tbool)
    | Or(a,b) ->  (or_f(fst(sem_eager a r), fst(sem_eager b r)), Tbool)
    | And(a,b) ->  (and_f(fst(sem_eager a r), fst(sem_eager b r)), Tbool)
    | Not(a) -> (not_f(fst(sem_eager a r)), Tbool)
    | Ifthenelse(a,b,c) -> 
            let g = (fst (sem_eager a r)) in
            if type_check("bool",g) then
               (if g = Bool(true) 
               then ((sem_eager b r))
               else ((sem_eager c r)))
            else failwith ("wrong guard")
    | Let(l,b) -> (sem_eager b (bindList l r))
    | Fun(i,a) -> (makefun(Fun(i,a)), type_inf(Fun(i,a),r))
    | Apply (a,b) -> let r' = applyf(a, (sem_eagerlist b r),r) in
        (applyfun((sem_eagerlist b r'), fst(sem_eager a r'), r), type_inf(Apply(a,b),r'))
| Try (e1,id,e2) -> sem_eager (add_exp ([id,e2]) e1) r
 | Raise d -> if d = default_id then failwith "Unhandled exception"
 else sem_eager (get_handler d !system_stack) r
and applyf ((a:exp),(b:eval list),(r:env)) = match a with
    Fun(ii,aa) -> bindlist2(r,ii,b)
  | _ -> failwith "No"

and bindList l r = match l with
    [] -> r
  | (x,a)::tl -> bindList tl (bind x (fst(sem_eager a r)) r)

and sem_eagerlist el r = match el with
	  | [] -> []
	  | e::el1 -> (fst(sem_eager e r))::(sem_eagerlist el1 r)

and makefun (a:exp) =
      (match a with
      |	Fun(ii,aa) -> Funval(a)
      |	_ -> failwith ("Non-functional object"))

and applyfun ((ev2:eval list),(ev1:eval),(r:env)) =
      ( match ev1 with
      | Funval(Fun(ii,aa)) -> fst(sem_eager aa (bindlist2(r,ii,ev2)))
      | _ -> failwith ("attempt to apply a non-functional object"))




(************************************************************)
(*                           TYPE_INF                       *)
(************************************************************)

and type_inf ((e:exp),(r:env)) = match e with
    Eint(n) -> Tint
  | Ebool(b) -> Tbool
  | Echar(c) -> Tchar
  | Empty -> Tlist (Tgen A)
  | Cons (a,b) -> Tlist (type_inf(a,r))
  | Den(i) -> let rec typ_den e =
      (match e with
           Int(n) -> Tint
         | Bool(b) -> Tbool
         | Char(c) -> Tchar
         | VoidList -> Tlist(Tgen A)
         | List(a,b) -> typ_den(a))
    in typ_den (applyenv r i)
  | Iszero(a) -> Tbool
  | Eqint(a,b) -> Tbool
  | Lesschar(a,b) -> Tbool
  | Lessint(a,b) -> Tbool
  | Eqchar(a,b) -> Tbool
  | Prod(a,b) -> Tint
  | Sum(a,b) -> Tint
  | Diff(a,b) -> Tint
  | Mod(a,b) -> Tint
  | Div(a,b) -> Tint
  | And(a,b) -> Tbool
  | Or(a,b) -> Tbool
  | Not(a) -> Tbool
  | Ifthenelse(a,b,c) -> if fst (sem_eager a r) = Bool(true) 
    then type_inf(b,r)
    else type_inf(c,r)
  | Let(l,b) -> type_inf(b,r)
  | Fun(i,a) -> Tfun(typ_list i r , type_inf(a,r))
  | Apply(a,b) -> 
      (match type_inf(a,r) with
           Tfun(l,e) -> e
         | _ -> failwith "first argument is not a function")
| Raise id -> Tgen (B)
 | Try (e0,id,e1) -> type_inf (e0,r)
and typ_list l r = match l with
    [] -> []
  | hd::tl -> type_inf((Den(hd)),r)::(typ_list tl r)


 

;;





(************************************************************)
(*                          SEM_LAZY                        *)
(************************************************************)





let rec sem_lazy (e:exp) (r:env) = match e with
    | Eint(n) -> (Int(n),Tint)
    | Ebool(b) -> (Bool(b),Tbool)
    | Echar(c) -> (Char(c),Tchar)
    | Empty -> (VoidList,(Tlist(Tgen A)))
    | Cons(a,b) -> let s = cons(fst(sem_lazy a r),fst(sem_lazy b r))
                   and t = type_inf (Cons(a,b),r)
                   in (s,t)
    | Den(i) -> applyenv r i ,Tgen(D)
    | Prod(a,b) ->( try mul(fst(sem_lazy a r), fst(sem_lazy b r)) with _->Funval(e)), Tint
    | Sum(a,b) -> (add(fst(sem_lazy a r), fst(sem_lazy b r)), Tint)
    | Diff(a,b)  -> (sub(fst(sem_lazy a r), fst(sem_lazy b r)), Tint)
    | Mod(a,b) -> (modulo(fst(sem_lazy a r), fst(sem_lazy b r)), Tint)
    | Div(a,b) -> (try divisione(fst(sem_lazy a r), fst(sem_lazy b r)) with _->Funval(e)), Tint
    | Lessint(a,b) -> (lessint(fst(sem_lazy a r), fst(sem_lazy b r)),Tbool)
    | Eqint(a,b) -> (eqint(fst(sem_lazy a r), fst(sem_lazy b r)), Tbool)
    | Iszero(a) -> (iszero(fst(sem_lazy a r)), Tbool)
    | Lesschar(a,b) -> (lesschar(fst(sem_lazy a r), fst(sem_lazy b r)), Tbool)
    | Eqchar(a,b) -> (eqchar(fst(sem_lazy a r), fst(sem_lazy b r) ), Tbool)
    | Or(a,b) ->  (or_f(fst(sem_lazy a r), fst(sem_lazy b r)), Tbool)
    | And(a,b) ->  (and_f(fst(sem_lazy a r), fst(sem_lazy b r)), Tbool)
    | Not(a) -> (not_f(fst(sem_lazy a r)), Tbool)
    | Ifthenelse(a,b,c) -> 
            let g = (fst (sem_lazy a r)) in
            if type_check("bool",g) then
               (if g = Bool(true) 
               then ((sem_lazy b r))
               else ((sem_lazy c r)))
            else failwith ("wrong guard")
    | Let(l,b) ->(match l with
           []->VoidList,Tint
            |(d1,d2)::tl -> (try (sem_lazy b (bindList l r)) with _->(match (sem_eagerlist [d2] (bindList l r)) with 
    
		[Int(n)]-> (Int(n),Tint)
	      | [Bool(b)]-> (Bool(b),Tbool)
	      | [Char(c)]-> (Char(c),Tchar)
	      |_->Funval(b),Tint))
	    |_->Funval(b),Tint )
    | Fun(i,a) ->(try (makefun(Fun(i,a)))with _->Funval(e)),Tgen(H)
    
    |Apply (a,b) ->match a with
	Fun (e0,e1) -> let w = sem_lazy e1 r in (match w with
	  (Int(n),Tint) -> (Int(n),Tint)
	| (Bool(b),Tbool) -> (Bool(b),Tbool)
	| (Char(c),Tchar) -> (Char(c),Tchar)
        |_->sem_lazy e r)
      |_->sem_lazy e r
;;
type ide = string;;

type exp =
  Eint of int
| Ebool of bool
| Echar of char
| Empty
| Cons of exp * exp
| Den of ide
| Prod of exp * exp
| Sum of exp * exp
| Diff of exp * exp
| Mod of exp * exp
| Div of exp * exp
| Lessint of exp * exp
| Eqint of exp * exp
| Iszero of exp
| Lesschar of exp * exp
| Eqchar of exp * exp
| Or of exp * exp
| And of exp * exp
| Not of exp
| Ifthenelse of exp * exp * exp
| Let of (ide * exp) list * exp
| Fun of ide list * exp
| Apply of exp * exp list
| Try of exp * ide * exp
| Raise of ide;;

(************************************************************)
(*                        ECCEZIONI                         *)
(************************************************************)


type exp_stack = List of (ide * exp);;
let default_id = "995e599d-2150-49a6-8c57-03e5bd976252";;
let system_stack = ref (["Default",Raise(default_id)]);;

let add_exp l e = system_stack := l @ !system_stack; e;;
let rem_exp l e = system_stack := l; e;;
let nxt_exp l = system_stack := l; !system_stack;;

let rec get_handler id h = match h with
 (a::[]) -> snd a
 |(a::l) -> let name = fst a in if name = id then rem_exp l (snd a)
 else get_handler id (nxt_exp l)
 |_ -> failwith "Unknow error";;

type generic = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y |Z;;
type typ = 
  Tint 
| Tbool
| Tchar
| Tlist of typ
| Tfun of typ list * typ
| Tgen of generic;;

(************************************************************)
(*                           ENVIRONMENT                    *)
(************************************************************)

type eval = None 
          | Int of int 
          | Bool of bool
          | Char of char
          | List of eval * eval
          | VoidList 
          | Funval of efun
and efun = exp;;

(* The function find, given a predicate p: 'a     bool,
a function f : 'a     eval and a list, finds the first element
of the list (if any) that satisfies the predicate. *)
let rec find p f = function
    [] -> None
  | x::l -> if p x then f x else find p f l;;

(* The function bind binds an identifier x to a value v in the given environment. *)
 let rec bind x v = function
    [] -> [(x,v)]
  | (y,v')::l when x=y -> (x,v)::l
  | (y,v')::l -> (y,v')::(bind x v l);;

(* The function applyenv searches the environment for the value bound to the identifier x. *)
let applyenv env x = (find (fun (y,v) -> x=y) (fun (y,v) -> v)) env;;

let emptyenv () = [];;

type env = (ide*eval) list;;

(************************************************************)
(*                       FUNCTIONS                          *)
(************************************************************)
(* type check principale*)
let type_check (x,y) =
  match x with
    | "int" ->
      (match y with 
      | Int(a) -> true
      | _ -> false)
    | "bool" ->
      (match y with 
      | Bool(a) -> true
      | _ -> false)
    | "char" ->
      (match y with 
      | Char(a) -> true
      | _ -> false)
    | "list" ->
      (match y with
      | VoidList -> true
      | List (a,b) -> true
      | _ -> false)
    | _ -> failwith ("invalid type");;

(* multiplicazione *)
let mul (x,y) =
  if type_check ("int",x) && type_check("int",y) 
  then
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a*b)
    | _ -> failwith("error"))
  else failwith ("type error mul");;

(* addizione *)
let add(x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a+b)
    | _ -> failwith("error"))
  else failwith ("type error add");;

(* sottrazione*)
let sub (x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a-b)
    | _ -> failwith("error"))
  else failwith ("type error sub");;

(* modulo *)
let modulo(x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a mod b)
    | _ -> failwith("error"))
  else failwith ("type error mod");;



(* divisione *)
let divisione (x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) -> Int(a / b)
    | _ -> failwith("error"))
  else failwith ("type error div");;

(* lessint *)
let lessint (x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) when Int(a)<Int(b) -> Int(a)
    | (Int(a), Int(b)) -> Int(b)
    | _ -> failwith("error"))
  else failwith ("type error lessint");;

(* eqint *)
let eqint (x,y) =
  if type_check("int",x) && type_check("int",y) 
  then 
    (match (x,y) with
    | (Int(a), Int(b)) when Int(a)=Int(b) -> Bool(true)
    | _ -> Bool(false))
  else failwith ("type error eqint");;

(* iszero *)
let iszero x =
  if type_check("int",x) 
  then 
    (match x with
    | Int(a) -> Bool(a=0)
    | _ -> failwith("error"))
  else failwith ("type error iszero");;

(* lesschar *)
let lesschar (x,y) =
  if type_check("char",x) && type_check("char",y) 
  then 
    (match (x,y) with
    | (Char(a), Char(b)) when Char(a)<Char(b) -> Char(a)
    | (Char(a), Char(b)) -> Char(b)
    | _ -> failwith("error"))
  else failwith ("type error lesschar");;

(* eqchar *)
let eqchar (x,y) =
  if type_check("char",x) && type_check("char",y) 
  then 
    (match (x,y) with
    | (Char(a), Char(b)) when Char(a)=Char(b) -> Bool(true)
    | _ -> Bool(false))
  else failwith ("type error eqchar");;

(* or*)
let or_f (x,y) =
  if type_check("bool",x) && type_check("bool",y) 
  then 
    (match (x,y) with
    | (Bool(a), Bool(b)) -> Bool(a || b)
    | _ -> failwith("error"))
  else failwith ("type error or");;

(* and*)
let and_f (x,y) =
  if type_check("bool",x) && type_check("bool",y) 
  then 
    (match (x,y) with
    | (Bool(a), Bool(b)) -> Bool(a && b)
    | _ -> failwith("error"))
  else failwith ("type error and");;

(* not*)
let not_f x =
  if type_check("bool",x) 
  then 
    (match x with
    | Bool(a) -> Bool(not a)
    | _ -> failwith("error"))
  else failwith ("type error not");;


let cons (x,y) = if type_check("list",y)
  then 
    (match (x,y) with
    | (_,VoidList) -> List(x,VoidList)
    | (Int(u),List(z,w)) -> 
        if type_check("int",z)
        then List(Int(u), List(z,w))
        else failwith "type list error"
    | (Bool(u),List(z,w)) ->
        if type_check("bool",z)
        then List(Bool(u),List(z,w))
        else failwith "type list error"
    | (Char(u),List(z,w)) ->
        if type_check("char",z) 
        then List(Char(u),List(z,w))
        else failwith "type list error"
    | _ -> failwith("error"))
  else failwith ("type error");;

exception WrongBindlist;;
let rec bindlist2 (r,il,el) =
  match (il,el) with
    ([],[]) -> r
  | i::il1, e::el1 -> bindlist2((bind i e r), il1, el1)
  | _ -> raise WrongBindlist;;


let rec sem_eager (e:exp) (r:env) = match e with
    | Eint(n) -> (Int(n),Tint)
    | Ebool(b) -> (Bool(b),Tbool)
    | Echar(c) -> (Char(c),Tchar)
    | Empty -> (VoidList,(Tlist(Tgen A)))
    | Cons(a,b) -> let s = cons(fst(sem_eager a r),fst(sem_eager b r))
                   and t = type_inf (Cons(a,b),r)
                   in (s,t)
    | Den(i) -> ((applyenv r i),(type_inf(Den(i),r)))
    | Prod(a,b) -> (mul(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Sum(a,b) -> (add(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Diff(a,b)  -> (sub(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Mod(a,b) -> (modulo(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Div(a,b) -> (divisione(fst(sem_eager a r), fst(sem_eager b r)), Tint)
    | Lessint(a,b) -> (lessint(fst(sem_eager a r), fst(sem_eager b r)),Tbool)
    | Eqint(a,b) -> (eqint(fst(sem_eager a r), fst(sem_eager b r)), Tbool)
    | Iszero(a) -> (iszero(fst(sem_eager a r)), Tbool)
    | Lesschar(a,b) -> (lesschar(fst(sem_eager a r), fst(sem_eager b r)), Tbool)
    | Eqchar(a,b) -> (eqchar(fst(sem_eager a r), fst(sem_eager b r) ), Tbool)
    | Or(a,b) ->  (or_f(fst(sem_eager a r), fst(sem_eager b r)), Tbool)
    | And(a,b) ->  (and_f(fst(sem_eager a r), fst(sem_eager b r)), Tbool)
    | Not(a) -> (not_f(fst(sem_eager a r)), Tbool)
    | Ifthenelse(a,b,c) -> 
            let g = (fst (sem_eager a r)) in
            if type_check("bool",g) then
               (if g = Bool(true) 
               then ((sem_eager b r))
               else ((sem_eager c r)))
            else failwith ("wrong guard")
    | Let(l,b) -> (sem_eager b (bindList l r))
    | Fun(i,a) -> (makefun(Fun(i,a)), type_inf(Fun(i,a),r))
    | Apply (a,b) -> let r' = applyf(a, (sem_eagerlist b r),r) in
        (applyfun((sem_eagerlist b r'), fst(sem_eager a r'), r), type_inf(Apply(a,b),r'))
| Try (e1,id,e2) -> sem_eager (add_exp ([id,e2]) e1) r
 | Raise d -> if d = default_id then failwith "Unhandled exception"
 else sem_eager (get_handler d !system_stack) r
and applyf ((a:exp),(b:eval list),(r:env)) = match a with
    Fun(ii,aa) -> bindlist2(r,ii,b)
  | _ -> failwith "No"

and bindList l r = match l with
    [] -> r
  | (x,a)::tl -> bindList tl (bind x (fst(sem_eager a r)) r)

and sem_eagerlist el r = match el with
	  | [] -> []
	  | e::el1 -> (fst(sem_eager e r))::(sem_eagerlist el1 r)

and makefun (a:exp) =
      (match a with
      |	Fun(ii,aa) -> Funval(a)
      |	_ -> failwith ("Non-functional object"))

and applyfun ((ev2:eval list),(ev1:eval),(r:env)) =
      ( match ev1 with
      | Funval(Fun(ii,aa)) -> fst(sem_eager aa (bindlist2(r,ii,ev2)))
      | _ -> failwith ("attempt to apply a non-functional object"))




(************************************************************)
(*                           TYPE_INF                       *)
(************************************************************)

and type_inf ((e:exp),(r:env)) = match e with
    Eint(n) -> Tint
  | Ebool(b) -> Tbool
  | Echar(c) -> Tchar
  | Empty -> Tlist (Tgen A)
  | Cons (a,b) -> Tlist (type_inf(a,r))
  | Den(i) -> let rec typ_den e =
      (match e with
           Int(n) -> Tint
         | Bool(b) -> Tbool
         | Char(c) -> Tchar
         | VoidList -> Tlist(Tgen A)
         | List(a,b) -> typ_den(a))
    in typ_den (applyenv r i)
  | Iszero(a) -> Tbool
  | Eqint(a,b) -> Tbool
  | Lesschar(a,b) -> Tbool
  | Lessint(a,b) -> Tbool
  | Eqchar(a,b) -> Tbool
  | Prod(a,b) -> Tint
  | Sum(a,b) -> Tint
  | Diff(a,b) -> Tint
  | Mod(a,b) -> Tint
  | Div(a,b) -> Tint
  | And(a,b) -> Tbool
  | Or(a,b) -> Tbool
  | Not(a) -> Tbool
  | Ifthenelse(a,b,c) -> if fst (sem_eager a r) = Bool(true) 
    then type_inf(b,r)
    else type_inf(c,r)
  | Let(l,b) -> type_inf(b,r)
  | Fun(i,a) -> Tfun(typ_list i r , type_inf(a,r))
  | Apply(a,b) -> 
      (match type_inf(a,r) with
           Tfun(l,e) -> e
         | _ -> failwith "first argument is not a function")
| Raise id -> Tgen (B)
 | Try (e0,id,e1) -> type_inf (e0,r)
and typ_list l r = match l with
    [] -> []
  | hd::tl -> type_inf((Den(hd)),r)::(typ_list tl r)


 

;;





(************************************************************)
(*                          SEM_LAZY                        *)
(************************************************************)





let rec sem_lazy (e:exp) (r:env) = match e with
    | Eint(n) -> (Int(n),Tint)
    | Ebool(b) -> (Bool(b),Tbool)
    | Echar(c) -> (Char(c),Tchar)
    | Empty -> (VoidList,(Tlist(Tgen A)))
    | Cons(a,b) -> let s = cons(fst(sem_lazy a r),fst(sem_lazy b r))
                   and t = type_inf (Cons(a,b),r)
                   in (s,t)
    | Den(i) -> applyenv r i ,Tgen(D)
    | Prod(a,b) ->( try mul(fst(sem_lazy a r), fst(sem_lazy b r)) with _->Funval(e)), Tint
    | Sum(a,b) -> (add(fst(sem_lazy a r), fst(sem_lazy b r)), Tint)
    | Diff(a,b)  -> (sub(fst(sem_lazy a r), fst(sem_lazy b r)), Tint)
    | Mod(a,b) -> (modulo(fst(sem_lazy a r), fst(sem_lazy b r)), Tint)
    | Div(a,b) -> (try divisione(fst(sem_lazy a r), fst(sem_lazy b r)) with _->Funval(e)), Tint
    | Lessint(a,b) -> (lessint(fst(sem_lazy a r), fst(sem_lazy b r)),Tbool)
    | Eqint(a,b) -> (eqint(fst(sem_lazy a r), fst(sem_lazy b r)), Tbool)
    | Iszero(a) -> (iszero(fst(sem_lazy a r)), Tbool)
    | Lesschar(a,b) -> (lesschar(fst(sem_lazy a r), fst(sem_lazy b r)), Tbool)
    | Eqchar(a,b) -> (eqchar(fst(sem_lazy a r), fst(sem_lazy b r) ), Tbool)
    | Or(a,b) ->  (or_f(fst(sem_lazy a r), fst(sem_lazy b r)), Tbool)
    | And(a,b) ->  (and_f(fst(sem_lazy a r), fst(sem_lazy b r)), Tbool)
    | Not(a) -> (not_f(fst(sem_lazy a r)), Tbool)
    | Ifthenelse(a,b,c) -> 
            let g = (fst (sem_lazy a r)) in
            if type_check("bool",g) then
               (if g = Bool(true) 
               then ((sem_lazy b r))
               else ((sem_lazy c r)))
            else failwith ("wrong guard")
    | Let(l,b) ->(match l with
           []->VoidList,Tint
            |(d1,d2)::tl -> (try (sem_lazy b (bindList l r)) with _->(match (sem_eagerlist [d2] (bindList l r)) with 
    
		[Int(n)]-> (Int(n),Tint)
	      | [Bool(b)]-> (Bool(b),Tbool)
	      | [Char(c)]-> (Char(c),Tchar)
	      |_->Funval(b),Tint))
	    |_->Funval(b),Tint )
    | Fun(i,a) ->(try (makefun(Fun(i,a)))with _->Funval(e)),Tgen(H)
    
    |Apply (a,b) ->match a with
	Fun (e0,e1) -> let w = sem_lazy e1 r in (match w with
	  (Int(n),Tint) -> (Int(n),Tint)
	| (Bool(b),Tbool) -> (Bool(b),Tbool)
	| (Char(c),Tchar) -> (Char(c),Tchar)
        |_->Funval(e),Tgen(F))
      |_->sem_lazy e r
;;


let x1=sem_eager (Try(Ifthenelse(Ebool(true),Raise "pippo", Empty),"pippo",Apply(Fun(["x"],Den("x")),[Echar('z')]))) (emptyenv());;
(************************************************************)
(*                        TEST                              *)
(************************************************************)

sem_lazy (Apply(Fun(["x"],Den("x")),[Eint 1])) (emptyenv());;
sem_eager (Apply(Fun(["x"],Den("x")),[Eint 1])) (emptyenv());;

sem_eager (Fun(["Y"],Prod(Den("X"),Den("Y")))) (emptyenv());;

sem_lazy  (Apply(Fun(["Y"],(Div(Den("Y"),Eint 3))),[Eint 1])) (emptyenv());;

sem_lazy(Let(["Y",Eint 1],Div(Div(Eint 4,Eint 2),Den"Y"))) (emptyenv());;
sem_lazy(Den "x" ) (emptyenv());;

(*let lazy_exp=sem_lazy (Let(["X",Eint 2],Apply(Fun(["Y"],Prod(Den("X"),Den("Y"))),[Eint 1]))) (emptyenv());;*)
let lazy_exp2=sem_lazy  (Apply(Fun(["x"], Eint 0),[Div(Eint 3, Den "x")])) (emptyenv());;
 let ris1=sem_lazy (Let(["X",(Sum(Eint 1,Eint 2))],Den("X"))) (emptyenv());;

sem_lazy (Let(["X",Eint 2],Apply(Fun(["Y"],Prod(Den("X"),Den("Y"))),[Eint 7]))) (emptyenv());;

let ris_lazy= (sem_lazy (Let(["X",Eint 2],Apply(Fun(["Y"],Prod(Den("X"),Den("Y"))),[Eint 1]))) (emptyenv()));;
let force f=f();;
from_val (sem_eager  (Let(["X",Eint 2],Apply(Fun(["Y"],Prod(Den("X"),Den("Y"))),[Eint 1]))) (emptyenv()));;
