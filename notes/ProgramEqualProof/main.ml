    (* recursive function with rec keyword *)
let rec fact n =
    if n = 0 then 1 else n * fact(n - 1);;

    (* This is hold return value in f *)
(*let f = print_string "hello\n";;*)

    (* This is function with void argument *)
let f () = print_string "hello";;

type tree =
    | Node of int * tree * tree
    | Leaf of int;;

let t = Node (3, Node (4, Leaf 1, Node(3, Leaf 5, Leaf 5)), Leaf 1);;

let rec height t =
    match t with
    | Node (n, t1, t2) -> 1 + max (height t1) (height t2)
    | Leaf n -> 0;;

let t_height = height(t);;
let t_height_string = string_of_int(t_height);;

(*print_string("Tree height: "^t_height_string^"\n");;*)

let rec sum t =
    match t with
    | Node (n, t1, t2) -> n + sum t1 + sum t2
    | Leaf n -> n

let sum_of_leafs = string_of_int(sum(t));;

(*print_string(sum_of_leafs^"\n");;*)

(* If else as recursive type *)
(* if b then e1 else e2 *)

(*match b with*)
    (*| True  -> e1*)
    (*| False -> e2*)

type 'a list =
    | Nil
    | Cons of 'a * 'a list;;

let rec length l =
    match l with
    | x::l -> 1 + length l
    | []   -> 0;;

(* definition of list, haven't found how to make it with our defined type *)
let l1 = [ 1; 2; 3; 4; 5 ]

type ('a, 'b) coprod =
    | Left of 'a
    | Right of 'b;;

let to_string = function
    | Left n  -> string_of_int n
    | Right x -> string_of_float x;;

type unit =
    | T;;

type empty =
    | ;;

let rec add m n =
    match m with
    | Zero  -> n
    | Suc m -> Suc (add m n);;

type 'a option =
    | Some of 'a
    | None;;

let hd l =
    match l with
    | x::l -> Some x
    | [] -> None;;

match head l with
    | Some n -> 2 * n
    | None   -> 0;;  (* This case cannot happen *)

(* exception mechanism *)
let hd l =
    match l with
    | x::l -> x
    | []   -> raise Not_found;;

    (* exception handling *)
(*  try                     *)
(*      ...                 *)
(*  with                    *)
(*      | Not_found -> ...  *)

type value =
    | Int of int
    | Bool of bool;;

type prog =
    | Val of value
    | Add of prog * prog
    | Lt  of prog * prog
    | If  of prog * prog * prog;;

    (* Perform one reduction step. *)
let rec red : prog -> prog option = function
    | Bool _ | Int _ -> None
    | Add (Int n1, Int n2) -> Some (Int (n1 + n2))
    | Add (p1, p2) ->
        (
            match red p1 with
                | Some p1' -> Some (Add (p1', p2))
                | None ->
                    match red p2 with
                        | Some p2' -> Some (Add (p1, p2'))
                        | None     -> None
        )
    | Lt (Int n1, Int n2) -> Some (Bool (n1 < n2))
    | Lt (p1, p2) ->
        (
            match red p1 with
                | Some p1' -> Some (Lt (p1', p2))
                | None ->
                    match red p2 with
                        | Some p2' -> Some (Lt (p1, p2'))
                        | None     -> None
        )
    | If (Bool true, p1, p2)  -> Some p1
    | If (Bool false, p1, p2) -> Some p2
    | If (p, p1, p2) ->
        match red p with
            | Some p' -> Some (If (p', p1, p2))
            | None    -> None;;

(* A => A *)
let id : 'a -> 'a = fun x -> x;;

(* A => B => A *)
let k : 'a -> 'b -> 'a = fun x y -> x;;

(* (A => B) => (B => C) => (A => C) *)
let comp : ('a -> 'b) -> ('b -> 'c) -> ('a -> 'c) =
    fun f g x -> g (f x);;

(* (A => B => C) => (A => B) => (A => C) *)
let s : ('a -> 'b -> 'c) -> ('a -> 'b) -> ('a -> 'c) =
    fun f g x -> f x (g x);;

(* A and B => A *)
let proj1 : ('a * 'b) -> 'a = fun (a, b) -> a;;

(* A and B => B and A *)
let comm : ('a * 'b) -> ('b * 'a) = fun (a, b) -> b, a;;

(* A => T *)

let unit_intro : 'a -> unit = fun x -> ();;

type empty = | ;;

(* False => A *)
(* '.' "refutation case" meaning that the compiler should ensure that this case should
 * never happen *)
let empty_elim : empty -> 'a = fun x -> match x with _ -> . ;;

(* (A => B) => (non B => non A) *)
let contr : ('a -> 'b) -> (('b -> empty) -> ('a -> empty)) =
    fun f g a -> g (f a);;

(* A => non non A *)
let nni : 'a -> (('a -> empty) -> empty) = fun a f -> f a;;

type ('a, 'b) coprod = Left of 'a | Right of 'b;;

(* A or B => B or A *)
let comm: ('a, 'b) coprod -> ('b, 'a) coprod = fun x ->
    match x with
    | Left  a -> Right a
    | Right b -> Left b;;

(* A and (B or C) => (A and B) or (A and C) *)
let dist : ('a ('b, 'c) coprod) -> ('a * 'b, 'a * 'c) coprod =
    fun (a, x) ->
    match x with
    | Left b  -> Left (a, b)
    | Right c -> Right (a, c);;

(* (non A or B) => (A => B) *)
let de_Mogan : ('a -> empty, 'b) coprod -> ('a -> 'b) = fun x a ->
    match x with
    | Left f -> empty elim(f a)
    | Right b -> b;;

(* "proving" A => B *)
let absurd : 'a -> b' = fun x -> raise Not_found;;

(* "proving" A => B *)
let rec absurd : 'a -> 'b = fun x -> absurd x;;

(* "proving" falsity *)
let fake : empty = absurd ();;
