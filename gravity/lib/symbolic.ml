open Utils

module Sym = struct
  type term = | Add of term * term
              | Mul of term * term
              | Pow of float * term
              | Var of int * string
              | Const of float

  let next_id = ref 0
  let var name =
    let id = !next_id in
    next_id := Stdlib.(id+1); Var (id, name)

  let rec simplify = function
    | Add (Const 0.0, b) -> b
    | Add (a, Const 0.0) -> a
    | Add (Const x, Const y) -> Const (x +. y)
    | Add (a, b) when a=b -> Mul (Const 2.0, a) |> simplify
    | Mul (Const 1.0, b) -> b
    | Mul (a, Const 1.0) -> a
    | Mul (Const 0.0, _) -> Const 0.0
    | Mul (_, Const 0.0) -> Const 0.0
    | Mul (Const x, Const y) -> Const (x *. y)
    | Mul (Const a, Mul (Const b, x)) -> Mul (Const (a *. b), x) |> simplify
    | Mul (Mul (Const b, x), Const a) -> Mul (Const (a *. b), x) |> simplify
    | Mul (a, b) when a=b -> Pow (2.0, a) |> simplify
    | Pow (n, Pow (m, x)) -> Pow (n *. m, x) |> simplify
    | Pow (_, Const 0.0) -> Const 0.0
    | Pow (_, Const 1.0) -> Const 1.0
    | Pow (0.0, _) -> Const 1.0
    | Pow (1.0, a) -> a
    | Pow (k, Const x) -> Const (x ** k)
    | x -> x

  let const x = Const x
  let zero    = const 0.0
  let one     = const 1.0
  let ( + ) x y  = Add (x,y) |> simplify
  let ( * ) x y  = Mul (x,y) |> simplify
  let pow y x    = Pow (y,x) |> simplify
  let recip x    = pow (-1.0) x
	let neg x      = const (-1.0) * x |> simplify
  let of_float x = Const x

  let rec str =
    let paren x = "(" ^ x ^ ")" in
    function
      | Add (a,Mul (Const -1.0, b)) -> str a ^ " - " ^ str b |> paren
      | Add (a,b) -> str a ^ " + " ^ str b |> paren
      | Mul (Const -1.0,b) -> "-" ^ str b |> paren
      | Mul (a,b) -> str a ^ "*" ^ str b |> paren
      | Pow (a,b) -> str b ^ "^" ^ string_of_float a
      | Const x -> string_of_float x
      | Var (_,n) -> n

  let rec deriv x y =
    if x=y then one
    else match x with
      | Add (a,b) -> deriv a y + deriv b y
      | Mul (a,b) -> deriv a y * b + a * deriv b y
      | Pow (n,a) -> deriv a y * const n * pow (n -. 1.0) a
      | Const _   -> zero
      | Var _ -> zero

  (* Allows Sym to be used as a SCALAR *)
  type t = term
end


module Tree = struct
  (* Aggregation of things *)
  type ('a,'b) t = | Seq : ('a,'b) t list -> ('a,'b list) t
                   | Two : ('a,'b) t * ('a,'c) t -> ('a,'b*'c) t
                   | One : 'a -> ('a,unit) t

  let seq x = Seq x
  let one x = One x
  let of_scalars xx = Seq (List.map one xx)
  let of_pair (x,y) = Two (One x,One y)
  let of_pairs pairs = Seq (List.map of_pair pairs)
  let pair_of_two (Two (One x, One y)) = (x,y)
  let list_of_seq (Seq xs) = xs
  let un_one (One x) = x

  let rec map: type e. ('a -> 'b) -> ('a,e) t -> ('b,e) t =
    fun f -> function
      | One x       -> One (f x)
      | Two (x1,x2) -> Two (map f x1, map f x2)
      | Seq xs      -> Seq (List.map (map f) xs)

  let rec map2: type e. ('a -> 'b -> 'c) -> ('a,e) t -> ('b,e) t -> ('c,e) t =
    fun f xs ys -> match (xs,ys) with
      | One x,       One y       -> One (f x y)
      | Two (x1,x2), Two (y1,y2) -> Two (map2 f x1 y1, map2 f x2 y2)
      | Seq xs,      Seq ys      -> Seq (List.map2 (map2 f) xs ys)

  let rec foldl: type e. ('b -> 'a -> 'b) -> 'b -> ('a,e) t -> 'b =
    fun f s -> function
      | One x       -> f s x
      | Two (x1,x2) -> foldl f (foldl f s x1) x2
      | Seq xs      -> List.fold_left (foldl f) s xs

  let rec flip_map: type e. ('a,e) t -> ('a -> 'b) -> ('b,e) t =
    function
      | One x       -> fun f -> One (f x)
      | Two (x1,x2) -> let fm1, fm2 = flip_map x1, flip_map x2 in
                       fun f -> Two (fm1 f, fm2 f)
      | Seq xs      -> let fmx = list_flip_map (List.map flip_map xs) in
                       fun f -> Seq (fmx (apply_to f))

  let rec papp_fold2: type e. ('a -> 'b -> 'c -> 'c) -> ('a,e) t -> ('b,e) t -> 'c -> 'c =
    fun f -> function
      | One x       -> fun (One y) s -> f x y s
      | Two (x1,x2) -> let ff1 = papp_fold2 f x1 in
                       let ff2 = papp_fold2 f x2 in
                       fun (Two (y1,y2)) s -> ff2 y2 (ff1 y1 s)
      | Seq xs      -> let ff = list_flip_fold2 (papp_fold2 f) xs in
                       fun (Seq ys) s -> ff ys s
end
