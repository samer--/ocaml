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

  (* This a mechanical refactor of the original symbol algebra. It should
   * give exactly the same simplified expressions. *)
  let rec pow' = function
    | (0.0, _) -> Const 1.0
    | (1.0, a) -> a
    | (n, a) ->
      match a with
      | Pow (m, x) -> pow' (n *. m, x)
      | Const 0.0 when n < 0.0 ->
          invalid_arg "Sym.pow: negative power of zero"
      | Const 0.0 -> Const 0.0
      | Const 1.0 -> Const 1.0
      | Const x -> Const (x ** n)
      | a -> Pow (n, a)

  let rec mul' = function
    | Const 1.0, b -> b
    | a, Const 1.0 -> a
    | Const 0.0, _ -> Const 0.0
    | _, Const 0.0 -> Const 0.0
    | Const x, Const y -> Const (x *. y)
    | Const a, Mul (Const b, x) -> mul' (Const (a *. b), x)
    | Mul (Const b, x), Const a -> mul' (Const (a *. b), x)
    | a, b when a=b -> pow' (2.0, a)
    | a, b -> Mul (a, b)

  let add' = function
    (* what about a * x + b * x --> (a+b) * x?
     * Maybe just for constants a and b? *)
    | (Const 0.0, b) -> b
    | (a, Const 0.0) -> a
    | (Const x, Const y) -> Const (x +. y)
    | (a, b) when a=b -> mul' (Const 2.0, a)
    | (a, b) -> Add (a, b)

  let const x = Const x
  let zero    = const 0.0
  let one     = const 1.0
  let ( + ) x y  = add' (x,y)
  let ( * ) x y  = mul' (x,y)
  let pow y x    = pow' (y,x)
  let recip x    = pow (-1.0) x
	let neg x      = const (-1.0) * x
  let of_float x = Const x

  (* ---- Pretty-printer (Format-based) ---- *)

  (* Precedence levels: 0=Add, 1=Mul, 2=Pow/atom *)
  let rec pp_prec (prec : int) (ppf : Format.formatter) (x : term) : unit =
    let parens needed pp_child =
      if prec > needed
      then Format.fprintf ppf "(@[%t@])" pp_child
      else pp_child ppf
    in
    match x with
    | Add (a, Mul (Const (-1.0), b)) ->
      parens 0 (fun ppf ->
        Format.fprintf ppf "@[%a -@ %a@]" (pp_prec 0) a (pp_prec 1) b)
    | Add (a, b) ->
      parens 0 (fun ppf ->
        Format.fprintf ppf "@[%a +@ %a@]" (pp_prec 0) a (pp_prec 1) b)
    | Mul (Const (-1.0), b) ->
      parens 1 (fun ppf ->
        Format.fprintf ppf "-%a" (pp_prec 2) b)
    | Mul (a, b) ->
      parens 1 (fun ppf ->
        Format.fprintf ppf "@[%a *@ %a@]" (pp_prec 1) a (pp_prec 2) b)
    | Pow (n, a) ->
      parens 2 (fun ppf ->
        Format.fprintf ppf "@[%a^%s@]" (pp_prec 2) a (Utils.float_str n))
    | Const x -> Format.fprintf ppf "%s" (Utils.float_str x)
    | Var (_, n) -> Format.pp_print_string ppf n

  let pp = pp_prec 0

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
  (* tree nodes typed by leaf type AND shape *)
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

  (* ---- Pretty-printer for trees of terms ---- *)

  (* Print a tree with indentation, using the given leaf printer *)
  let rec pp_generic : type e. (Format.formatter -> 'a -> unit) -> Format.formatter -> ('a,e) t -> unit =
    fun pp_leaf ppf -> function
      | One x -> pp_leaf ppf x
      | Two (x1, x2) ->
        Format.fprintf ppf "@[<v>(@,%a,@,%a)@]" (pp_generic pp_leaf) x1 (pp_generic pp_leaf) x2
      | Seq xs ->
        Format.fprintf ppf "@[<v>[%a]@]"
          (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") (pp_generic pp_leaf))
          xs
end
