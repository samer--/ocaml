type 'a pair = 'a * 'a

let ( -| ) f g x = f (g x)
let ( % ) f g x = f (g x) (* same as in Batteries *)
let uncurry f (x,y) = f x y
let pair x y = (x,y)

(* returns all distinct subsets of two elements as a list of pairs *)
(* pairs : 'a list -> ('a * 'a) list *)
let rec pairs = function
		| [] -> []
		| x::xs -> (List.map (pair x) xs) @ pairs xs

let apply_to x f = f x
let rec rep n a = if n=0 then [] else a::rep (n-1) a
let rec iota n = if n=0 then [] else iota (n-1) @ [n]
let rec iterate n f x = if n=0 then x else iterate (n-1) f (f x)

let rec unzip = function
  | [] -> [], []
  | (x,y)::pairs -> let xs, ys = unzip pairs in x::xs, y::ys

let rec unzip3 = function
  | [] -> [], [], []
  | (x,y,z)::xyzs -> let xs, ys, zs = unzip3 xyzs in x::xs, y::ys, z::zs

type ('a, 'b) either = Left of 'a | Right of 'b

let divby y x = x /. y
let setup_call_cleanup setup cleanup f =
  let x = setup () in
  let y = try Left (f x) with e -> Right e in
  cleanup x;
  match y with
    | Left y -> y
    | Right e -> raise e

let get_time = Unix.gettimeofday

let sleep_until target =
  let rec delay t =
    try ignore (Unix.select [] [] [] t)
    with Unix.Unix_error(Unix.EINTR, _, _) ->
      let remaining = target -. get_time () in
      if remaining > 0.0 then delay remaining
  in let remaining = target -. get_time () in
  if remaining > 0.0 then delay remaining
  (* else Printf.printf "!" *)

let rec list_flip_map = function
  | []    -> fun _ -> []
  | x::xs -> let g = list_flip_map xs in fun f -> f x::g f

let rec list_flip_fold2 f = function
  | []    -> fun _ s -> s
  | x::xs -> let ffxs = list_flip_fold2 f xs in
             let fx = f x in
             fun (y::ys) s -> ffxs ys (fx y s)

let rec repeat n thunk =
  if n=0 then () else (thunk (); repeat (n-1) thunk)

(* time execution *)
let timeit n thunk =
  let time_start = Sys.time () in
  let result = repeat n thunk in
  Printf.printf "Time: %g s" (Sys.time () -. time_start);
  print_endline "";
  result

