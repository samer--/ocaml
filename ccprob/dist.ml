(* Dist provides tools for adding numerical weights to things, and
 * constructing weighted distributions over things. Currently, the weight type
 * is fixed at float, but at some point I might consider functorising on the
 * weight type so that I can use rational or other numerical types.
 *)

open Utils
include Float

type weight  = t
type 'a weighted = weight * 'a
type 'a dist = 'a weighted list


let mul x y = x *. y
let div k x = x /. k
let string_of_weight = to_string

(* fmap : ('a -> 'b) -> 'a dist -> 'b dist
 * In Haskell, dist would be an instance of Functor *)
let fmap f = List.map (fun (w,x) -> (w,f x))

(* map_weights : (weight -> weight) -> 'a dist -> 'a dist
 * apply a function to the weights *)
let map_weights f = List.map (fun (w,x) -> (f w,x))

let div_weights k = List.map (fun (w,x) -> (w /. k,x))
let mul_weights k = List.map (fun (w,x) -> (w *. k,x))

(* prune : 'a dist -> 'a dist
 * removes zero-weighted items from a distribution *)
let prune d = List.filter (fun (w,x) -> w>zero) d

(* total : 'a dist -> weight
 * Sum up weights *)
let total d = List.fold_left (fun s (w,_) -> s +. w) zero d 

(* normalise' : 'a dist -> weight * 'a dist
 * As normalise but return original total as well *)
let normalise' d = let t=total d in (t,div_weights t d)

(* normalise : 'a dist -> 'a dist
 * Rescale weights to sum to unity *)
let normalise d = snd (normalise' d)

let weights d = List.map fst d
let values d = List.map snd d


(* sample' : weight -> 'a dist -> 'a
 * Sample un-normalised dist with given total *)
let sample' (tot : weight) dist = 
  let rec select (u : weight) (cum : weight) = function
    | [] -> failwith "sampling failure"
    | (w,x)::rest -> let cum = cum +. w in
         if u < to_float cum then x else select u cum rest in
  select (Random.float (to_float tot)) zero dist

(* sample : 'a dist -> 'a
 * Sample using system random generator, assumes normalisation. *)
let sample dist = sample' one dist

(* sample from un-normalisated distribution *)
let sample_unnormed dist = sample' (total dist) dist

(* sample from un-normalisation distribution and return total *)
let sample_and_total d = let t=total d in (t,sample' t d)

module MDist_BatMap = struct
  (** Representation of a distribution as a map from values to weights *)
  type 'a t = ('a,weight) BatMap.t

  let empty = BatMap.empty
  let to_dist m = List.map Pair.swap (BatMap.bindings m)
  (* let to_dist m = BatMap.foldi (fun x w ts -> (w,x)::ts) m [] *)
  let foldl f = BatMap.foldi (fun x w ts -> f (w,x) ts)
  let accum (w,x) (m : 'a t) : 'a t = BatMap.modify_def zero x ((+.) w) m
  let accum' w x (m : 'a t) : 'a t = BatMap.modify_def zero x ((+.) w) m
end

(* module MDist_PMap = struct *)
(*   (** Representation of a distribution as a map from values to weights *) *)
(*   type 'a t = ('a,weight) PMap.t *)

(*   let empty = PMap.empty *)
(*   let to_dist m = PMap.foldi (fun x w ts -> (w,x)::ts) m [] *)
(*   let foldl f = PMap.foldi (fun x w ts -> f (w,x) ts) *)
(*   let accum (w,x) (m : 'a t) : 'a t = PMap.insert_with (+.) x w m *)
(*   let accum' w x (m : 'a t) : 'a t = PMap.insert_with (+.) x w m *)
(* end *)
module MDist = MDist_BatMap

let init_random = Random.init
let full_init_random = Random.full_init
