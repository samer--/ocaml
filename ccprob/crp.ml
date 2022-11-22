
(* These are my original attempt at memo using the [new_ref] and [upd] functions
 * from the [ImplicitStore] module. It has the advantage that lookups
 * do not need to mutate the store, but I find it not as neat the
 * alternative above that uses [with_ref] to hide the funny business with
 * references behind a purely functional interface.

  let memo' f =
    let loc = S.new_ref PMap.empty in fun x ->
      try PMap.find x (S.get loc) 
      with Not_found -> 
        let v = f x in S.upd loc (PMap.add x v); v
*)

  (* let crp alpha = *) 
  (*   let loc = S.new_ref (0.0,0,[]) *)
  (*   and append = List.append  in *)
  (*   let rec increment n (x::xs) = if n=0 then (x+1)::xs else x::(increment (n-1) xs) *)
  (*   and divby k xs = List.map (fun x -> x/.k) xs *) 
  (*   and bernoulli p  = dist [p,true; 1.0 -. p,false] in *)
  (*   fun () -> *)
  (*     let (total,n,counts) = S.get loc in *)
  (*     if bernoulli (alpha /. (total +. alpha)) then *)
  (*       let x = n in *)
  (*       S.put loc (total +. 1.0,x+1, append counts [1]); x *)
  (*     else *)
  (*       let x = discrete (divby total counts) in *) 
  (*       S.put loc (total +. 1.0,n, increment x counts); x *)

  (* assuming depth=1 
  let rec bound_and_prune1 trees = 
    let not_failure (w,t) = match t with | Leaf _ -> true | Node tt -> tt () <> []
    in Dist.normalise' (List.filter not_failure trees)
    *)

  let rec bound_and_prune' depth trees = 
    let reweight (w,t) = if depth=0 then (w,t) else match t with 
        | Leaf x -> (w,t)
        | Node tt -> let (tot,normed) = bound_and_prune' (depth-1) (tt ()) 
                     in (tot *. w, Node (const normed)) 
    in Dist.normalise' (Dist.prune (List.map reweight trees)) 

  (* flatten : int -> 'a tree -> 'a tree 
   * 
   * flatten for WTreeAlt 
   *) 
  let flatten depth tree = 
    let accum_map (nodes,leaves) (w,tree) = match tree with 
      | Leaf x -> (nodes, PMap.modify_def 0.0 x ((+.) w) leaves)
      | Node tts -> ((w,const (Node tts)) :: nodes, leaves) 
    and build (nodes,leaves) = PMap.foldi (fun x w ts -> (w,const (Leaf x)) :: ts) leaves nodes
    in Node (build (foldl_bounded depth accum_map ([],PMap.empty) tree))
