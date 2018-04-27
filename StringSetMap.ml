open Util

(* This file instantiates the Set module from the OCaml standard library with
 * the string type as StringSet, and likewise for the Map module as StringMap.
 * There is some included trickery to teach OCaml how to derive show for
 * compound types that contain string_set or ('a string_map).
 *
 * For most purposes, just know that you have access to two types:
 *
 *     string_set
 *     'a string_map
 *
 * and access to all of the standard library functions mentioned here:
 *
 *     https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html
 *     https://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.S.html
 *
 * which are accessible from StringSet and StringMap modules, e.g.,
 * StringSet.union or StringMap.add
 *)

let pp_set 
  (pp_elem : Format.formatter -> 'a -> unit) 
  (fmt : Format.formatter) 
  (xs : 'a list) 
  : unit =
    Format.fprintf fmt "@[<2>{" ;
    List.iteri begin fun i x ->
      if i <> 0 then Format.fprintf fmt ";@ " ;
      pp_elem fmt x
    end xs ;
    Format.fprintf fmt "@,}@]" 

let pp_map
  (pp_key : Format.formatter -> 'a -> unit)
  (pp_val : Format.formatter -> 'b -> unit)
  (fmt : Format.formatter)
  (kvs : ('a * 'b) list)
  : unit =
    Format.fprintf fmt "@[<2>{" ;
    List.iteri begin fun i (k,v) ->
      if i <> 0 then Format.fprintf fmt ";@ " ;
      pp_key fmt k ;
      Format.fprintf fmt ":" ;
      pp_val fmt v
    end kvs ;
    Format.fprintf fmt "@,}@]" 

module StringSet = struct
  include Set.Make(String)
  let pp (fmt : Format.formatter) (ss : t) : unit = 
    pp_set pp_pstring fmt (elements ss)
end

module StringMap = struct
  include Map.Make(String)
  let pp (pp_val : Format.formatter -> 'a -> unit) (fmt : Format.formatter) (kvs : 'a t) : unit = 
    pp_map pp_pstring pp_val fmt (bindings kvs)
end

type string_set = StringSet.t
[@@deriving show]

type 'a string_map = 'a StringMap.t
[@@deriving show]

let string_set_map_examples () =
  print_endline ([%show: string list] ["x";"y";"z";"x";"y";"z"]) ;
  print_endline ([%show: string_set]  (StringSet.of_list ["x";"y";"z";"x";"y";"z"])) ;
  print_endline ([%show: int string_map] (List.fold_right (fun (k,v) -> StringMap.add k v) [("x",1);("y",2);("z",3)] StringMap.empty))

(*
let _ = string_set_map_examples ()
*)
