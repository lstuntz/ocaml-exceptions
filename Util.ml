(* Some functions in this project are not fully implemented. (It will be your
 * job to fill them in.) To indicate this, but still allow OCaml to typecheck
 * the file, those functions are defined to throw a TODO exception. The line
 * that follows this comment defines the existence of that exception. *)
exception TODO

(* When we know that a particular case of a pattern match is impossible, we
 * will raise this exception *)
exception IMPOSSIBLE

type pbool = bool [@@deriving show]
type pint = int [@@deriving show]
type pchar = char [@@deriving show]
type pstring = string [@@deriving show]
