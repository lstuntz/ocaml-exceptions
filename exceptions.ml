(* Name: <Lindsey Stuntz> *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* Final Project *)

open Util
open StringSetMap

(* Before merlin will work, first execute:
 *
 *     > make
 *
 * To run this file, execute:
 *
 *     > make hw3
 *)

(********************
 * Syntax for types *
 ********************)

(* τ ∈ ty ⩴ bool | τ ⇒ τ | empty | unit | τ + τ | τ × τ
 *)
type ty =
  | Bool
  | Nat
  | Fun of ty * ty
  | Prod of ty * ty
[@@deriving show {with_path = false}]

(**************************
 * Syntax for expressions *
 **************************)

(* x ∈ var ≈ 𝕊
*)
type var = string
[@@deriving show {with_path = false}]

(* e ∈ exp ⩴ true | false | if(e){e}{e}
 *         | zero | succ(e) | pred(e) | iszero(e)
 *         | x | λx:τ.e | e e | ⟨e,e⟩
 *         | projl(e) | projr(e) | error
 *)
type exp =
  | True
  | False
  | If of exp * exp * exp
  | Zero
  | Succ of exp
  | Pred of exp
  | IsZero of exp
  | Var of var
  | Lambda of var * ty * exp
  | Apply of exp * exp
  | Pair of exp * exp
  | Projl of exp
  | Projr of exp
  | Error
[@@deriving show {with_path = false}]

(*********************
 * Syntax for values *
 *********************)

(* nv ∈ nval ⩴ zero | succ(nv)
*)
type natval =
  | VZero
  | VSucc of natval
[@@deriving show {with_path = false}]

(* v ∈ value ⩴ true | false
 *           | n
 *           | ⟨v,v⟩
 *           | λ(x:τ).e
*)
type value =
  | VTrue
  | VFalse
  | VNat of natval
  | VPair of value * value
  | VLambda of var * ty * exp
[@@deriving show {with_path = false}]

(**********************************
 * Free variables for expressions *
 **********************************)

(* FV ∈ exp → ℘(var)
 * efree_vars e ≡ FV(e)
 *)
let rec free_vars (e0 : exp) : string_set = match e0 with
  | True -> StringSet.empty
  | False -> StringSet.empty
  | If(e1,e2,e3) ->
      StringSet.union (StringSet.union (free_vars e1) (free_vars e2))
        (free_vars e3)
  | Zero -> StringSet.empty
  | Succ(e) -> free_vars e
  | Pred(e) -> free_vars e
  | IsZero(e) -> free_vars e
  | Var(x) -> StringSet.of_list [x]
  | Lambda(x,t,e) -> StringSet.remove x (free_vars e)
  | Apply(e1,e2) -> StringSet.union (free_vars e1) (free_vars e2)
  | Pair(e1,e2) -> StringSet.union (free_vars e1) (free_vars e2)
  | Projl(e) -> free_vars e
  | Projr(e) -> free_vars e
  | Error -> StringSet.empty

exception SCOPE_ERROR
exception TYPE_ERROR

(***********************************************
 * Substitution for expressions in expressions *
 ***********************************************)

(* Non-capture-avoiding substitution for expressions in expressions. Because
 * this is non-capture-avoiding, it assumes that the expression being
 * substituted is closed.
 *
 *   esubst_e_i x e′ e
 *
 * Assumption: e′ is closed
 *
 * Do not use this function directly. Instead, use esubst_e which checks the
 * invariant.
 *)
let rec esubst_e_i (x : var) (e' : exp) (e0 : exp) : exp = match e0 with
  | True -> True
  | False -> False
  | If(e1,e2,e3) -> If(esubst_e_i x e' e1,esubst_e_i x e' e2,esubst_e_i x e' e3)
  | Zero -> Zero
  | Succ(e) -> Succ(esubst_e_i x e' e)
  | Pred(e) -> Pred(esubst_e_i x e' e)
  | IsZero(e) -> IsZero(esubst_e_i x e' e)
  | Pair(e1,e2) -> Pair(esubst_e_i x e' e1,esubst_e_i x e' e2)
  | Projl(e) -> Projl(esubst_e_i x e' e)
  | Projr(e) -> Projr(esubst_e_i x e' e)
  | Var(y) -> if x = y then e' else Var(y)
  | Lambda(y,t,e) ->
      if x = y
      then Lambda(x,t,e)
      else Lambda(y,t,esubst_e_i x e' e)
  | Apply(e1,e2) -> Apply(esubst_e_i x e' e1,esubst_e_i x e' e2)
  | Error -> Error

exception NOT_CLOSED_ERROR

(* A version of non-capture-avoiding substitution that raises an exception if
 * its required assumptions are not satisfied.
 *
 * [_↦_]_ ∈ var × exp × exp → exp
 * esubst_e x e′ e ≡ [x↦e′]e
 *
 * Raises exception if e′ is not closed
 *)
let esubst_e (x : var) (e' : exp) (e : exp) : exp =
  if StringSet.equal (free_vars e') StringSet.empty
  then esubst_e_i x e' e
  else raise NOT_CLOSED_ERROR

(**********************************
 * Small step transition relation *
 **********************************)

(* Converting natval to exp *)
let rec exp_of_natval (nv0 : natval) : exp = match nv0 with
  | VZero -> Zero
  | VSucc(nv) -> Succ(exp_of_natval nv)

(* Converting val to exp *)
let rec exp_of_val (v0 : value) : exp = match v0 with
  | VTrue -> True
  | VFalse -> False
  | VNat(nv) -> exp_of_natval nv
  | VPair(v1,v2) -> Pair(exp_of_val v1,exp_of_val v2)
  | VLambda(x,t,e) -> Lambda(x,t,e)

(* A result is either a value, an expression, or the symbol `stuck`.
 *
 * r ∈ result ⩴ v | e | stuck
*)
type result =
  | Val of value
  | Step of exp
  | Stuck
  | Err
[@@deriving show {with_path = false}]

(* The small-step relation e —→ e
 *
 * Assumption: e is closed.
 *
 * If step(e) = v, then e is a value (and does not take a step).
 * (i.e., e ∈ val)
 *
 * If step(e) = e′, then e steps to e′.
 * (i.e., e —→ e′)
 *
 * If step(e) = stuck, then e is stuck, that is e is not a value and does not
 * take a step.
 * (i.e., e ∉ val and e —↛)
 *)
let rec step (e0 : exp) : result = match e0 with
  (* true ∈ val *)
  | True -> Val(VTrue)
  (* false ∈ val *)
  | False -> Val(VFalse)
  | If(e1,e2,e3) -> begin match step e1 with
      (* [If-True]
       * if(true){e₂}{e₃} —→ e₂ *)
      | Val(VTrue) -> Step(e2)
      (* [If-False]
       * if(false){e₂}{e₃} —→ e₃ *)
      | Val(VFalse) -> Step(e3)
      (* v ∉ {true,false}
       * ⟹
       * if(v){e₂}{e₃} ∉ val
       * if(v){e₂}{e₃} —↛ *)
      | Val(_) -> Stuck
      (* [If-Cong]
       * e₁ —→ e₁′
       * ⟹
       * if(e₁){e₂}{e₃} —→ if(e₁′){e₂}{e₃} *)
      | Step(e1') -> Step(If(e1',e2,e3))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * if(e₁){e₂}{e₃} ∉ val
       * if(e₁){e₂}{e₃} —↛ *)
      | Stuck -> Stuck
      | Err -> Err
    end
  (* zero ∈ val *)
  | Zero -> Val(VNat(VZero))
  | Succ(e) -> begin match step e with
      (* nv ∈ nval
       * ⟹
       * succ(nv) ∈ nval ⊆ val *)
      | Val(VNat(nv)) -> Val(VNat(VSucc(nv)))
      (* v ∉ nval
       * ⟹
       * succ(v) ∉ val
       * succ(v) —↛ *)
      | Val(_) -> Stuck
      (* [Succ-Cong]
       * e —→ e′
       * succ(e) —→ succ(e′) *)
      | Step(e') -> Step(Succ(e'))
      (* e ∉ val
       * e —↛
       * ⟹
       * succ(e) ∉ val
       * succ(e) —↛ *)
      | Stuck -> Stuck
      | Err -> Err
    end
  | Pred(e) -> begin match step e with
      (* [Pred-Zero]
       * pred(zero) —→ zero *)
      | Val(VNat(VZero)) -> Step(Zero)
      (* [Pred-Succ]
       * pred(succ(nv)) —→ nv *)
      | Val(VNat(VSucc(nv))) -> Step(exp_of_natval nv)
      (* v ∉ nval
       * ⟹
       * pred(v) ∉ val
       * pred(v) —↛ *)
      | Val(_) -> Stuck
      (* [Pred-Cong]
       * e —→ e′
       * ⟹
       * pred(e) —→ pred(e′) *)
      | Step(e') -> Step(Pred(e'))
      (* e ∉ val
       * e —↛
       * ⟹
       * pred(e) ∉ val
       * pred(e) —↛ *)
      | Stuck -> Stuck
      | Err -> Err
    end
  | IsZero(e) -> begin match step e with
      (* [IsZero-Zero]
       * iszero(zero) —→ true *)
      | Val(VNat(VZero)) -> Step(True)
      (* [IsZero-Succ]
       * iszero(succ(nv)) —→ false *)
      | Val(VNat(VSucc(nv))) -> Step(False)
      (* v ∉ nval
       * ⟹
       * iszero(v) ∉ val
       * iszero(v) —↛ *)
      | Val(_) -> Stuck
      (* [IsZero-Cong]
       * e —→ e′
       * ⟹
       * iszero(e) —→ iszero(e′) *)
      | Step(e') -> Step(IsZero(e'))
      (* e ∉ val
       * e —↛
       * ⟹
       * iszero(e) ∉ val
       * iszero(e) —↛ *)
      | Stuck -> Stuck
      | Err -> Err
    end
  | Pair(e1,e2) -> begin match step e1 with
      | Val(v1) -> begin match step e2 with
          (* ⟨v₁,v₂⟩ ∈ val *)
          | Val(v2) -> Val(VPair(v1,v2))
          (* [Pair-Cong-2]
           * e —→ e′
           * ⟹
           * ⟨v,e⟩ —→ ⟨v,e′⟩ *)
          | Step(e2') -> Step(Pair(e1,e2'))
          (* e ∉ val
           * e —↛
           * ⟹
           * ⟨v,e⟩ ∉ val
           * ⟨v,e⟩ —↛ *)
          | Stuck -> Stuck
          | Err -> Err
          end
      (* [Pair-Cong-1]
       * e₁ —→ e₁′
       * ⟹
       * ⟨e₁,e₂⟩ —→ ⟨e₁′,e₂⟩ *)
      | Step(e1') -> Step(Pair(e1',e2))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * ⟨e₁,e₂⟩ ∉ val
       * ⟨e₁,e₂⟩ —↛ *)
      | Stuck -> Stuck
      | Err -> Err
      end
  | Projl(e1) -> begin match step e1 with
      (* [Projl-Pair]
       * projl(⟨v₁,v₂⟩) —→ v₁ *)
      | Val(VPair(v1,v2)) -> Step(exp_of_val v1)
      (* ∄v₁,v₂. v = ⟨v₁,v₂⟩
       * ⟹
       * projl(v) ∉ val
       * projl(v) —↛ *)
      | Val(_) -> Stuck
      (* [Projl-Cong]
       * e —→ e′
       * ⟹
       * projl(e) —→ projl(e′) *)
      | Step(e1') -> Step(Projl(e1'))
      (* e ∉ val
       * e —↛
       * ⟹
       * projl(e) ∉ val
       * projl(e) —↛ *)
      | Stuck -> Stuck
      | Err -> Err
      end
  | Projr(e1) -> begin match step e1 with
      (* [Projr-Pair]
       * projr(⟨v₁,v₂⟩) —→ v₂ *)
      | Val(VPair(v1,v2)) -> Step(exp_of_val v2)
      (* ∄v₁,v₂. v = ⟨v₁,v₂⟩
       * ⟹
       * projr(v) ∉ val
       * projr(v) —↛ *)
      | Val(_) -> Stuck
      (* [Projr-Cong]
       * e —→ e′
       * ⟹
       * projr(e) —→ projr(e′) *)
      | Step(e1') -> Step(Projr(e1'))
      (* e ∉ val
       * e —↛
       * ⟹
       * projr(e) ∉ val
       * projr(e) —↛ *)
      | Stuck -> Stuck
      | Err -> Err
      end
  (* x is not closed *)
  | Var(x) -> raise NOT_CLOSED_ERROR
  (* λ(x:τ).e ∈ val *)
  | Lambda(x,t,e) -> Val(VLambda(x,t,e))
  | Apply(e1,e2) -> begin match step e1 with
      | Val(v1) -> begin match step e2 with
          | Val(v2) -> begin match v1 with
              (* [Apply-Lambda (β)]
               * (λ(x:τ).e)v —→ [x↦v]e *)
              | VLambda(x,t,e) -> Step(esubst_e x (exp_of_val v2) e)
              (* ∄x,τ,e. v₁ = λ(x:τ).e
               * ⟹
               * v₁(v₂) ∉ val
               * v₁(v₂) —↛ *)
              | _ -> Stuck
              end
          (* [Apply-Cong-2]
           * e —→ e′
           * ⟹
           * v(e) —→ v(e′) *)
          | Step(e2') -> Step(Apply(exp_of_val v1, e2'))
          (* e ∉ val
           * e —↛
           * ⟹
           * v(e) ∉ val
           * v(e) —↛ *)
          | Stuck -> Stuck
          (* [E-AppErr2]
           * v₁(error) —→ error *)
          | Err -> Err
          end
      (* [Apply-Cong-1]
       * e₁ —→ e₁′
       * ⟹
       * e₁(e₂) —→ e₁′(e₂) *)
      | Step(e1') -> Step(Apply(e1',e2))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * e₁(e₂) ∉ val
       * e₁(e₂) –↛ *)
      | Stuck -> Stuck
      (* [E-AppErr1]
       * error(t₂) —→ error *)
      | Err -> Err
    end
  | Error -> Err

(* The reflexive transitive closure of the small-step relation e —→* e *)
let rec step_star (e : exp) : exp = match step e with
  | Val(v) -> exp_of_val v
  | Step(e') -> step_star e'
  | Stuck -> e
  | Err -> Error
(*
(***********************************
 * Syntax for type system contexts *
 ***********************************)

(* Γ ∈ tenv ≔ var ⇀ type
*)
type tscope = string_set
[@@deriving show {with_path = false}]

(* S ∈ scope ≔ ℘(tvar)
*)
type tenvv = ty string_map
[@@deriving show {with_path = false}] *)


(* type type_env = (string * ty) list *)

(***********************
 * Well-typed relation *
 ***********************)

type type_env = (string * ty) list

(* A metafunction to look up a variable's type in the type environment *)
let rec infer_var (tenv : type_env) (x : string) : ty = match tenv with
  | [] -> raise SCOPE_ERROR
  | (y,t)::tenv' -> if x = y then t else infer_var tenv' x

(* Typing relation encoded as an inference metafunction. *)
let rec infer (tenv : type_env) (e0 : exp) : ty = match e0 with
  (* ———————————————
   * Γ ⊢ true : bool
   *)
  | True -> Bool

  (* ———————————————
   * Γ ⊢ true : bool
   *)
  | False -> Bool

  (* Γ ⊢ e₁ : bool
   * Γ ⊢ e₂ : τ
   * Γ ⊢ e₃ : τ
   * ———————————————–––––––
   * Γ ⊢ if(e₁){e₂}{e₃} : τ
   *)
  | If(e1,e2,e3) ->
      let t1 = infer tenv e1 in
      let t2 = infer tenv e2 in
      let t3 = infer tenv e3 in
      if not (t1 = Bool) then raise TYPE_ERROR else
      if not (t2 = t3) then raise TYPE_ERROR else
        t2
  (*
   * Γ ⊢ zero : nat
   *)
  | Zero -> Nat

  (* [Succ]
   * Γ ⊢ e : nat
   * ⟹
   * Γ ⊢ succ(e) : nat
   *)
  | Succ(e) ->
      let t = infer tenv e in
      if not (t = Nat) then raise TYPE_ERROR else
        Nat

  (*
   * S , Γ ⊢ e : nat
   * ⟹
   * S , Γ ⊢ pred(e) : nat
   *)
  | Pred(e) ->
      let t = infer tenv e in
      if not (t = Nat) then raise TYPE_ERROR else
        Nat

  (* [IsZero]
   * Γ ⊢ e : nat
   * ⟹
   * Γ ⊢ iszero(e) : bool
   *)
  | IsZero(e) ->
      let t = infer tenv e in
      if not (t = Nat) then raise TYPE_ERROR else
          Bool

  (* x:τ ∈ Γ
   * —————————
   * Γ ⊢ x : τ
   *)
  | Var(x) -> infer_var tenv x

  (* x:τ₁,Γ ⊢ e : τ₂
   * ————————————————————
   * Γ ⊢ λx:τ.e : τ₁ ⇒ τ₂
   *)
  | Lambda(x,t1,e) ->
      let t2 = infer ((x,t1)::tenv) e in
      Fun(t1,t2)

  (* Γ ⊢ e₁ : τ₁ ⇒ τ₂
   * Γ ⊢ e₂ : τ₁
   * ——————————————————————————————
   * Γ ⊢ e₁ e₂ : τ₂
   *)
  | Apply(e1,e2) ->
      let t1 = infer tenv e1 in
      let t2 = infer tenv e2 in
      begin match t1 with
      | Fun(t11,t12) ->
          if not (t11 = t2) then raise TYPE_ERROR else
          t12
      | _ -> raise TYPE_ERROR
      end

  (* Γ ⊢ e₁ : τ₁
   * Γ ⊢ e₂ : τ₂
   * ———————————————————————
   * Γ ⊢ ⟨e₁,e₂⟩ : (τ₁ × τ₂)
   *)
  | Pair(e1,e2) ->
    let t1 = infer tenv e1 in
    let t2 = infer tenv e2 in
    Prod(t1,t2)

  (* Γ ⊢ e : (τ₁ × τ₂)
   * —————————————————
   * Γ ⊢ projl(e) : τ₁
   *)
  | Projl(e) ->
    let t1 = infer tenv e in
    begin match t1 with
      |Prod(t11,t12) ->
        t11
      |_ -> raise TYPE_ERROR
    end

  (* Γ ⊢ e : (τ₁ × τ₂)
   * —————————————————
   * Γ ⊢ projr(e) : τ₂
   *)
  | Projr(e) ->
    let t1 = infer tenv e in
    begin match t1 with
      |Prod(t11,t12) ->
        t12
      |_ -> raise TYPE_ERROR
    end
  | Error -> raise TODO

let _ =
  let free_vars_tests =
    (* test expressions and sets of free variables they should return *)
    [ Var("x")                                     , StringSet.of_list ["x"]
    ; Lambda("x",Bool,Var("x"))                       , StringSet.of_list []
    ; Lambda("x",Bool,Var("y"))                       , StringSet.of_list ["y"]
    (* ; App(Lambda("x",Bool,Var("x")),Var("y"))         , StringSet.of_list ["y"]
    ; Absurd(Var("x"),Bool)                        , StringSet.of_list ["x"]
    ; Lambda("x",Bool,Bullet)                         , StringSet.of_list []
    ; Inl(Var("x"),Sum(Unit,Unit))                 , StringSet.of_list ["x"]
    ; Inr(Var("y"),Sum(Unit,Unit))                 , StringSet.of_list ["y"]
    ; Case(Var("x"),("y",Var("y")),("a",Var("b"))) , StringSet.of_list ["x";"b"]
    ; Lambda("x",Bool,Pair(Var("x"),Var("y")))        , StringSet.of_list ["y"]
    ; Projl(Pair(Var("x"),Bullet))                 , StringSet.of_list ["x"] *)
    ; Projr(Pair(Lambda("x",Bool,Var("x")),Var("y"))) , StringSet.of_list ["y"]
    ]
  in
  let (fv_passed,fv_failed,fv_todo) =
    List.fold_left begin fun (passed,failed,todo) (e,xs) ->
      try
        if not (StringSet.equal xs (free_vars e))
        then begin
          print_endline "!!FAILED:" ;
          print_endline "<free_vars>" ;
          print_endline ("-------- " ^ show_exp e) ;
          print_endline ("RETURNED " ^ show_string_set (free_vars e)) ;
          print_endline ("EXPECTED " ^ show_string_set xs) ;
          (passed,failed+1,todo)
        end
        else begin
          print_endline "PASSED:" ;
          print_endline "<free_vars>" ;
          print_endline ("-- " ^ (show_exp e)) ;
          (passed+1,failed,todo)
        end
      with TODO ->
        print_endline "!!TODO:" ;
        print_endline "<free_vars>" ;
        print_endline ("-- " ^ show_exp e) ;
        (passed,failed,todo+1)
    end (0,0,0) free_vars_tests
  in
  let infer_tests =
    (* test expressions and the types that should be inferred for them *)
    [ Lambda("x",Nat,Var("x"))                                            , Fun(Nat,Nat)
    (* ; App(Lambda("x",Unit,Var("x")),Bullet)                                , Unit
    ; Inl(Bullet,Sum(Unit,Bool))                                        , Sum(Unit,Bool)
    ; Inr(True,Sum(Unit,Bool))                                          , Sum(Unit,Bool)
    ; Lambda("x",Sum(Unit,Bool),Case(Var("x"),("y",False),("z",Var("z")))) , Fun(Sum(Unit,Bool),Bool)
    ; Pair(Bullet,False)                                                , Prod(Unit,Bool)
    ; Lambda("x",Prod(Unit,Bool),Projl(Var("x")))                          , Fun(Prod(Unit,Bool),Unit)
    ; Lambda("x",Prod(Unit,Bool),Projr(Var("x")))                          , Fun(Prod(Unit,Bool),Bool) *)
    ]
  in
  let (ty_passed,ty_failed,ty_todo) =
    List.fold_left begin fun (passed,failed,todo) (e,t) ->
      try
        if not (t = infer [] e)
        then begin
          print_endline "!!FAILED:" ;
          print_endline "<infer>" ;
          print_endline ("-------- " ^ show_exp e) ;
          print_endline ("RETURNED " ^ show_ty (infer [] e)) ;
          print_endline ("EXPECTED " ^ show_ty t) ;
          (passed,failed+1,todo)
        end
        else begin
          print_endline "PASSED:" ;
          print_endline "<infer>" ;
          print_endline ("-- " ^ (show_exp e)) ;
          (passed+1,failed,todo)
        end
      with TODO ->
        print_endline "!!TODO:" ;
        print_endline "<infer>" ;
        print_endline ("-- " ^ show_exp e) ;
        (passed,failed,todo+1)
    end (0,0,0) infer_tests
  in
  print_endline "" ;
  print_endline ("TESTS PASSED: " ^ string_of_int (fv_passed + ty_passed)) ;
  print_endline ("TESTS FAILED: " ^ string_of_int (fv_failed + ty_failed)) ;
  print_endline ("TESTS TODO: " ^ string_of_int (fv_todo + ty_todo))

(* Name: <Lindsey Stuntz> *)
