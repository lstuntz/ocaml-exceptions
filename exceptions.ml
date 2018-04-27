(* Name: <Lindsey Stuntz> *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* HW: HW3 *)

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

(* Types.
 *
 * τ ∈ ty ⩴ bool
 *        | τ ⇒ τ
 *        | empty
 *        | unit
 *        | τ + τ
 *        | τ × τ
 *)
type ty =
  | Bool
  | Fun of ty * ty
  (* New types *)
  | Empty
  | Unit
  | Sum of ty * ty
  | Prod of ty * ty
[@@deriving show {with_path = false}]

(* Expressions.
 *
 * e ∈ exp ⩴ true | false | if(e){e}{e}
 *         | x | λx:τ.e | e e
 *         | absurd(e) as τ
 *         | •
 *         | inl(e) as τ | inr(e) as τ
 *         | case(e){x.e}{x.e}
 *         | ⟨e,e⟩ | projl(e) | projr(e)
 *)
type exp =
  | True
  | False
  | If of exp * exp * exp
  | Var of string
  | Lam of string * ty * exp
  | App of exp * exp
  (* New expressions *)
  | Absurd of exp * ty
  | Bullet
  | Inl of exp * ty
  | Inr of exp * ty
  | Case of exp * (string * exp) * (string * exp)
  | Pair of exp * exp
  | Projl of exp
  | Projr of exp
[@@deriving show {with_path = false}]

(* Free variables metafunction.
 *
 * FV ∈ exp → 𝒫(var)
 * FV(true) ≔ {}
 * FV(false) ≔ {}
 * FV(if(e₁){e₂}{e₃}) ≔ FV(e₁) ∪ FV(e₂) ∪ FV(e₃)
 * FV(x) ≔ {x}
 * FV(λx:τ.e) ≔ FV(e) \ {x}
 * FV(e₁ e₂) ≔ FV(e₁) ∪ FV(e₂)
 * FV(absurd(e) as τ) ≔ FV(e)
 * FV(•) ≔ {}
 * FV(inl(e) as τ) ≔ FV(e)
 * FV(inr(e) as τ) ≔ FV(e)
 * FV(case(e₁){x₂.e₂}{x₃.e₃}) ≔
 *   FV(e₁) ∪ (FV(e₂) \ {x₂}) ∪ (FV(e₃) \ {x₃})
 * FV(⟨e₁,e₂⟩) ≔ FV(e₁) ∪ FV(e₂)
 * FV(projl(e)) ≔ FV(e)
 * FV(projr(e)) ≔ FV(e)
 *)
let rec free_vars (e0 : exp) : string_set = match e0 with
  | True -> StringSet.empty
  | False -> StringSet.empty
  | If(e1,e2,e3) ->
      StringSet.union (StringSet.union (free_vars e1) (free_vars e2))
      (free_vars e3)
  | Var(x) -> StringSet.of_list [x]
  | Lam(x,t,e) -> StringSet.remove x (free_vars e)
  | App(e1,e2) -> StringSet.union (free_vars e1) (free_vars e2)

  (* New cases *)

  | Absurd(e',t) -> free_vars e'
  | Bullet -> StringSet.empty
  | Inl(e,t) -> free_vars e
  | Inr(e,t) -> free_vars e
  | Case(e1,(x2,e2),(x3,e3)) -> StringSet.union (StringSet.union (free_vars e1) (StringSet.remove x2 (free_vars e2))) (StringSet.remove x3 (free_vars e3))
  | Pair(e1,e2) -> StringSet.union (free_vars e1) (free_vars e2)
  | Projl(e) -> free_vars e
  | Projr(e) -> free_vars e

exception SCOPE_ERROR
exception TYPE_ERROR

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
  (* x:τ ∈ Γ
   * —————————
   * Γ ⊢ x : τ
   *)
  | Var(x) -> infer_var tenv x
  (* x:τ₁,Γ ⊢ e : τ₂
   * ————————————————————
   * Γ ⊢ λx:τ.e : τ₁ ⇒ τ₂
   *)
  | Lam(x,t1,e) ->
      let t2 = infer ((x,t1)::tenv) e in
      Fun(t1,t2)
  (* Γ ⊢ e₁ : τ₁ ⇒ τ₂
   * Γ ⊢ e₂ : τ₁
   * ——————————————————————————————
   * Γ ⊢ e₁ e₂ : τ₂
   *)
  | App(e1,e2) ->
      let t1 = infer tenv e1 in
      let t2 = infer tenv e2 in
      begin match t1 with
      | Fun(t11,t12) ->
          if not (t11 = t2) then raise TYPE_ERROR else
          t12
      | _ -> raise TYPE_ERROR
      end

  (* New cases *)

  (* Γ ⊢ e : empty
   * —————————————————
   * Γ ⊢ absurd(e) : τ
   *)
  | Absurd(e,t) ->
    let t1 = infer tenv e in
    if not (t1 = Empty) then raise TYPE_ERROR else
    t

  (* ————————————
   * Γ ⊢ • : unit
   *)
  | Bullet -> Unit

  (* Γ ⊢ e : τ₁
   * ———————————————————————————————
   * Γ ⊢ inl(e) as τ₁ + τ₂ : τ₁ + τ₂
   *)
  | Inl(e,t') ->
    let t1 = infer tenv e in
    begin match t' with
      |Sum(t11,t12) ->
        if not (t1 = t11) then raise TYPE_ERROR else
        t'
      |_ -> raise TYPE_ERROR
    end

  (* Γ ⊢ e : τ₂
   * ———————————————————————————————
   * Γ ⊢ inr(e) as (τ₁ + τ₂) : (τ₁ + τ₂)
   *)
  | Inr(e,t') ->
    let t1 = infer tenv e in
    begin match t' with
      |Sum(t11,t12) ->
        if not (t1 = t12) then raise TYPE_ERROR else
          t'
      |_ -> raise TYPE_ERROR
    end

  (* Γ ⊢ e₁ : (τ₂ + τ₃)
   * x:τ₂,Γ ⊢ e₂ : τ
   * x:τ₃,Γ ⊢ e₃ : τ
   * ——————————————————————————————
   * Γ ⊢ case(e₁){x₂.e₂}{x₃.e₃} : τ
   *)
  | Case(e1,(x2,e2),(x3,e3)) ->
    let t = infer tenv e1 in
    begin match t with
      |Sum(t2,t3) ->
        let t22 = infer ((x2,t2)::tenv) e2 in
        let t33 = infer ((x3,t3)::tenv) e3 in
        if not (t22 = t33) then raise TYPE_ERROR else
        t22
      |_ -> raise TYPE_ERROR
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

let _ =
  let free_vars_tests =
    (* test expressions and sets of free variables they should return *)
    [ Var("x")                                     , StringSet.of_list ["x"]
    ; Lam("x",Bool,Var("x"))                       , StringSet.of_list []
    ; Lam("x",Bool,Var("y"))                       , StringSet.of_list ["y"]
    ; App(Lam("x",Bool,Var("x")),Var("y"))         , StringSet.of_list ["y"]
    ; Absurd(Var("x"),Bool)                        , StringSet.of_list ["x"]
    ; Lam("x",Bool,Bullet)                         , StringSet.of_list []
    ; Inl(Var("x"),Sum(Unit,Unit))                 , StringSet.of_list ["x"]
    ; Inr(Var("y"),Sum(Unit,Unit))                 , StringSet.of_list ["y"]
    ; Case(Var("x"),("y",Var("y")),("a",Var("b"))) , StringSet.of_list ["x";"b"]
    ; Lam("x",Bool,Pair(Var("x"),Var("y")))        , StringSet.of_list ["y"]
    ; Projl(Pair(Var("x"),Bullet))                 , StringSet.of_list ["x"]
    ; Projr(Pair(Lam("x",Bool,Var("x")),Var("y"))) , StringSet.of_list ["y"]
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
    [ Lam("x",Unit,Var("x"))                                            , Fun(Unit,Unit)
    ; App(Lam("x",Unit,Var("x")),Bullet)                                , Unit
    ; Inl(Bullet,Sum(Unit,Bool))                                        , Sum(Unit,Bool)
    ; Inr(True,Sum(Unit,Bool))                                          , Sum(Unit,Bool)
    ; Lam("x",Sum(Unit,Bool),Case(Var("x"),("y",False),("z",Var("z")))) , Fun(Sum(Unit,Bool),Bool)
    ; Pair(Bullet,False)                                                , Prod(Unit,Bool)
    ; Lam("x",Prod(Unit,Bool),Projl(Var("x")))                          , Fun(Prod(Unit,Bool),Unit)
    ; Lam("x",Prod(Unit,Bool),Projr(Var("x")))                          , Fun(Prod(Unit,Bool),Bool)
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
