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

type test_result = TestPassed | TestFailed | TestTodo

type test_block = 
  TestBlock : string * ('a * 'b) list * ('a -> 'b) * ('b -> 'b -> bool) * ('a -> string) * ('b -> string) -> test_block

let _SHOW_PASSED_TESTS : bool ref = ref true

let run_tests (tests : test_block list) =
  let (passed,failed,todo) = 
    List.fold_left begin fun (passed,failed,todo) (TestBlock(name,test_cases,run_test,compare,show_input,show_output)) ->
      print_endline ("<" ^ name ^ ">") ;
      List.fold_left begin fun (passed,failed,todo) (input,expected) ->
        try
          let result = run_test input in
          if compare result expected
          then begin
            if ! _SHOW_PASSED_TESTS then begin
              print_endline ("test    : " ^ show_input input) ;
              print_endline ("expected: " ^ show_output expected) ;
              print_endline "PASSED"
            end ;
            (passed+1,failed,todo)
          end else begin
            print_endline ("test    : " ^ show_input input) ;
            print_endline ("expected: " ^ show_output expected) ;
            print_endline ("output  : " ^ show_output result) ;
            print_endline "FAILED" ;
            (passed,failed+1,todo)
          end
        with 
          | TODO -> 
            print_endline ("test    : " ^ show_input input) ;
            print_endline ("expected: " ^ show_output expected) ;
            print_endline "TODO" ;
            (passed,failed,todo+1)
          | _ -> begin
            print_endline ("test    : " ^ show_input input) ;
            print_endline ("expected: " ^ show_output expected) ;
            print_endline ("output  : <exception>") ;
            print_endline "FAILED" ;
            (passed,failed+1,todo)
            end
      end (passed,failed,todo) test_cases
    end (0,0,0) tests
  in
  print_endline "" ;
  print_endline ("TESTS PASSED: " ^ string_of_int passed) ;
  print_endline ("TESTS FAILED: " ^ string_of_int failed) ;
  print_endline ("TESTS TODO: " ^ string_of_int todo)

