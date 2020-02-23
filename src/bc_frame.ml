open Base
open Import

type t =
  { stack : Bc_value.t Stack.t
  ; code : Bc_value.code
  ; mutable counter : int
  ; local_scope : Bc_scope.t
  ; global_scope : Bc_scope.t
  ; builtins : Bc_scope.t
  ; parent_frame : t option
  }

let create ~code ~local_scope ~global_scope ~builtins ~parent_frame =
  { stack = Stack.create ()
  ; code
  ; counter = 0
  ; local_scope
  ; global_scope
  ; builtins
  ; parent_frame
  }

let top_frame ~code ~global_scope ~builtins =
  create
    ~code
    ~local_scope:(Bc_scope.create ())
    ~global_scope
    ~builtins
    ~parent_frame:None

let call_frame t ~code ~local_scope =
  create
    ~code
    ~local_scope
    ~global_scope:t.global_scope
    ~builtins:t.builtins
    ~parent_frame:(Some t)

type internal_action =
  | Continue (* Different from loop continue. *)
  | Jump_rel of int
  | Jump_abs of int
  | Call_fn of
      { code : Bc_value.code
      ; local_scope : Bc_scope.t
      }
  | Return of Bc_value.t

let push_and_continue stack v =
  Stack.push stack v;
  Continue

let pop_top stack =
  ignore (Stack.pop_exn stack : Bc_value.t);
  Continue

let rot_two stack =
  let a = Stack.pop_exn stack in
  let b = Stack.pop_exn stack in
  Stack.push stack a;
  push_and_continue stack b

let rot_three stack =
  let a = Stack.pop_exn stack in
  let b = Stack.pop_exn stack in
  let c = Stack.pop_exn stack in
  Stack.push stack a;
  Stack.push stack c;
  push_and_continue stack b

let dup_top stack =
  let a = Stack.top_exn stack in
  push_and_continue stack a

let dup_top_two stack =
  let a = Stack.pop_exn stack in
  let b = Stack.top_exn stack in
  Stack.push stack b;
  Stack.push stack a;
  push_and_continue stack a

module Unary_op = struct
  type t =
    | Positive
    | Negative
    | Not
    | Invert

  let apply t _v =
    match t with
    | Positive -> failwith "Unsupported: Positive"
    | Negative -> failwith "Unsupported: Negative"
    | Not -> failwith "Unsupported: Not"
    | Invert -> failwith "Unsupported: Invert"
end

module Binary_op = struct
  type t =
    | Matrix_multiply
    | Power
    | Multiply
    | Add
    | Subtract
    | Subscr
    | Floor_divide
    | True_divide
    | Modulo
    | Lshift
    | Rshift
    | And
    | Xor
    | Or

  let bin_add v1 v2 =
    match (v1 : Bc_value.t), (v2 : Bc_value.t) with
    | Int v1, Int v2 -> Bc_value.Int (Z.add v1 v2)
    | _, _ -> errorf "TypeError in add"

  let bin_mult v1 v2 =
    match (v1 : Bc_value.t), (v2 : Bc_value.t) with
    | Int v1, Int v2 -> Bc_value.Int (Z.mul v1 v2)
    | _, _ -> errorf "TypeError in add"

  let apply t v1 v2 =
    match t with
    | Matrix_multiply -> failwith "Unsupported: Matrix_multiply"
    | Power -> failwith "Unsupported: Power"
    | Multiply -> bin_mult v1 v2
    | Add -> bin_add v1 v2
    | Subtract -> failwith "Unsupported: Subtract"
    | Subscr -> failwith "Unsupported: Subscr"
    | Floor_divide -> failwith "Unsupported: Floor_divide"
    | True_divide -> failwith "Unsupported: True_divide"
    | Modulo -> failwith "Unsupported: Modulo"
    | Lshift -> failwith "Unsupported: Lshift"
    | Rshift -> failwith "Unsupported: Rshift"
    | And -> failwith "Unsupported: And"
    | Xor -> failwith "Unsupported: Xor"
    | Or -> failwith "Unsupported: Or"

  let apply_inplace t _v1 _v2 =
    match t with
    | Matrix_multiply -> failwith "Unsupported: Matrix_multiply"
    | Power -> failwith "Unsupported: Power"
    | Multiply -> failwith "Unsupported: Multiply"
    | Add -> failwith "Unsupported: Add"
    | Subtract -> failwith "Unsupported: Subtract"
    | Subscr -> failwith "Unsupported: Subscr"
    | Floor_divide -> failwith "Unsupported: Floor_divide"
    | True_divide -> failwith "Unsupported: True_divide"
    | Modulo -> failwith "Unsupported: Modulo"
    | Lshift -> failwith "Unsupported: Lshift"
    | Rshift -> failwith "Unsupported: Rshift"
    | And -> failwith "Unsupported: And"
    | Xor -> failwith "Unsupported: Xor"
    | Or -> failwith "Unsupported: Or"
end

let unary op stack =
  let tos = Stack.pop_exn stack in
  let tos = Unary_op.apply op tos in
  push_and_continue stack tos

let binary op stack =
  let tos = Stack.pop_exn stack in
  let tos1 = Stack.pop_exn stack in
  let tos = Binary_op.apply op tos1 tos in
  push_and_continue stack tos

let inplace op stack =
  let tos = Stack.pop_exn stack in
  let tos1 = Stack.pop_exn stack in
  let tos = Binary_op.apply_inplace op tos1 tos in
  push_and_continue stack tos

let load_fast t ~arg =
  let name = t.code.varnames.(arg) in
  match Bc_scope.find t.local_scope t.code.varnames.(arg) with
  | Some v -> push_and_continue t.stack v
  | None -> Printf.failwithf "local %s is not defined" name ()

let store_fast t ~arg =
  let tos = Stack.pop_exn t.stack in
  Bc_scope.set t.local_scope t.code.varnames.(arg) tos;
  Continue

let delete_fast t ~arg =
  Bc_scope.remove t.local_scope t.code.varnames.(arg);
  Continue

let load_global t ~arg =
  let name = t.code.names.(arg) in
  match Bc_scope.find t.global_scope name with
  | Some v -> push_and_continue t.stack v
  | None -> Printf.failwithf "global %s is not defined" name ()

let store_global t ~arg =
  let tos = Stack.pop_exn t.stack in
  Bc_scope.set t.global_scope t.code.names.(arg) tos;
  Continue

let delete_global t ~arg =
  Bc_scope.remove t.global_scope t.code.names.(arg);
  Continue

let popn stack n =
  let rec loop acc n =
    match n with
    | 0 -> acc
    | n -> loop (Stack.pop_exn stack :: acc) (n - 1)
  in
  loop [] n

let popn_pairs stack n =
  let rec loop acc n =
    match n with
    | 0 -> acc
    | n ->
      let a = Stack.pop_exn stack in
      let b = Stack.pop_exn stack in
      loop ((a, b) :: acc) (n - 1)
  in
  loop [] n

let build_tuple t ~arg =
  let tuple = popn t.stack arg |> Array.of_list in
  push_and_continue t.stack (Tuple tuple)

let eval_one t opcode ~arg =
  match (opcode : Bc_code.Opcode.t) with
  | POP_TOP -> pop_top t.stack
  | ROT_TWO -> rot_two t.stack
  | ROT_THREE -> rot_three t.stack
  | DUP_TOP -> dup_top t.stack
  | DUP_TOP_TWO -> dup_top_two t.stack
  | NOP -> Continue
  | UNARY_POSITIVE -> unary Positive t.stack
  | UNARY_NEGATIVE -> unary Negative t.stack
  | UNARY_NOT -> unary Not t.stack
  | UNARY_INVERT -> unary Invert t.stack
  | BINARY_MATRIX_MULTIPLY -> binary Matrix_multiply t.stack
  | INPLACE_MATRIX_MULTIPLY -> inplace Matrix_multiply t.stack
  | BINARY_POWER -> binary Power t.stack
  | BINARY_MULTIPLY -> binary Multiply t.stack
  | BINARY_MODULO -> binary Modulo t.stack
  | BINARY_ADD -> binary Add t.stack
  | BINARY_SUBTRACT -> binary Subtract t.stack
  | BINARY_SUBSCR -> binary Subscr t.stack
  | BINARY_FLOOR_DIVIDE -> binary Floor_divide t.stack
  | BINARY_TRUE_DIVIDE -> binary True_divide t.stack
  | INPLACE_FLOOR_DIVIDE -> inplace Floor_divide t.stack
  | INPLACE_TRUE_DIVIDE -> inplace True_divide t.stack
  | GET_AITER -> failwith "Unsupported: GET_AITER"
  | GET_ANEXT -> failwith "Unsupported: GET_ANEXT"
  | BEFORE_ASYNC_WITH -> failwith "Unsupported: BEFORE_ASYNC_WITH"
  | INPLACE_ADD -> inplace Add t.stack
  | INPLACE_SUBTRACT -> inplace Subtract t.stack
  | INPLACE_MULTIPLY -> inplace Multiply t.stack
  | INPLACE_MODULO -> inplace Modulo t.stack
  | STORE_SUBSCR -> failwith "Unsupported: STORE_SUBSCR"
  | DELETE_SUBSCR -> failwith "Unsupported: DELETE_SUBSCR"
  | BINARY_LSHIFT -> binary Lshift t.stack
  | BINARY_RSHIFT -> binary Rshift t.stack
  | BINARY_AND -> binary And t.stack
  | BINARY_XOR -> binary Xor t.stack
  | BINARY_OR -> binary Or t.stack
  | INPLACE_POWER -> inplace Power t.stack
  | GET_ITER -> failwith "Unsupported: GET_ITER"
  | GET_YIELD_FROM_ITER -> failwith "Unsupported: GET_YIELD_FROM_ITER"
  | PRINT_EXPR -> failwith "Unsupported: PRINT_EXPR"
  | LOAD_BUILD_CLASS -> failwith "Unsupported: LOAD_BUILD_CLASS"
  | YIELD_FROM -> failwith "Unsupported: YIELD_FROM"
  | GET_AWAITABLE -> failwith "Unsupported: GET_AWAITABLE"
  | INPLACE_LSHIFT -> inplace Lshift t.stack
  | INPLACE_RSHIFT -> inplace Rshift t.stack
  | INPLACE_AND -> inplace And t.stack
  | INPLACE_XOR -> inplace Xor t.stack
  | INPLACE_OR -> inplace Or t.stack
  | BREAK_LOOP -> failwith "Unsupported: BREAK_LOOP"
  | WITH_CLEANUP_START -> failwith "Unsupported: WITH_CLEANUP_START"
  | WITH_CLEANUP_FINISH -> failwith "Unsupported: WITH_CLEANUP_FINISH"
  | RETURN_VALUE -> Return (Stack.pop_exn t.stack)
  | IMPORT_STAR -> failwith "Unsupported: IMPORT_STAR"
  | SETUP_ANNOTATIONS -> failwith "Unsupported: SETUP_ANNOTATIONS"
  | YIELD_VALUE -> failwith "Unsupported: YIELD_VALUE"
  | POP_BLOCK -> failwith "Unsupported: POP_BLOCK"
  | END_FINALLY -> failwith "Unsupported: END_FINALLY"
  | POP_EXCEPT -> failwith "Unsupported: POP_EXCEPT"
  | STORE_NAME ->
    let name = t.code.names.(arg) in
    let value = Stack.pop_exn t.stack in
    Bc_scope.set t.local_scope name value;
    Continue
  | DELETE_NAME -> failwith "Unsupported: DELETE_NAME"
  | UNPACK_SEQUENCE -> failwith "Unsupported: UNPACK_SEQUENCE"
  | FOR_ITER -> failwith "Unsupported: FOR_ITER"
  | UNPACK_EX -> failwith "Unsupported: UNPACK_EX"
  | STORE_ATTR -> failwith "Unsupported: STORE_ATTR"
  | DELETE_ATTR -> failwith "Unsupported: DELETE_ATTR"
  | STORE_GLOBAL -> store_global t ~arg
  | DELETE_GLOBAL -> delete_global t ~arg
  | LOAD_CONST -> push_and_continue t.stack t.code.consts.(arg)
  | LOAD_NAME ->
    let name = t.code.names.(arg) in
    let value =
      match Bc_scope.find t.local_scope name with
      | Some v -> v
      | None ->
        (match Bc_scope.find t.global_scope name with
        | Some v -> v
        | None ->
          (match Bc_scope.find t.builtins name with
          | Some v -> v
          | None -> Printf.failwithf "NameError: name '%s' is not defined" name ()))
    in
    push_and_continue t.stack value
  | BUILD_TUPLE -> build_tuple t ~arg
  | BUILD_LIST -> failwith "Unsupported: BUILD_LIST"
  | BUILD_SET -> failwith "Unsupported: BUILD_SET"
  | BUILD_MAP -> failwith "Unsupported: BUILD_MAP"
  | LOAD_ATTR -> failwith "Unsupported: LOAD_ATTR"
  | COMPARE_OP -> failwith "Unsupported: COMPARE_OP"
  | IMPORT_NAME -> failwith "Unsupported: IMPORT_NAME"
  | IMPORT_FROM -> failwith "Unsupported: IMPORT_FROM"
  | JUMP_FORWARD -> Jump_rel arg
  | JUMP_IF_FALSE_OR_POP ->
    let v = Stack.top_exn t.stack in
    if not (Bc_value.to_bool v)
    then Jump_abs arg
    else (
      ignore (Stack.pop_exn t.stack : Bc_value.t);
      Continue)
  | JUMP_IF_TRUE_OR_POP ->
    let v = Stack.top_exn t.stack in
    if Bc_value.to_bool v
    then Jump_abs arg
    else (
      ignore (Stack.pop_exn t.stack : Bc_value.t);
      Continue)
  | JUMP_ABSOLUTE -> Jump_abs arg
  | POP_JUMP_IF_FALSE ->
    let v = Stack.pop_exn t.stack in
    if not (Bc_value.to_bool v) then Jump_abs arg else Continue
  | POP_JUMP_IF_TRUE ->
    let v = Stack.pop_exn t.stack in
    if Bc_value.to_bool v then Jump_abs arg else Continue
  | LOAD_GLOBAL -> load_global t ~arg
  | CONTINUE_LOOP -> failwith "Unsupported: CONTINUE_LOOP"
  | SETUP_LOOP -> failwith "Unsupported: SETUP_LOOP"
  | SETUP_EXCEPT -> failwith "Unsupported: SETUP_EXCEPT"
  | SETUP_FINALLY -> failwith "Unsupported: SETUP_FINALLY"
  | LOAD_FAST -> load_fast t ~arg
  | STORE_FAST -> store_fast t ~arg
  | DELETE_FAST -> delete_fast t ~arg
  | RAISE_VARARGS -> failwith "Unsupported: RAISE_VARARGS"
  | CALL_FUNCTION ->
    let n_kwargs = arg / 256 in
    let n_args = arg % 256 in
    let _kwargs = popn_pairs t.stack n_kwargs in
    let pos_args = popn t.stack n_args in
    let fn = Stack.pop_exn t.stack in
    (match fn with
    | Builtin_fn { name = _; fn } ->
      let value = fn pos_args in
      push_and_continue t.stack value
    | Function { name = _; code; args; defaults = _ } ->
      let local_scope = Bc_scope.create () in
      List.iter2_exn args.args pos_args ~f:(fun arg_name value ->
          Bc_scope.set local_scope arg_name value);
      Call_fn { code; local_scope }
    | _ ->
      errorf "'%s' object is not callable" (Bc_value.type_ fn |> Bc_value.Type_.to_string))
  | MAKE_FUNCTION ->
    let name = Stack.pop_exn t.stack |> Bc_value.str_exn in
    let code, args = Stack.pop_exn t.stack |> Bc_value.code_exn in
    let defaults = popn t.stack arg in
    let value = Bc_value.Function { name; code; args; defaults } in
    push_and_continue t.stack value
  | BUILD_SLICE -> failwith "Unsupported: BUILD_SLICE"
  | LOAD_CLOSURE -> failwith "Unsupported: LOAD_CLOSURE"
  | LOAD_DEREF -> failwith "Unsupported: LOAD_DEREF"
  | STORE_DEREF -> failwith "Unsupported: STORE_DEREF"
  | DELETE_DEREF -> failwith "Unsupported: DELETE_DEREF"
  | CALL_FUNCTION_KW -> failwith "Unsupported: CALL_FUNCTION_KW"
  | CALL_FUNCTION_EX -> failwith "Unsupported: CALL_FUNCTION_EX"
  | SETUP_WITH -> failwith "Unsupported: SETUP_WITH"
  | EXTENDED_ARG -> failwith "Unsupported: EXTENDED_ARG"
  | LIST_APPEND -> failwith "Unsupported: LIST_APPEND"
  | SET_ADD -> failwith "Unsupported: SET_ADD"
  | MAP_ADD -> failwith "Unsupported: MAP_ADD"
  | LOAD_CLASSDEREF -> failwith "Unsupported: LOAD_CLASSDEREF"
  | BUILD_LIST_UNPACK -> failwith "Unsupported: BUILD_LIST_UNPACK"
  | BUILD_MAP_UNPACK -> failwith "Unsupported: BUILD_MAP_UNPACK"
  | BUILD_MAP_UNPACK_WITH_CALL -> failwith "Unsupported: BUILD_MAP_UNPACK_WITH_CALL"
  | BUILD_TUPLE_UNPACK -> failwith "Unsupported: BUILD_TUPLE_UNPACK"
  | BUILD_SET_UNPACK -> failwith "Unsupported: BUILD_SET_UNPACK"
  | SETUP_ASYNC_WITH -> failwith "Unsupported: SETUP_ASYNC_WITH"
  | FORMAT_VALUE -> failwith "Unsupported: FORMAT_VALUE"
  | BUILD_CONST_KEY_MAP -> failwith "Unsupported: BUILD_CONST_KEY_MAP"
  | BUILD_STRING -> failwith "Unsupported: BUILD_STRING"
  | BUILD_TUPLE_UNPACK_WITH_CALL -> failwith "Unsupported: BUILD_TUPLE_UNPACK_WITH_CALL"
  | LOAD_METHOD -> failwith "Unsupported: LOAD_METHOD"
  | CALL_METHOD -> failwith "Unsupported: CALL_METHOD"

type action =
  | Continue
  | Call_fn of
      { code : Bc_value.code
      ; local_scope : Bc_scope.t
      }
  | Return of Bc_value.t

let eval_step t =
  if t.counter >= Array.length t.code.opcodes
  then Return Bc_value.none
  else (
    let opcode, arg = t.code.opcodes.(t.counter) in
    match eval_one t opcode ~arg with
    | Continue ->
      t.counter <- t.counter + 1;
      Continue
    | Call_fn { code; local_scope } ->
      t.counter <- t.counter + 1;
      Call_fn { code; local_scope }
    | Jump_rel i ->
      t.counter <- t.counter + i;
      Continue
    | Jump_abs a ->
      t.counter <- a;
      Continue
    | Return v -> Return v)

let function_call_returned t v = Stack.push t.stack v