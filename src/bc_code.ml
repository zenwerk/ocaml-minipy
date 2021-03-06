open Base
open Import

module Opcode = struct
  type t =
    | POP_TOP
    | ROT_TWO
    | ROT_THREE
    | DUP_TOP
    | DUP_TOP_TWO
    | NOP
    | UNARY_POSITIVE
    | UNARY_NEGATIVE
    | UNARY_NOT
    | UNARY_INVERT
    | BINARY_MATRIX_MULTIPLY
    | INPLACE_MATRIX_MULTIPLY
    | BINARY_POWER
    | BINARY_MULTIPLY
    | BINARY_MODULO
    | BINARY_ADD
    | BINARY_SUBTRACT
    | BINARY_SUBSCR
    | BINARY_FLOOR_DIVIDE
    | BINARY_TRUE_DIVIDE
    | INPLACE_FLOOR_DIVIDE
    | INPLACE_TRUE_DIVIDE
    | GET_AITER
    | GET_ANEXT
    | BEFORE_ASYNC_WITH
    | INPLACE_ADD
    | INPLACE_SUBTRACT
    | INPLACE_MULTIPLY
    | INPLACE_MODULO
    | STORE_SUBSCR
    | DELETE_SUBSCR
    | BINARY_LSHIFT
    | BINARY_RSHIFT
    | BINARY_AND
    | BINARY_XOR
    | BINARY_OR
    | INPLACE_POWER
    | GET_ITER
    | GET_YIELD_FROM_ITER
    | PRINT_EXPR
    | LOAD_BUILD_CLASS
    | YIELD_FROM
    | GET_AWAITABLE
    | INPLACE_LSHIFT
    | INPLACE_RSHIFT
    | INPLACE_AND
    | INPLACE_XOR
    | INPLACE_OR
    | BREAK_LOOP
    | WITH_CLEANUP_START
    | WITH_CLEANUP_FINISH
    | RETURN_VALUE
    | IMPORT_STAR
    | SETUP_ANNOTATIONS
    | YIELD_VALUE
    | POP_BLOCK
    | END_FINALLY
    | POP_EXCEPT
    | STORE_NAME
    | DELETE_NAME
    | UNPACK_SEQUENCE
    | FOR_ITER
    | UNPACK_EX
    | STORE_ATTR
    | DELETE_ATTR
    | STORE_GLOBAL
    | DELETE_GLOBAL
    | LOAD_CONST
    | LOAD_NAME
    | BUILD_TUPLE
    | BUILD_LIST
    | BUILD_SET
    | BUILD_MAP
    | LOAD_ATTR
    | COMPARE_OP
    | IMPORT_NAME
    | IMPORT_FROM
    | JUMP_FORWARD
    | JUMP_IF_FALSE_OR_POP
    | JUMP_IF_TRUE_OR_POP
    | JUMP_ABSOLUTE
    | POP_JUMP_IF_FALSE
    | POP_JUMP_IF_TRUE
    | LOAD_GLOBAL
    | CONTINUE_LOOP
    | SETUP_LOOP
    | SETUP_EXCEPT
    | SETUP_FINALLY
    | LOAD_FAST
    | STORE_FAST
    | DELETE_FAST
    | RAISE_VARARGS
    | CALL_FUNCTION
    | MAKE_FUNCTION
    | BUILD_SLICE
    | LOAD_CLOSURE
    | LOAD_DEREF
    | STORE_DEREF
    | DELETE_DEREF
    | CALL_FUNCTION_KW
    | CALL_FUNCTION_EX
    | SETUP_WITH
    | EXTENDED_ARG
    | LIST_APPEND
    | SET_ADD
    | MAP_ADD
    | LOAD_CLASSDEREF
    | BUILD_LIST_UNPACK
    | BUILD_MAP_UNPACK
    | BUILD_MAP_UNPACK_WITH_CALL
    | BUILD_TUPLE_UNPACK
    | BUILD_SET_UNPACK
    | SETUP_ASYNC_WITH
    | FORMAT_VALUE
    | BUILD_CONST_KEY_MAP
    | BUILD_STRING
    | BUILD_TUPLE_UNPACK_WITH_CALL
    | LOAD_METHOD
    | CALL_METHOD
    | ENTER_FINALLY (*borrowed from RustPython *)
  [@@deriving sexp]

  let of_int opcode =
    match opcode with
    | 1 -> POP_TOP
    | 2 -> ROT_TWO
    | 3 -> ROT_THREE
    | 4 -> DUP_TOP
    | 5 -> DUP_TOP_TWO
    | 9 -> NOP
    | 10 -> UNARY_POSITIVE
    | 11 -> UNARY_NEGATIVE
    | 12 -> UNARY_NOT
    | 15 -> UNARY_INVERT
    | 16 -> BINARY_MATRIX_MULTIPLY
    | 17 -> INPLACE_MATRIX_MULTIPLY
    | 19 -> BINARY_POWER
    | 20 -> BINARY_MULTIPLY
    | 22 -> BINARY_MODULO
    | 23 -> BINARY_ADD
    | 24 -> BINARY_SUBTRACT
    | 25 -> BINARY_SUBSCR
    | 26 -> BINARY_FLOOR_DIVIDE
    | 27 -> BINARY_TRUE_DIVIDE
    | 28 -> INPLACE_FLOOR_DIVIDE
    | 29 -> INPLACE_TRUE_DIVIDE
    | 50 -> GET_AITER
    | 51 -> GET_ANEXT
    | 52 -> BEFORE_ASYNC_WITH
    | 55 -> INPLACE_ADD
    | 56 -> INPLACE_SUBTRACT
    | 57 -> INPLACE_MULTIPLY
    | 59 -> INPLACE_MODULO
    | 60 -> STORE_SUBSCR
    | 61 -> DELETE_SUBSCR
    | 62 -> BINARY_LSHIFT
    | 63 -> BINARY_RSHIFT
    | 64 -> BINARY_AND
    | 65 -> BINARY_XOR
    | 66 -> BINARY_OR
    | 67 -> INPLACE_POWER
    | 68 -> GET_ITER
    | 69 -> GET_YIELD_FROM_ITER
    | 70 -> PRINT_EXPR
    | 71 -> LOAD_BUILD_CLASS
    | 72 -> YIELD_FROM
    | 73 -> GET_AWAITABLE
    | 75 -> INPLACE_LSHIFT
    | 76 -> INPLACE_RSHIFT
    | 77 -> INPLACE_AND
    | 78 -> INPLACE_XOR
    | 79 -> INPLACE_OR
    | 80 -> BREAK_LOOP
    | 81 -> WITH_CLEANUP_START
    | 82 -> WITH_CLEANUP_FINISH
    | 83 -> RETURN_VALUE
    | 84 -> IMPORT_STAR
    | 85 -> SETUP_ANNOTATIONS
    | 86 -> YIELD_VALUE
    | 87 -> POP_BLOCK
    | 88 -> END_FINALLY
    | 89 -> POP_EXCEPT
    | 90 -> STORE_NAME
    | 91 -> DELETE_NAME
    | 92 -> UNPACK_SEQUENCE
    | 93 -> FOR_ITER
    | 94 -> UNPACK_EX
    | 95 -> STORE_ATTR
    | 96 -> DELETE_ATTR
    | 97 -> STORE_GLOBAL
    | 98 -> DELETE_GLOBAL
    | 100 -> LOAD_CONST
    | 101 -> LOAD_NAME
    | 102 -> BUILD_TUPLE
    | 103 -> BUILD_LIST
    | 104 -> BUILD_SET
    | 105 -> BUILD_MAP
    | 106 -> LOAD_ATTR
    | 107 -> COMPARE_OP
    | 108 -> IMPORT_NAME
    | 109 -> IMPORT_FROM
    | 110 -> JUMP_FORWARD
    | 111 -> JUMP_IF_FALSE_OR_POP
    | 112 -> JUMP_IF_TRUE_OR_POP
    | 113 -> JUMP_ABSOLUTE
    | 114 -> POP_JUMP_IF_FALSE
    | 115 -> POP_JUMP_IF_TRUE
    | 116 -> LOAD_GLOBAL
    | 119 -> CONTINUE_LOOP
    | 120 -> SETUP_LOOP
    | 121 -> SETUP_EXCEPT
    | 122 -> SETUP_FINALLY
    | 124 -> LOAD_FAST
    | 125 -> STORE_FAST
    | 126 -> DELETE_FAST
    | 130 -> RAISE_VARARGS
    | 131 -> CALL_FUNCTION
    | 132 -> MAKE_FUNCTION
    | 133 -> BUILD_SLICE
    | 135 -> LOAD_CLOSURE
    | 136 -> LOAD_DEREF
    | 137 -> STORE_DEREF
    | 138 -> DELETE_DEREF
    | 141 -> CALL_FUNCTION_KW
    | 142 -> CALL_FUNCTION_EX
    | 143 -> SETUP_WITH
    | 144 -> EXTENDED_ARG
    | 145 -> LIST_APPEND
    | 146 -> SET_ADD
    | 147 -> MAP_ADD
    | 148 -> LOAD_CLASSDEREF
    | 149 -> BUILD_LIST_UNPACK
    | 150 -> BUILD_MAP_UNPACK
    | 151 -> BUILD_MAP_UNPACK_WITH_CALL
    | 152 -> BUILD_TUPLE_UNPACK
    | 153 -> BUILD_SET_UNPACK
    | 154 -> SETUP_ASYNC_WITH
    | 155 -> FORMAT_VALUE
    | 156 -> BUILD_CONST_KEY_MAP
    | 157 -> BUILD_STRING
    | 158 -> BUILD_TUPLE_UNPACK_WITH_CALL
    | 160 -> LOAD_METHOD
    | 161 -> CALL_METHOD
    | 250 -> ENTER_FINALLY
    | i -> Printf.failwithf "unknown opcode %d" i ()
end

type opcode_with_arg =
  { opcode : Opcode.t
  ; arg : int
  ; lineno : int
  }
[@@deriving sexp]

type 'const t =
  { opcodes : opcode_with_arg array
  ; consts : 'const array
  ; varnames : string array
  ; names : string array
  ; filename : string
  }
[@@deriving sexp]

let cmpop_of_int = function
  | 0 -> Ast.Lt
  | 1 -> LtE
  | 2 -> Eq
  | 3 -> NotEq
  | 4 -> Gt
  | 5 -> GtE
  | 6 -> In
  | 7 -> NotIn
  | 8 -> Is
  | 9 -> IsNot
  | id -> errorf "unknown comparison id %d" id

let int_of_cmpop = function
  | Ast.Lt -> 0
  | LtE -> 1
  | Eq -> 2
  | NotEq -> 3
  | Gt -> 4
  | GtE -> 5
  | In -> 6
  | NotIn -> 7
  | Is -> 8
  | IsNot -> 9
