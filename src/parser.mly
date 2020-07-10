%{
(* Python grammar specification.
   Adapted from: https://docs.python.org/3/reference/grammar.html
   This tries to follow the original LL(1) grammar so is not very
   idiomatic for menhir.
*)

module List = Base.List
module Option = Base.Option
exception ParseError of string
open Ast
let errorf fmt = Printf.ksprintf (fun s -> raise (ParseError s)) fmt

(* 既存のIf条件の先頭に新たに test, body をいい感じにガッチャンコして返す *)
let combine_if loc ~test ~body ~elif ~orelse =
  let orelse =
    List.rev elif (* elif list を反転 | ~~後からパースされたものがけつにくるはずなので反転して定義された順に elif文を取り出しているのだろう~~ *)
    (* 初期値が引数で渡されてきた orelse, それに elif の (test, body) list を畳み込む
       畳み込む結果は [If {elif-test; elif-body; acc}]
       よって  elif が逆順に orelseに畳み込まれていき, initのorelseが最後になるように畳み込まれていく
       得られる結果は -> [If {先頭のelif; orelse=If{2番めのelif; orelse=If{3番目のelif... orelse=initのorelse}}}] のような構造 *)
    |> List.fold ~init:orelse ~f:(fun orelse (test, body) -> (* orelse が acc *)
        [ { loc; value = If { test; body; orelse } } ])
  in
  (* 畳み込んだ結果を orelse に配置し引数の test, body を先頭条件にする If-Ast を返す *)
  { loc; value = If { test; body; orelse } }

(* 空のパラメータを表す *)
let empty_args = { args = []; vararg = None; kwonlyargs = []; kwarg = None }

(* 複数の引数レコードを一つのレコードにマージして返す *)
let merge_parameters parameters =
  let a =
    List.fold parameters
      ~init:empty_args
      ~f:(fun acc arg ->
        match arg with
        | `arg id ->
            (* **kwargs,*argsの後に通常の引数は書けない *)
            if Option.is_some acc.vararg
            then errorf "positional argument %s after vararg" id;
            if Option.is_some acc.kwarg
            then errorf "positional argument %s after kwarg" id;
            { acc with args = id :: acc.args }
        | `kwonlyarg (id, e) ->
            (* a=b は **kwargs の後に書けない *)
            if Option.is_some acc.kwarg
            then errorf "keyword argument %s after kwarg" id;
            { acc with kwonlyargs  = (id, e) :: acc.kwonlyargs }
        | `vararg id ->
            if Option.is_some acc.vararg
            then errorf "duplicate vararg" id; (* *args は複数定義できない *)
            if Option.is_some acc.kwarg
            then errorf "vararg %s after kwarg" id; (* **kwargs の後に *args は書けない *)
            { acc with vararg = Some id }
        | `kwarg id ->
            if Option.is_some acc.kwarg
            then errorf "duplicate kwarg" id; (* **kwargs は複数定義できない *)
            { acc with kwarg = Some id }
      )
  in
  (* 引数名を一つのリストにまとめる *)
  let all_ids =
    a.args @ Option.to_list a.vararg @ Option.to_list a.kwarg @ List.map a.kwonlyargs ~f:fst
  in
  Option.iter (List.find_a_dup all_ids ~compare:String.compare) ~f:(fun dup_id ->
    errorf "duplicate argument name %s" dup_id);
  { a with args = List.rev a.args; kwonlyargs = List.rev a.kwonlyargs }

let merge_args args =
  let args, keywords =
    List.fold args ~init:([], [])  ~f:(fun (acc_a, acc_kw) arg ->
      match arg with
      | `Arg arg ->
          if not (List.is_empty acc_kw)
          then errorf "positional argument follows keyword argument"; (* キーワード引数の後に位置引数はおけない *)
          arg :: acc_a, acc_kw
      | `Keyword kwarg -> acc_a, kwarg :: acc_kw)
  in
  List.rev args, List.rev keywords

let none loc = { loc; value = None_ }
let bool loc b = { loc; value = Bool b }
let num loc v = { loc; value = Num v }
let float loc f = { loc; value = Float f }
let str loc s = { loc; value = Str s }
let name loc s = { loc; value = Name s }
let list loc l = { loc; value = List l }
let dict loc ~key_values = { loc; value = Dict { key_values } }
let listcomp loc ~elt ~generators = { loc; value = ListComp { elt; generators } }
let tuple loc l = { loc; value = Tuple l }
let lambda loc ~args ~body = { loc; value = Lambda { args; body } }
let boolop loc ~op ~values = { loc; value = BoolOp { op; values } }
let binop loc ~left ~op ~right = { loc; value = BinOp { left; op; right } }
let unaryop loc ~op ~operand = { loc; value = UnaryOp { op; operand } }
let ifexp loc ~body ~test ~orelse = { loc; value = IfExp { body; test; orelse } }
let compare loc ~left ~ops_and_exprs = { loc; value = Compare { left; ops_and_exprs } }
let call loc ~func ~args ~keywords = { loc; value = Call { func; args; keywords } }
let attribute loc ~value ~attr = { loc; value = Attribute { value; attr } }
let subscript loc ~value ~slice = { loc; value = Subscript { value; slice } }

let functiondef loc ~name ~args ~body = { loc; value = FunctionDef { name; args; body } }
let classdef loc ~name ~args ~body = { loc; value = ClassDef { name; args; body } }
let _if_ loc ~test ~body ~orelse = { loc; value = If { test; body; orelse } }
let for_ loc ~target ~iter ~body ~orelse = { loc; value = For { target; iter; body; orelse } }
let while_ loc ~test ~body ~orelse = { loc; value = While { test; body; orelse } }
let raise_ loc ~exc ~cause = { loc; value = Raise { exc; cause } }
let try_ loc ~body ~handlers ~orelse ~finalbody = { loc; value = Try { body; handlers; orelse; finalbody } }
let with_ loc ~body ~context ~vars = { loc; value = With { body; context; vars } }
let assert_ loc ~test ~msg = { loc; value = Assert { test; msg } }
let _import loc i = { loc; value = Import i }
let _importfrom loc n is = { loc; value = ImportFrom (n, is) }
let expr loc ~value = { loc; value = Expr { value } }
let assign loc ~targets ~value = { loc; value = Assign { targets; value } }
let augassign loc ~target ~op ~value = { loc; value = AugAssign { target; op; value } }
let return loc ~value = { loc; value = Return { value } }
let delete loc ~targets = { loc; value = Delete { targets } }
let pass loc = { loc; value = Pass }
let break loc = { loc; value = Break }
let continue loc = { loc; value = Continue }
%}

%token <string> INTEGER
%token <string> FLOAT
%token <string> IDENTIFIER STRING
%token <bool> BOOL
%token NONE
%token COLON SEMICOLON
%token OPAND OPOR OPLSHIFT OPRSHIFT OPINVERT OPBXOR OPBAND OPBOR
%token OPADD OPSUB OPMUL OPDIV OPEDIV OPMOD OPPOWER
%token ADDEQ SUBEQ MULEQ DIVEQ EDIVEQ MODEQ
%token OPNEQ OPEQ OPLT OPLTEQ OPGT OPGTEQ OPNOT OPIS
%token DOT COMMA EQUAL
%token DEF RETURN DELETE ASSERT IF ELIF ELSE WHILE FOR IN BREAK CONTINUE PASS
%token LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK
%token LAMBDA CLASS RAISE FROM TRY EXCEPT WITH IMPORT AS FINALLY
%token INDENT DEDENT
%token NEWLINE
%token ENDMARKER

%type <Ast.t> mod_
%start mod_
%%

// スタート
mod_:
  | l=newline_or_stmt* ENDMARKER { List.concat l } // stmt list list を list に結合(concat)
;

newline_or_stmt:
  | NEWLINE { [] }
  | s=stmt { s }
;

stmt:
  | s=simple_stmt { s }
  | s=compound_stmt { [ s ] }
;

// スモール文\n | スモール文; simple_stmt_or_empty
simple_stmt:
  | s=small_stmt NEWLINE { [ s ] } // 文\n
  | s=small_stmt SEMICOLON l=simple_stmt_or_empty { s :: l } // 文; 文;*
;

// \n | スモール文\n | スモール文; rec
simple_stmt_or_empty: // shift/reduce回避のため改行付きかどうかで分けている？
  | NEWLINE { [] }
  | s=small_stmt NEWLINE { [ s ] }
  | s=small_stmt SEMICOLON l=simple_stmt_or_empty { s :: l }
;

small_stmt:
  | value=testlist { expr $loc ~value }
  | e1=testlist EQUAL e2=testlist l=assign_right {
    match List.rev (e1 :: e2 :: l) with
    | value :: targets -> assign $loc ~targets ~value
    | _ -> assert false
  }
  | target=testlist op=augassign value=testlist { augassign $loc ~target ~value ~op }
  | DELETE e=testlist { delete $loc ~targets:[ e ] }
  | PASS { pass $loc }
  | s=flow_stmt { s }
  | ASSERT test=test msg=assert_message { assert_ $loc ~test ~msg }
;

augassign:
  | ADDEQ { Add }
  | SUBEQ { Sub }
  | MULEQ { Mult }
  | DIVEQ { Div }
  | EDIVEQ { FloorDiv }
  | MODEQ { Mod }
;

assign_right:
  | { [] }
  | EQUAL l=separated_list(EQUAL, testlist) { l }
;

flow_stmt:
  | BREAK { break $loc }
  | CONTINUE { continue $loc }
  | RETURN { return $loc ~value:None }
  | RETURN v=testlist { return $loc ~value:(Some v) }
  | RAISE exc=test? { raise_ $loc ~exc ~cause:None }
  | RAISE exc=test? FROM cause=test { raise_ $loc ~exc ~cause:(Some cause) }
;

(* インデントでのひとかたまりを表すのはこの部分のようだ(仮) *)
suite:
  | s=simple_stmt { s }
  | NEWLINE INDENT l=stmt+ DEDENT { List.concat l }
;

// 複合文
compound_stmt:
  | IF test=test COLON body=suite elif=elif* orelse=orelse { combine_if $loc ~test ~body ~elif ~orelse }
  | WHILE test=test COLON body=suite orelse=orelse { while_ $loc ~test ~body ~orelse }
  | FOR target=exprlist IN iter=testlist COLON body=suite orelse=orelse { for_ $loc ~target ~iter ~body ~orelse }
  | TRY COLON body=suite finalbody=try_finally { try_ $loc ~body ~handlers:[] ~orelse:[] ~finalbody }
  | TRY COLON body=suite handlers=try_except+ orelse=try_orelse f=try_finally?
    { try_ $loc ~body ~handlers ~orelse ~finalbody:(Option.value f ~default:[]) }
  | WITH context=test COLON body=suite { with_ $loc ~context ~body ~vars:None }
  | WITH context=test AS vars=expr COLON body=suite { with_ $loc ~context ~body ~vars:(Some vars) }
  | DEF name=IDENTIFIER LPAREN args=parameters RPAREN COLON body=suite { functiondef $loc ~name ~args ~body }
  | CLASS name=IDENTIFIER args=class_parameters COLON body=suite { classdef $loc ~name ~args ~body }
;

try_except:
    | EXCEPT COLON body=suite { { type_ = None; name = None; body } }
    | EXCEPT e=expr COLON body=suite { { type_ = Some e; name = None; body } }
    | EXCEPT e=expr AS name=IDENTIFIER COLON body=suite { { type_ = Some e; name = Some name; body } }
;

try_orelse:
    | { [] }
    | ELSE COLON f=suite { f }
;

try_finally:
    | FINALLY COLON f=suite { f }
;

class_parameters:
    | { empty_args }
    | LPAREN args=parameters RPAREN { args }
;

// カンマ区切りパラメーター
parameters:
  | l=separated_list(COMMA, parameter) { merge_parameters l }
;

parameter:
  | id=IDENTIFIER { `arg id }
  | id=IDENTIFIER EQUAL e=expr { `kwonlyarg (id, e) }
  | OPMUL id=IDENTIFIER { `vararg id }
  | OPPOWER id=IDENTIFIER { `kwarg id }
;

elif:
  | ELIF e=test COLON s=suite { e, s }
;

assert_message:
  | { None }
  | COMMA e=test { Some(e) }
;

// test | test, testlist_or_empty
// A or A,A* のようなパターンは後続の A* の任意追加部分の生成規則を分けるとコンフリクトを回避できるようだ
testlist:
  | e=test { e }
  | e=test COMMA l=testlist_or_empty { tuple $loc (Array.of_list (e :: l)) }
;

testlist_or_empty:
  | { [] }
  | e=test { [e] }
  | e=test COMMA l=testlist_or_empty { e :: l }
;

exprlist:
  | e=expr { e }
  | e=expr COMMA l=exprlist_or_empty { tuple $loc (Array.of_list (e :: l)) }
;

exprlist_or_empty:
  | { [] }
  | e=expr { [e] }
  | e=expr COMMA l=exprlist_or_empty { e :: l }
;

// test は条件式の生成規則だが、一番したまで行くと単一の expr だけになるパターンがある
// こういう生成規則のほうがよいのかな…
test:
  | e=or_test { e } // このパターンで一切条件式が出ないまま最後まで行くと単一 expr だけが残る -> 式表現
  | body=or_test IF test=or_test ELSE orelse=test { ifexp $loc ~body ~test ~orelse }
  | LAMBDA args=parameters COLON body=test { lambda $loc ~args ~body }
;


// あとから定義されているものほど優先度が高い -> not, and, or の順に評価される
// A or B ..
or_test:
  | e=separated_nonempty_list(OPOR, and_test) {
    match e with
    | [e] -> e
    | values -> boolop $loc ~op:Or ~values
}
;
// A and B
and_test:
  | e=separated_nonempty_list(OPAND, not_test) {
    match e with
    | [e] -> e
    | values -> boolop $loc ~op:And ~values
}
;
// not A
not_test:
  | OPNOT operand=not_test { unaryop $loc ~op:Not ~operand }
  | e=comparison { e }
;

// 条件式
comparison:
  | e=expr { e } // 式
  | l=expr o=comp_op c=comparison {
    let ops_and_exprs =
      match c with
      | { loc = _; value = Compare { left; ops_and_exprs } } -> (o, left) :: ops_and_exprs
      | e -> [ o, e ]
    in
    compare $loc ~left:l ~ops_and_exprs
  }
;

comp_op:
  | OPEQ { Eq }
  | OPNEQ { NotEq }
  | OPLT { Lt }
  | OPLTEQ { LtE }
  | OPGT { Gt }
  | OPGTEQ { GtE }
  | IN { In }
  | OPNOT IN  { NotIn }
  | OPIS { Is }
  | OPIS OPNOT { IsNot }
;

expr:
  | e=xor_expr { e }
  | left=xor_expr OPBOR right=expr { binop $loc ~left ~op:BitOr ~right }
;

xor_expr:
  | e=and_expr { e }
  | left=and_expr OPBXOR right=xor_expr { binop $loc ~left ~op:BitXor ~right }
;

and_expr:
  | e=shift_expr { e }
  | left=shift_expr OPBAND right=and_expr { binop $loc ~left ~op:BitAnd ~right }
;

shift_expr:
  | e=arith_expr { e }
  | left=arith_expr op=opshift right=shift_expr { binop $loc ~left ~op ~right }
;

opshift:
  | OPLSHIFT { LShift }
  | OPRSHIFT { RShift }
;

arith_expr:
  | e=term { e }
  | left=arith_expr op=oparith right=term { binop $loc ~left ~op ~right }
;

oparith:
  | OPADD { Add }
  | OPSUB { Sub }
;

term:
  | e=factor { e }
  | left=term op=opfactor right=factor { binop $loc ~left ~op ~right }
;

opfactor:
  | OPMUL { Mult }
  | OPDIV { Div }
  | OPEDIV { FloorDiv }
  | OPMOD { Mod }
;

factor:
  | OPADD operand=factor { unaryop $loc ~op:UAdd ~operand }
  | OPSUB operand=factor { unaryop $loc ~op:USub ~operand }
  | OPINVERT operand=factor { unaryop $loc ~op:Invert ~operand }
  | e=power { e }
;

power:
  | e=atom_expr { e }
  | left=atom_expr OPPOWER right=factor { binop $loc ~left ~op:Pow ~right }
;

atom_expr:
  | e=atom { e }
  | func=atom_expr LPAREN args=separated_list(COMMA, argument) RPAREN {
    let args, keywords = merge_args args in
    call $loc ~func ~args ~keywords }
  | value=atom_expr DOT attr=IDENTIFIER { attribute $loc ~value ~attr }
  | value=atom_expr LBRACK slice=testlist RBRACK { subscript $loc ~value ~slice }
;

// リテラル式
atom:
  | LPAREN e=testlist RPAREN { e } // タプル
  | LBRACK l=separated_list(COMMA, expr) RBRACK { list $loc (Array.of_list l) } // リスト
  | LBRACK elt=expr FOR target=exprlist IN iter=or_test ifs=ifs f=fors RBRACK
    { listcomp $loc ~elt ~generators:({ target; iter; ifs } :: f) } // リスト内包表記
  | LBRACE key_values=separated_list(COMMA, key_value) RBRACE { dict $loc ~key_values } // 辞書
  | IDENTIFIER { name $loc $1 }               // 変数
  | STRING { str $loc $1 }                    // 文字列
  | INTEGER { num $loc (Z.of_string $1) }     // int
  | FLOAT { float $loc (float_of_string $1) } // float
  | BOOL { bool $loc $1 }                     // bool
  | NONE { none $loc}                         // None
;

argument:
  | e=test { `Arg e }
  | id=IDENTIFIER EQUAL e=test { `Keyword (id, e) }
;

key_value:
  | key=test COLON value=test { key, value }
;

fors:
  | { [] }
  | FOR target=exprlist IN iter=or_test ifs=ifs f=fors { { target; iter; ifs } :: f }
;

ifs:
  | { [] }
  | IF e=or_test l=ifs { e :: l }
;

orelse:
  | { [] }
  | ELSE COLON b=suite { b }
;
