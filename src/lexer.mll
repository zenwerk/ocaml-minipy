{
open! Lexing
open! Parser
module String = Base.String
module Stack = Base.Stack
module Queue = Base.Queue
exception SyntaxError of string

(* lexbuf をマニュアルで更新する *)
let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with  (* lexer の現在位置を元にして *)
    pos_bol = lexbuf.lex_curr_pos; (* 行頭オフセットはlexerの現在のカーソル位置とする *)
    pos_lnum = pos.pos_lnum + 1 }  (* 行番号をインクリメント *)

(* Lexerの実行情報; parse.ml でも使われる *)
module Env = struct
  (* Envが保持する情報 *)
  type t =
    { indents: int Stack.t (* インデント増加時の累積スペースの数をスタックで保持する,スペース2個ルールなら 2,4,6,8... *)
    ; mutable nestings : int
    ; mutable tokens : Parser.token Queue.t
    ; mutable last_token : Parser.token option
    }

  let create () =
    { indents = Stack.create ()
    ; nestings = 0
    ; tokens = Queue.create ()
    ; last_token = None
    }

  (* nestレベルをインクリメント *)
  let enter t =
    t.nestings <- t.nestings + 1

  (* nestレベルをデクリメント *)
  let exit t =
    t.nestings <- t.nestings - 1;
    if t.nestings < 0
    then raise (SyntaxError "too many closing delimiters")

  (* 最後のインデントレベル *)
  let last_indent t =
    Option.value (Stack.top t.indents) ~default:0

  let push_indent t indent =
    Stack.push t.indents indent

  let drop_indent t ~until =
    let rec loop acc =
      match Stack.top t.indents with (* 先頭のインデント数のスペース数を取り出す *)
      | None -> if until = 0 then Some acc else None  (* スタックが空かつインデントレベル0 のとき *)
      | Some level when level = until -> Some acc     (* 指定したインデントレベル(until)に到達 *)
      | Some level when level < until -> None         (* インデント数が揃っていない *)
      | Some _level (* when level > until *) ->       (* POPしてインデントレベルを下げる *)
          ignore (Stack.pop_exn t.indents : int);
          loop (acc + 1) (* DEDENT数をインクリメント *)
    in
    loop 0

  let token t =
    Queue.dequeue t.tokens

  let add_tokens t tokens = Queue.enqueue_all t.tokens tokens
end

let string_loop lexbuf ~f =
  let buf = Buffer.create 1024 in (* 1024byteのバッファを生成 *)
  let ok = ref true in
  (* eos になるまで Buffer に lexbuf から取り出したバイトを追加する *)
  while !ok do
    match f lexbuf with
    | `char c -> Buffer.add_char buf c
    | `eos -> ok := false
  done;
  [ STRING (Buffer.contents buf) ]
}

rule read env = parse
  | ' ' { read env lexbuf } (* インデントではなく (assert foo) とか print(a, b, c) のようなスペースは無視する *)
  | "\\\n" { read env lexbuf }
  | "def" { [DEF] }
  | "if" { [IF] }
  | "elif" { [ELIF] }
  | "else" { [ELSE] }
  | "return" { [RETURN] }
  | "del" { [DELETE] }
  | "while" { [WHILE] }
  | "True" { [BOOL true] }
  | "False" { [BOOL false] }
  | "None" { [NONE] }
  | "and" { [OPAND] }
  | "or" { [OPOR] }
  | "break" { [BREAK] }
  | "continue" { [CONTINUE] }
  | "pass" { [PASS] }
  | "for" { [FOR] }
  | "in" { [IN] }
  | "lambda" { [LAMBDA] }
  | "assert" { [ASSERT] }
  | "class" { [CLASS] }
  | "raise" { [RAISE] }
  | "from" { [FROM] }
  | "try" { [TRY] }
  | "except" { [EXCEPT] }
  | "finally" { [FINALLY] }
  | "with" { [WITH] }
  | "as" { [AS] }
  | "import" { [IMPORT] }
  | "not" { [OPNOT] }
  | "is" { [OPIS] }
  | "r\"" { string_loop lexbuf ~f:string_raw2 }
  | "r'" { string_loop lexbuf ~f:string_raw1 }
  | "\"" { string_loop lexbuf ~f:string_escaped2 }
  | "'" { string_loop lexbuf ~f:string_escaped1 }
  | "r\"\"\"" { string_loop lexbuf ~f:string_triple_raw2 }
  | "r'''" { string_loop lexbuf ~f:string_triple_raw1 }
  | "\"\"\"" { string_loop lexbuf ~f:string_triple_escaped2 }
  | "'''" { string_loop lexbuf ~f:string_triple_escaped1 }
  | ['0'-'9']+ as int { [INTEGER int] }
  | '0' ['x' 'X'] ['0'-'9' 'a'-'f' 'A'-'F']+ as int { [INTEGER int] }
  | '0' ['b' 'B'] ['0'-'1']+ as int { [INTEGER int] }
  | '0' ['o' 'O'] ['0'-'7']+ as int { [INTEGER int] }
  | ['0'-'9']+ '.' ['0'-'9']* as float { [FLOAT float] }
  | ['0'-'9']* '.' ['0'-'9']+ as float { [FLOAT float] }
  | ['0'-'9']+ '.' ['0'-'9']* ['e' 'E'] ['+' '-']? ['0'-'9']+ as float { [FLOAT float] }
  | ['0'-'9']* '.' ['0'-'9']+ ['e' 'E'] ['+' '-']? ['0'-'9']+ as float { [FLOAT float] }
  | '(' { Env.enter env; [LPAREN] }
  | '{' { Env.enter env; [LBRACE] }
  | '[' { Env.enter env; [LBRACK] }
  | ')' { Env.exit env; [RPAREN] }
  | '}' { Env.exit env; [RBRACE] }
  | ']' { Env.exit env; [RBRACK] }
  | '.' { [DOT] }
  | ',' { [COMMA] }
  | "**" { [OPPOWER] }
  | '+' { [OPADD] }
  | '-' { [OPSUB] }
  | '*' { [OPMUL] }
  | '/' { [OPDIV] }
  | "//" { [OPEDIV] }
  | '%' { [OPMOD] }
  | ':' { [COLON] }
  | ';' { [SEMICOLON] }
  | "<<" { [OPLSHIFT] }
  | ">>" { [OPRSHIFT] }
  | "==" { [OPEQ] }
  | "!=" { [OPNEQ] }
  | '<' { [OPLT] }
  | "<=" { [OPLTEQ] }
  | '>' { [OPGT] }
  | ">=" { [OPGTEQ] }
  | '=' { [EQUAL] }
  | "+=" { [ADDEQ] }
  | "-=" { [SUBEQ] }
  | "*=" { [MULEQ] }
  | "/=" { [DIVEQ] }
  | "//=" { [EDIVEQ] }
  | "%=" { [MODEQ] }
  | '~' { [OPINVERT] }
  | '^' { [OPBXOR] }
  | '&' { [OPBAND] }
  | '|' { [OPBOR] }
  (* TODO: handle tabs *)
  (* This discards lines with only spaces in them.
      (# コメント)? 改行 (スペースor改行)* を str として取得
      コメントは任意, 改行は必須, その後任意の(スペースor改行)
        1. 改行無視 -> 最初の for の処理
        2. 行頭のスペースをカウントしてインデントの判定 -> その後の if の処理
   *)
  | ('#' [^'\n']*)? '\n' [' ' '\n']* as str {
    (* 改行の分だけ lex_curr_p の行をすすめる *)
    for _i = 1 to String.count str ~f:(Base.Char.(=) '\n') do
      next_line lexbuf
    done;
    (* 最後の改行から何個スペースがあるか = インデント数
       " \n \n   " のとき indent は 3
     *)
    let indent = String.length str - String.rindex_exn str '\n' - 1 in
    (* nesting != 0 のときカッコの中にいるのでインデントは無視される *)
    if env.nestings <> 0 then read env lexbuf
    (* インデントの処理 *)
    else
      let last_indent = Env.last_indent env in
      if last_indent = indent then [NEWLINE]
      (* 最後のインデントより少ないスペース数 = インデントが下がっている *)
      else if last_indent > indent then (
        (* インデントが下がった分だけ DEDENT を返す *)
        let dropped =
          match Env.drop_indent env ~until:indent with
          | None -> raise (SyntaxError (Printf.sprintf "Unexpected indentation level %d" indent))
          | Some dropped -> dropped
        in
        (* [改行; 下げた分のDEDENT] を返す *)
        NEWLINE :: List.init dropped (fun _ -> DEDENT)
      ) else (
        (* インデントを増やす *)
        Env.push_indent env indent; (* インデント(正確にはインデントしたスペースの数)を積む *)
        [NEWLINE; INDENT]
      )
  }
  | ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']* as id { [IDENTIFIER id] }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof {
    match Env.drop_indent env ~until:0 with
    | None -> [ENDMARKER]
    | Some dropped -> List.init dropped (fun _ -> DEDENT) @ [ENDMARKER]
  }
(* 各種文字列定義のパース *)
and string_escaped1 = parse
 | "\\\"" { `char '\"' }
 | "\\\'" { `char  '\'' }
 | "\\\\" { `char '\\' }
 | "\\n" { `char '\n' }
 | "\\t" { `char '\t' }
 | '\'' { `eos }
 | _ as c { `char c }
and string_raw1 = parse     (* r'foo' *)
 | '\'' { `eos }
 | _ as c { `char c }
and string_escaped2 = parse
 | "\\\"" { `char '\"' }
 | "\\\'" { `char  '\'' }
 | "\\\\" { `char '\\' }
 | "\\n" { `char '\n' }
 | "\\t" { `char '\t' }
 | '\"' { `eos }
 | _ as c { `char c }
and string_raw2 = parse (* r"foo" *)
 | '\"' { `eos }
 | _ as c { `char c }
and string_triple_escaped1 = parse
 | "\\\"" { `char '\"' }
 | "\\\'" { `char  '\'' }
 | "\\\\" { `char '\\' }
 | "\\n" { `char '\n' }
 | "\\t" { `char '\t' }
 | "'''" { `eos }
 | _ as c { `char c }
and string_triple_raw1 = parse
 | "'''" { `eos }
 | _ as c { `char c }
and string_triple_escaped2 = parse
 | "\\\"" { `char '\"' }
 | "\\\'" { `char  '\'' }
 | "\\\\" { `char '\\' }
 | "\\n" { `char '\n' }
 | "\\t" { `char '\t' }
 | "\"\"\"" { `eos }
 | _ as c { `char c }
and string_triple_raw2 = parse
 | "\"\"\"" { `eos }
 | _ as c { `char c }

{
  let read env lexbuf =
    match Env.token env with
    | Some token ->
        env.last_token <- Some token;
        token
    | None ->
        match read env lexbuf with
        | [] -> assert false
        | token :: tokens ->
          env.last_token <- Some token;
          Env.add_tokens env tokens;
          token
}
