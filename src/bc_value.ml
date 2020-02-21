open Base

module Type_ = struct
  type t =
    | None_t
    | Bool
    | Int
    | Float
    | Tuple
    | Dict
    | List
    | Str
    | Builtin_fn
    | Function
    | Object
    | Class
  [@@deriving sexp]

  let to_string t = sexp_of_t t |> Sexp.to_string_mach
end

type t =
  | None
  | Bool of bool
  | Int of Z.t
  | Float of float
  | Tuple of t array
  | List of t array
  | Dict of (t, t) Hashtbl.Poly.t
  | Str of string
  | Builtin_fn of
      { name : string
      ; fn : t list -> t
      }

let type_ = function
  | None -> Type_.None_t
  | Bool _ -> Bool
  | Int _ -> Int
  | Float _ -> Float
  | Tuple _ -> Tuple
  | List _ -> List
  | Dict _ -> Dict
  | Str _ -> Str
  | Builtin_fn _ -> Builtin_fn

let to_string ?(escape_special_chars = true) t =
  let rec loop ~e = function
    | None -> "None"
    | Bool true -> "True"
    | Bool false -> "False"
    | Int i -> Z.to_string i
    | Float f -> Float.to_string f
    | Tuple [| t |] -> "(" ^ loop ~e:true t ^ ",)"
    | Tuple ts ->
      Array.to_list ts
      |> List.map ~f:(loop ~e:true)
      |> String.concat ~sep:", "
      |> fun s -> "(" ^ s ^ ")"
    | List ts ->
      Array.to_list ts
      |> List.map ~f:(loop ~e:true)
      |> String.concat ~sep:", "
      |> fun s -> "[" ^ s ^ "]"
    | Dict dict ->
      Hashtbl.to_alist dict
      |> List.map ~f:(fun (key, value) -> loop ~e:true key ^ ": " ^ loop ~e:true value)
      |> String.concat ~sep:","
      |> fun s -> "{" ^ s ^ "}"
    | Str s -> if e then "\'" ^ String.escaped s ^ "\'" else s
    | Builtin_fn { name; fn = _ } -> Printf.sprintf "builtin<%s>" name
  in
  loop t ~e:escape_special_chars

type code = t Bc_code.t
