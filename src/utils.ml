
module IntMap = Map.Make (struct type t = int let compare = compare end)
module StrMap = Map.Make (struct type t = string let compare = compare end)
module StrSet = Set.Make (struct type t = string let compare = compare end)
module IntSet = Set.Make (struct type t = int let compare = compare end)

let removeDupes l =
  List.rev
    (List.fold_left (fun acc x -> if List.mem x acc then acc else x::acc) [] l)

let flattenSomeLists : ('a list option) list -> 'a list option =
fun los ->
  List.fold_left (fun acc lo ->
    match acc, lo with
      | Some l1, Some l2 -> Some (l1 @ l2)
      | _ -> None
  ) (Some []) los

let strPrefix s pre =
  let n = String.length s in
  let m = String.length pre in
    (n >= m) && (String.sub s 0 m = pre)

let rec clip s =
  if s = "" then s
  else let (c,s') = (s.[0], String.sub s 1 (String.length s - 1)) in
       if c = ' '
         then clip s'
         else String.make 1 c ^ s'

let redString s = Printf.sprintf "\027[31m%s\027[0m" s
let greenString s = Printf.sprintf "\027[32m%s\027[0m" s
let yellowString s = Printf.sprintf "\027[33m%s\027[0m" s
