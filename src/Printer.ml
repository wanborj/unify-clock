(*
Copyright (c) 2013 Yucheng Zhang

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)


open Printf
open Results
open List

(* A printer for the example programs. The annotated type and clock at each
 * expression node is omitted for clarity. *)

let str_kind = function
  | Kin -> "Kin"
  | Kout -> "Kout"
  | Kloc -> "Kloc"

let str_type = function
  | Tbool -> "Tbool"
  | Tz -> "Tz"

let str_clock = function
  | None -> "glb"
  | Some x -> sprintf "smp(x%d)" (int_of_pos x)

let str_const = function
  | (Vbool true) -> sprintf "true"
  | (Vbool false) -> sprintf "false"
  | (Vz z) -> sprintf "%d" (int_of_z z)

let str_op = function
  | Oplus    -> "+"
  | Oopp     -> "-"
  | Ominus   -> "-"
  | Omul     -> "*"
  | Odiv     -> "/"
  | Omod     -> "mod"
  | Ole      -> "<="
  | Olt      -> "<"
  | Oge      -> ">="
  | Ogt      -> ">"
  | Oeq      -> "=="
  | One      -> "<>"
  | Onot     -> "not"
  | Oand     -> "and"
  | Oor      -> "or"
  | Oif      -> "if"

let rec str_expr = function
  | Evar (x, _, _) -> sprintf "x%d" (int_of_pos x)
  | Econst (v, _, _) -> str_const v
  | Ewhen (e, x, _, _) -> sprintf "when (%s) x%d" (str_expr e) (int_of_pos x)
  | Ecurr (e, x, v, _, _) -> sprintf "curr (%s) x%d %s" (str_expr e) (int_of_pos x) (str_const v)
  | Efby (e1, e2, _, _) -> sprintf "fby (%s) (%s)" (str_expr e1) (str_expr e2)
  | Edata1 (Onot, e1, _, _) -> sprintf "not (%s)" (str_expr e1)
  | Edata2 (Oplus, e1, e2, _, _) -> sprintf "(%s) + (%s)" (str_expr e1) (str_expr e2)
  | Edata2 (Oand, e1, e2, _, _) -> sprintf "(%s) and (%s)" (str_expr e1) (str_expr e2)
  | Edata2 (Oor, e1, e2, _, _) -> sprintf "(%s) or (%s)" (str_expr e1) (str_expr e2)
  | Edata3 (Oif, e1, e2, e3, _, _) -> sprintf "if (%s) then (%s) else (%s)" (str_expr e1) (str_expr e2) (str_expr e3)
  | Edata1 (o, e1, _, _) -> sprintf "data1 (%s) (%s)" (str_op o) (str_expr e1)
  | Edata2 (o, e1, e2, _, _) -> sprintf "data2 (%s) (%s) (%s)" (str_op o) (str_expr e1) (str_expr e2)
  | Edata3 (o, e1, e2, e3, _, _) -> sprintf "data3 (%s) (%s) (%s) (%s)" (str_op o) (str_expr e1) (str_expr e2) (str_expr e3)

let sort_env e =
  sort (fun (x1, _) (x2, _) -> int_of_pos x1 - int_of_pos x2) e

let print_env to_string env =
  let env' = sort_env env in
  iter ( fun (x, y) ->
         printf "x%d\t\t=== %s\n" (int_of_pos x) (to_string y) ) env';
  printf "\n\n"

let print_decl env_k env_t env_c =
  let env_k' = sort_env env_k in
  let env_t' = sort_env env_t in
  let env_c' = sort_env env_c in
  let env_all = combine env_k' (combine env_t' env_c') in
  iter ( fun ((x1, y1), ((x2, y2), (x3, y3))) ->
         assert ( int_of_pos x1 == int_of_pos x2 &&
                  int_of_pos x2 == int_of_pos x3 );
         printf "x%d\t\t:: %s, \t%s, \t%s\n" (int_of_pos x1) (str_kind y1) (str_type y2) (str_clock y3)
       ) env_all;
  printf "\n\n"

let print_prog p =
  print_decl
    (PositiveMap.elements (kK p))
    (PositiveMap.elements (tT p))
    (PositiveMap.elements (cC p));
  print_env str_expr (PositiveMap.elements (eE p))

let print_result i (p,q') =
  printf "\n\n####### Example %d #######\n" i;
  printf "Source Program:\n";
  print_prog p;
  match q' with
    | None -> printf "Ill-formed Source Program\n"
    | Some q -> printf "Result Program:\n"; print_prog q

;;

iteri print_result allExampleResults
