open Compile
open Runner
open Printf
open OUnit2
open ExtLib
open Types
open Expr
open Pretty

let t name program expected = name>::test_run [] program name expected;;
let te name program expected_err = name>::test_err [] program name expected_err;;
let tgc name heap_size program expected = name>::test_run [string_of_int heap_size] program name expected;;
let tvg name program expected = name>::test_run_valgrind [] program name expected;;
let tvgc name heap_size program expected = name>::test_run_valgrind [string_of_int heap_size] program name expected;;
let terr name program expected = name>::test_err [] program name expected;;
let tgcerr name heap_size program expected = name>::test_err [string_of_int heap_size] program name expected;;

let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let vars = free_vars anfed in
    let c = Pervasives.compare in
    let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
    assert_equal (List.sort ~cmp:c vars) (List.sort ~cmp:c expected) ~printer:str_list_print)
;;

let pair_tests = [
  t "tup1" "let t = (4, (5, 6)) in
            begin
              t[0] := 7;
              t
            end" "(7, (5, 6))";
  t "tup2" "let t = (4, (5, 6)) in
            begin
              t[1] := 7;
              t
            end" "(4, 7)";
  t "tup3" "let t = (4, (5, 6)) in
            begin
              t[1] := t;
              t
            end" "(4, <cyclic tuple 1>)";
  t "tup4" "let t = (4, 6) in
            (t, t)"
           "((4, 6), (4, 6))"

]

let oom = [
  tgcerr "oomgc1" 7 "(1, (3, 4))" "Out of memory";
  tgc "oomgc2" 8 "(1, (3, 4))" "(1, (3, 4))";
  tvgc "oomgc3" 8 "(1, (3, 4))" "(1, (3, 4))";
  tgc "oomgc4" 4 "(3, 4)" "(3, 4)";
  tgcerr "oomgc5" 3 "(3, 4)" "Allocation";
]

let gc = [
  tgc "gc1" 10
      "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
      "(1, 2)";
]

let tests = [
  t "forty" "let x = 40 in x" "40";
  t "fals" "let x = false in x" "false";
  t "tru" "let x = true in x" "true";
  t "true1" "if true : 5 else: 10" "5";
  t "false1" "if false : 5 else: 10" "10";
  t "print1" "print(5 - 10)" "-5\n-5";
  t "comp_1" "if (5 > 7): true else: false" "false";
  t "comp_2" "if (5 < 7): true else: false" "true";
  t "comp_3" "if (5 == 7): true else: false" "false";
  t "comp_4" "if (5 == 5): true else: false" "true";
  t "let_1" "let x = 5 in let y = 4 in let z = 3 in x + y + z" "12";

  t "m1" "5 - 5" "0";
  t "m2" "5 + 5" "10";
  t "m3" "5 * 5" "25";
  t "m4" "5 - 0" "5";
  t "m5" "5 + 0" "5";
  t "m6" "5 * 0" "0";
  t "m7" "let x = 5 in x" "5";
  t "m8" "let x = 5, y = 6 in x + y" "11";
  t "m9" "let x = 5 + 6 in x" "11";
  t "m10" "let x = let y = 5 + 6 in y in x - 6" "5";
  t "m11" "let x = 5 in let y = 5 + x in y" "10";
  t "m12" "let x = 5, y = 6 in let z = x + y in z" "11";
  t "m13" "let x = 5, y = 6 in let z = let a = x + y in a in z" "11";
  t "m14" "let x = 5 in 5 * x" "25";
  t "m15" "let x = 5, y = 6 in x * y" "30";
  t "m16" "let x = 5, y = 6 in let z = let a = x * y in a in z" "30";

  t "f1" "let sq = (lambda x: x * x), ten = (lambda: 10) in sq(ten())" "100";
  t "f2" "let sub = (lambda x, y: x - y) in sub(8, 6)" "2";
  t "f3" "let f = (lambda x,y,z: x*y+z),
          g = (lambda x,y: x+y),
          h = (lambda x,y: 2*x+y) in
          f(g(3,4),g(2,2),h(5,9))" "47";
  t "f4" "let f = (lambda x,y,z,t: x*y+z*t),
          g = (lambda x,y: x+y),
          h = (lambda x,y: 2*x+y),
          j = (lambda x: x*x) in
          j(f(g(4,4),h(2,2),g(5,5),h(3,3)))" "272484";
  t "f5" "let f = (lambda x: if x==1: x else: 0) in f(4)" "0";
  t "f6" "let f = (lambda x: if x==1: x else: 1) in f(1)" "1";
  t "f7" "let rec f = (lambda x: if x==0: 0 else: (x + f(x - 1))) in f(24)" "300";
  t "f8" "let rec f = (lambda x: if x==0: 1 else: (x * f(x - 1))) in f(6)" "720";
  t "f9" "let rec f = (lambda x: if x==0: 1 else: (x * f(x - 1))) in f(10)" "3628800";
  t "f10" "let f = (lambda: 5) in f()" "5";
  t "f11" "let f = (lambda x: x + 1) in let y = (lambda x: x(5)) in y(f)" "6";

  t "rec1" "let rec f = (lambda x: if x==0: 1 else: (x * f(x - 1))),
                    g = (lambda x: x + x) in f(g(3))" "720";
  t "rec2" "let rec f = (lambda x,y,z: x*y+z),
          g = (lambda x,y: x+y),
          h = (lambda x,y: 2*x+y) in
          f(g(3,4),g(2,2),h(5,9))" "47";
  t "rec3" "let rec f = (lambda x,y,z,t: x*y+z*t),
          g = (lambda x,y: x+y),
          h = (lambda x,y: 2*x+y),
          j = (lambda x: x*x) in
          j(f(g(4,4),h(2,2),g(5,5),h(3,3)))" "272484";
  t "rec4" "let rec f = (lambda x, a: if x==1: a else: g(x - 1, a * x)),
            g = (lambda x, a: if x==1: a+1 else: f(x - 1, a + x)) in f(16, 1)" "20643839";

  t "free_1" "let x = 10 in let f = (lambda y: x + y) in f(10)" "20";
  t "free_2" "let x = 10 in let f = (lambda y, z: x + y + z) in f(10, 5)" "25";
  t "free_3" "let x = 10, y = 5 in let f = (lambda z, t: (x * z) + (y * t)) in f(10, 5)" "125";

  t "ll_1" "let rec length = (lambda l: length_rec(l, 0)),
            length_rec = (lambda l, acc: if l == false: acc else: length_rec(l[1], acc + 1)) in
            length((0, (1, (2, (3, (4, (5, (6, (7, (8, (9, false)))))))))))"
            "10";
  t "ll_2" "let rec sum = (lambda l: sum_rec(l, 0)),
            sum_rec = (lambda l, acc: if l == false: acc else: sum_rec(l[1], acc + l[0])) in
            sum((0, (1, (2, (3, (4, (5, (6, (7, (8, (9, false)))))))))))"
            "45";
  t "ll_3" "let rec reverse = (lambda l: reverse_rec(l, false)),
            reverse_rec = (lambda l, prev: if l[1] == false: (l[0], prev) else: reverse_rec(l[1], (l[0], prev))) in
            reverse((0, (1, (2, (3, (4, (5, (6, (7, (8, (9, false)))))))))))"
            "(9, (8, (7, (6, (5, (4, (3, (2, (1, (0, false))))))))))";

  te "e_lam_1" "let x = 10 in let f = (lambda y: x + y) in x(10)" "10";
  te "e_lam_2" "let x = 10 in let f = (lambda y: x + y) in f(10, 10)" "11";
  t "tup_1" "let x = (3, 4, 5, 6) in x[0]" "3";
  t "tup_2" "let x = (3, 4, 5, 6) in x[1]" "4";
  t "tup_3" "let x = (3, 4, 5, 6) in x[2]" "5";
  t "tup_4" "let x = (3, 4, 5, 6) in x[3]" "6";
  t "tup_5" "let x = (1, 2, 3, 4, 5, 6) in x[0]" "1";
  t "tup_6" "let x = (1, 2, 3, 4, 5, 6) in x[2]" "3";
  t "tup_7" "let x = (1, 2, 3, 4, 5, 6) in x[4]" "5";
  t "tup_8" "let x = (1, 2, 3, 4, 5, 6) in x[2+2]" "5";
  t "tup_9" "let x = (1, 2, 3, 4, 5, 6) in x[0+1]+x[1+2]+x[2+3]" "12";
  t "tup_10" "let x = (1, 2, 3, 4, 5, 6) in x[x[x[x[x[x[0]]]]]]" "6";
  t "tup_11" "let x = (0, false, 1, true) in x" "(0, false, 1, true)";
  t "tup_12" "let x = ((0, false), (1, true), (2, (true, false))) in x"
             "((0, false), (1, true), (2, (true, false)))";
  t "tup_13" "let x = (0, (1, 2)) in x[1]" "(1, 2)";
  t "tup_14" "let x = (0, (1, 2)) in x[1][0]" "1";
  t "tup_15" "let x = (0, (1, (3, 4))) in x[1][1][1]" "4";
  t "tup_16" "let x = (0, (1, (3, 4))) in x[1][1][1] + x[1][1][0]" "7";
  t "tup_17" "let x = (3, 4, 5, 6) in begin x[0] := 9; x end" "(9, 4, 5, 6)";
  t "tup_18" "let x = (3, 4, 5, 6) in begin x[2] := 9; x end" "(3, 4, 9, 6)";
  t "tup_19" "let x = ((0, false), (1, true), (2, (true, false))) in
              begin x[0][1] := true; x end"
             "((0, true), (1, true), (2, (true, false)))";
  t "tup_20" "let x = ((0, false), (1, true), (2, (true, false))) in
              begin x[0][1] := true; x[2][1][0] := false; x[1] := 5; x end"
             "((0, true), 5, (2, (false, false)))";
  t "tup_21" "let x = (1, 2, 3, 4, 5, 6) in begin x[x[x[x[x[x[0]]]]]] := 9; x end" "(1, 2, 3, 4, 5, 9)";

  t "eq_1" "let x = (1, 2, 3) in (x == x)" "true";
  t "eq_2" "let x = (1, 2, 3), y = (1, 2, 3) in (x == y)" "true";
  t "eq_3" "let x = (1, 2, 3), y = (1, 2, 4) in (x == y)" "false";
  t "eq_4" "let x = (1, 2, 3), y = (1, 2, 3, 4) in (x == y)" "false";
  t "eq_5" "let x = ((1, 2), (3, 4), 5), y = ((1, 2), (3, 4), 5) in (x == y)" "true";
  t "eq_6" "let x = ((1, 2), (3, 4), 5), y = ((1, 2), (3, 5), 5) in (x == y)" "false";
  t "eq_7" "let x = (1, (2, (3, (4, false)))), y = (1, (2, (3, (4, false)))) in (x == y)" "true";
  t "eq_8" "let x = (1, (2, (3, (4, false)))), y = (1, (2, (3, (5, false)))) in (x == y)" "false";

  te "comp_num_1" "if (5 < true): 5 else: 10" "1";
  te "comp_num_2" "if (5 > true): 5 else: 10" "1";
  te "arith_num_1" "5 + true" "2";
  te "arith_num_2" "5 - true" "2";
  te "arith_num_3" "5 * true" "2";
  te "logic_bool_1" "!(5)" "3";
  te "logic_bool_2" "5 && 5" "3";
  te "logic_bool_3" "5 || 5" "3";
  te "if_num" "if 5 : 5 else: 10" "4";
  te "ovf_1" "999999999 * 999999999" "5";
  te "ovf_2" "let rec f = (lambda x: if x==0: 1 else: (x * f(x - 1))) in f(100)" "5";
  te "e_tup_1" "let x = 5 in x[1]" "6";
  te "e_tup_2" "let x = (1, 2) in x[false]" "7";
  te "e_tup_3" "let x = (1, 2) in x[2]" "8";
  te "e_tup_4" "let x = (1, 2) in x[-1]" "9";
  te "e_tup_5" "let x = 5 in x[1] := 0" "6";
  te "e_tup_6" "let x = (1, 2) in x[false] := 0" "7";
  te "e_tup_7" "let x = (1, 2) in x[2] := 0" "8";
  te "e_tup_8" "let x = (1, 2) in x[-1] := 0" "9";

  te "e_scope_1" "let x = 5 in x + y" "The identifier y, used at <e_scope_1, 1:17-1:18>, is not in scope";

  te "e_shadow_1" "let x = 5 in let x = 5 in 4" "The identifier x, defined at <e_shadow_1, 1:17-1:18>, shadows one defined at <e_shadow_1, 1:4-1:5>";

  te "e_num_1" "let x = 1073741824 in x" "The number literal 1073741824, used at <e_num_1, 1:8-1:18>, is not supported in this language";
  te "e_num_2" "let x = -1073741825 in x" "The number literal -1073741825, used at <e_num_2, 1:8-1:19>, is not supported in this language";

]

let suite =
"suite">:::tests
 (*pair_tests @ oom @ gc*)



let () =
  run_test_tt_main suite
;;

