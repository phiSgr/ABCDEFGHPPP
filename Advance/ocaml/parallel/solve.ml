open Core.Std

module type QUESTION =
  sig
    val width : int val base : int
  end

module type SOLVED =
  sig
    val solve : unit -> int
  end

module Solver(Q: QUESTION): SOLVED = struct
 
(*
   ABCD
  -EFGH
  =====
   IJKL
  +MNOP
  =====
  11111
*)

  open Q (* so that base and width go into scope *)
  let biggest_digit = base - 1

  open Functory.Cores

  (* let () = Functory.Control.set_debug true *)

  let worker_num = 4
  let () = set_number_of_cores worker_num

  (* open Functory.Sequential *)
  (* Uncomment the above line to use sequential mode *)

  (* This is not exactly cps because of the non-tail calls,
     but I like the name :P *)
  (* Insert x into the list at every possible positions and callback f. *)
  let rec insert_into_cps x ~f = function
    | [] -> f [x]
    | hd::tl -> (
        f (x::hd::tl);
        insert_into_cps x tl ~f:(fun inserted ->
          hd :: inserted |> f
        )
      )

  (* Select r elements from l, callback f for effects *)
  let rec perm_cps r l ~f =
    if r = 0 then f [] else match l with
      | [] -> ()
      | hd :: tl ->
        perm_cps r tl ~f;
        perm_cps (r-1) tl ~f:(insert_into_cps hd ~f)

  (* Due to symmetry, only smaller half of the digits will be selected first,
     need flipping 8 to 9, for example.
     E.g. width 4 and base 17, suppose 8762 is selected,
     there are 15 more IJKL to test, from 876G, 87B2 to 9ABG *)
  let generate_flipped = function
    | [] -> assert false
    | l::kji ->
    	let rec flip = function
    	  | [] -> [[]]
    	  | k::ji -> List.concat_map ~f:(fun jm -> [k::jm; (base - k)::jm]) (flip ji)
      in flip kji |> List.concat_map ~f:(fun ojm -> [l::ojm; (base + 1 - l)::ojm])

  (* E.g. width 4 and base 17, suppose 876 is selected for ijk, l cannot be 6, 7, 8, 9. *)
  let iter_possible_lijk ijk ~f =
    for l = 2 to base / 2 do
      if List.for_all ijk ~f:(fun k -> l <> k && l <> k + 1) then
        l :: ijk |> f
    done

  exception Out_of_range of int
  let print_int_in_base wxyz =
    let show_digit digit =
      Char.of_int_exn(
        if digit <= 9 then Char.to_int '0' + digit else
        if digit <= 35 then Char.to_int 'A' + (digit - 10)
          else raise (Out_of_range digit)) in
    List.iter wxyz ~f:(fun x -> show_digit x |> print_char) 

  (* Note that only EFGHLKJI are in the solution,
     the remaining digits are generated in printing a solution. *)
  let print_sol solution =
    let (efgh, l::kji) = List.split_n solution width in
    let (ijkl, mnop) =
      let rec build ji (kl, p) = match ji with
        | j::i -> build i (j::kl, (base - j)::p)
        | [] -> (kl, p) in
      build kji ([l], [base + 1 -l]) in
    let (false, abcd) =
      List.fold2_exn (List.rev efgh) (l::kji) ~init:(false, []) ~f:(fun (carry, d) g k ->
        let digit_difference = k + if carry then 1 else 0 in
        let (c, carry) = if g + digit_difference > biggest_digit
          then (g + digit_difference - base, true)
          else (g + digit_difference, false) in
        (carry, c::d)
    ) in 
    print_int_in_base abcd; print_string " - ";
    print_int_in_base efgh; print_string " = ";
    print_int_in_base ijkl; print_string ", ";
    print_int_in_base ijkl; print_string " + ";
    print_int_in_base mnop; print_string " = ";
    List.init (width + 1) (fun _ -> 1) |> print_int_in_base;
    print_newline ()

  let flip ref_int index =
    ref_int := Int.bit_xor !ref_int (Int.shift_left 1 index)

  let get ref_int index =
    Int.bit_and !ref_int (Int.shift_left 1 index) <> 0

  (* Suppose we have 9762 as IJKL, we know either 2 + H = D (no carrying) or 2 + H = D + base (carrying)
     Without carrying, (H, D) can be (0, 2), (1, 3) to (14, 16) in base 17, as in the first for loop
     With carrying, (H, D) can be (15, 0), (16, 1), in the second for loop.

     Then the pairs will be checked if they are availabe and recursively go to next column.
     Suppose we assumed (H, D) as (15, 0), then either 7 + G = C or 7 + G = C + base... you know where this is going. *)
  let iterate_solution_from_lkji ~new_sol = function
    (* new_sol is called when a solution is found *)
    | [] -> assert false
    | l::kji ->
      (* ..11111101, the second last digit is 0 as 1 is used *)
      let available = ref (-3) in
      let () =
        flip available l; flip available (base + 1 - l);
        List.iter kji ~f:(fun k -> flip available k; flip available (base - k)) in 
      let rec go_deeper carry base partial_solution = function
        | [i] ->
          let digit_difference = i + if carry then 1 else 0 in
          for e = 2 to biggest_digit - digit_difference do
            let a = e + digit_difference in
              if get available e && get available a then
                new_sol (e::partial_solution)
          done
        | k::ji ->
          let digit_difference = k + if carry then 1 else 0 in
          let max_g_without_carry = base - digit_difference - 1 in
          for g = 0 to max_g_without_carry do
            let c = g + digit_difference in 
            if get available g && get available c then (
              flip available g; flip available c;
              go_deeper false base (g::partial_solution) ji;
              flip available g; flip available c
            )
          done;
          for g = (max_g_without_carry + 1) to biggest_digit do
            let c = g + digit_difference - base in 
            if get available g && get available c then (
              flip available g; flip available c;
              go_deeper true base (g::partial_solution) ji;
              flip available g; flip available c
            ) (* manual inlining, im really desperate *)
          done;
        | [] -> assert false in
      go_deeper false base (l::kji) (l::kji)

  let count = ref 0
  let print = ref true
  let lkjis = Array.create ~len:worker_num []
  let current = ref 0

  let do_in_local = 
    iterate_solution_from_lkji
      ~new_sol:(fun sol ->
        count:= !count + 1;
        if !print then (
          (* ! in OCaml does not mean not, but is the operator getting the content of a ref cell *)
          print_sol sol;
          if !count = 50 then print := false
        )
      )

  let solve () =
    (* With base 17, {{I, M}, {J, N}, {K, O}} is a subset of {{2, 15}, {3, 14}... {8, 9}} *)
    List.range ~stop:`inclusive 2 (biggest_digit/2)
    (* So we permute the smaller half of the digits first *)
    |> perm_cps (width - 1) ~f:(fun ijk ->
      (* then add the possible l's *)
      iter_possible_lijk ijk ~f:(fun lijk ->
        lijk
        |> generate_flipped (* and flip to the bigger digits *)
        |> List.iter ~f: (fun lkji ->
          if !print then do_in_local lkji
          else (
            current := !current + 1;
            (* prepare the work for forked workers *)
            let c = !current % worker_num in lkjis.(c) <- lkji :: lkjis.(c)
          )
        )
      )
    );
    lkjis |> Array.to_list
    (* ac means that the way of combining results, addition, is associative and commutative *)
    |> map_fold_ac ~fold:(+) !count ~f:(
      let count = ref 0 in
      fun lkjis -> List.iter lkjis ~f:
        (iterate_solution_from_lkji ~new_sol:(fun _ -> count := !count + 1));
      !count
    )

end