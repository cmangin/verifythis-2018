(* Insert [x] in array [a], assuming [0, hi[ is sorted and [hi, hi + shift[
 * can be rewritten. Will leave a hole of size [shift - 1] and
 * return a position [j] such that [a.(j + shift)] is [x], and the hole is
 * in [j, j + shift - 1[. Leaves [hi + shift, length a[ unchanged. *)

let insert (a : int array) (x : int) (j : int ref) (shift : int) : unit =
  while !j >= 0 && a.(!j) > x do
    a.(!j + shift) <- a.(!j);
    decr j
  done;
  a.(!j + shift) <- x

let sort (a : int array) : unit =
  let i = ref 0 in
  while !i < Array.length a - 1 do

    let x = ref a.(!i) in
    let y = ref a.(!i + 1) in
    
    if !x < !y then begin
      let tmp = !x in
      x := !y; y := tmp
    end;

    let j = ref (!i - 1) in
    insert a !x j 2;
    insert a !y j 1;
    
    i := !i + 2
  done;

  if !i = Array.length a - 1 then begin
    let y = a.(!i) in
    let j = ref (!i - 1) in
    insert a y j 1
  end
