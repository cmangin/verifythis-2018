
let sort (a : int array) : unit =
  let i = ref 0 in
  while !i < Array.length a - 1 do

    let x = ref a.(!i) in
    let y = ref a.(!i + 1) in
(*
    let x, y =
      if x < y then x, y else y, x
    in
*)
    if !x < !y then begin
      let tmp = !x in
      x := !y; y := tmp
    end;

    let j = ref (!i - 1) in
    while !j >= 0 && a.(!j) > !x do
      a.(!j + 2) <- a.(!j);
      decr j
    done;
    a.(!j + 2) <- !x;

    while !j >= 0 && a.(!j) > !y do
      a.(!j + 1) <- a.(!j);
      decr j
    done;
    a.(!j + 1) <- !y;
    
    i := !i + 2
  done;

  if !i = Array.length a - 1 then begin
    let y = a.(!i) in
    let j = ref (!i - 1) in

    while !j >= 0 && a.(!j) > y do
      a.(!j + 1) <- a.(!j);
      decr j
    done;
    a.(!j + 1) <- y
  end
