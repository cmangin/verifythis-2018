type t = {
  mutable buf : int array;
  mutable l : int;
  mutable r : int;
}

let left (b: t) =
  if b.l <> 0 then (
    b.l <- b.l - 1;
    b.r <- b.r - 1;
    b.buf.(b.r) <- b.buf.(b.l)
  )

let right (b: t) =
  if b.r <> Array.length b.buf then (
    b.buf.(b.l) <- b.buf.(b.r);
    b.l <- b.l + 1;
    b.r <- b.r + 1
  )

let insert (b: t) (x: int) =
  if b.l = b.r then assert false
  else (
    b.buf.(b.l) <- x;
    b.l <- b.l + 1
  )

let delete (b: t) =
  if b.l <> 0 then (
    b.l <- b.l - 1
  )
