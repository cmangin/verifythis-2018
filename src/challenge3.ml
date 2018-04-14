let fetch_and_add next =
  let x = !next in
  incr next;
  x

let abql_acquire next n pass =
  let my_ticket = (fetch_and_add next) mod n in
  while not pass.(my_ticket) do
    ()
  done;
  pass.(my_ticket) <- false;
  my_ticket

let abql_release n pass my_ticket =
  pass.((my_ticket + 1) mod n) <- true
