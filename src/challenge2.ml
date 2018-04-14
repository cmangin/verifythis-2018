let docount (count : int array) =
  let len = Array.length count in
  count.(0) <- 1;
  count.(1) <- 1;
  count.(2) <- 1;
  count.(3) <- 2;
  for n = 4 to len - 1 do
    count.(n) <- count.(n-1);
    for k = 3 to n - 1 do
      count.(n) <- count.(n) + count.(n - k - 1)
    done;
    count.(n) <- count.(n) + 1
  done
