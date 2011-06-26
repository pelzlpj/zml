
let counter = ref 0

let mktmp () =
  incr counter;
  Printf.sprintf "__tmp%d" !counter

