hiphop module Await (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {A}
@*/
{
  emit C; 
  (yield; emit A) 
  ||
  (await A)
}