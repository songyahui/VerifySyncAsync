hiphop module Trap (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {A}.{B}.{C}
@*/
{
  trap T in
  emit A; yield; emit B; yield; emit C;
  end trap 
}


