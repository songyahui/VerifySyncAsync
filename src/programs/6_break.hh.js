hiphop module Break (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {A}.{B}
@*/
{
  trap T in
  emit A; yield; emit B; 
  exit T;
  yield; emit C;
  end trap 
}


