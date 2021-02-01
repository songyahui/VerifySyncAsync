hiphop module Loop (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {A}.({B}.{C}.{})^*
@*/
{
  emit A;
  loop 
  yield; emit B; yield; emit C ;yield
  end loop 
}

hiphop module Loop1 (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {A}.({B}.{C})^*
@*/
{
  emit A;
  loop 
  yield; emit B; yield; emit C 
  end loop 
}


hiphop module Loop2 (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {A,B}.({C}.{B})^*
@*/
{
  emit A;
  loop 
  emit B; yield; emit C ;yield
  end loop 
}

hiphop module Loop3 (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {A,B}.({C}.{A,B})^*
@*/
{
  emit A;
  loop 
  emit B; yield; emit C; yield; emit A
  end loop 
}



