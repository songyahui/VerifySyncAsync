hiphop module Present (out S1, out S2) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {S1,S2}
@*/
{
  emit S1; 
  present S1 then emit S2
  else emit S2
  end present
}

hiphop module Present1 (out S1, out S2) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {S1}.{S2}
@*/
{
  emit S1; 
  present S1 then yield; emit S2
  else yield; emit S1; 
  end present
}

hiphop module Present2 (out S1, out S2) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {S2}.{S1}
@*/
{
  emit S2; 
  present S1 then yield; emit S2
  else yield; emit S1; 
  end present
}
