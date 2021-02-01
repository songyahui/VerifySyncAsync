hiphop module Par (out S1, out S2) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {S1,S2}.{}
@*/
{
  (emit S1; yield)
  ||
  (emit S2)
}
