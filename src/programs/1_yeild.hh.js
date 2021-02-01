hiphop module Yield (out S) 
/*@
  require TRUE /\ {}
  ensure TRUE /\ {S}.{}
@*/
{
  emit S; yield
}
