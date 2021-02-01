hiphop module Abort (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure t < 4 /\ ({A}.{})#t .{B}
@*/
{
  abort 
  emit A; yield
  when 3 ;
  emit B
}


hiphop module Abort1 (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure t < 4 /\ ({A}.{})#t 
@*/
{
  abort 
  emit A; yield
  when 3 
}


