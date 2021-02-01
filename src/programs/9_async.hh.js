hiphop module Async (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure t > 2 /\ ({B}.{})#t .{A}
@*/
{
  async A 3 {
    emit B; yield
  }
}


hiphop module Async1 (out A, out B, out C) 
/*@
  require TRUE /\ {}
  ensure t > 2 /\ ({B}.{})#t .{A, C}
@*/
{
  async A 3 {
    emit B; yield
  };
  emit C
}




