hiphop module prg(in a, out blur, inout c) 
/*@
  require TRUE /\ {OPEN} 
  ensure TRUE /\ {}.{CLOSE} 
  @*/
{
   loop {
      signal L;

      emit L (1);
      yield
   }
}