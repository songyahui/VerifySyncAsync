hiphop module prg() 
/*@
  require TRUE /\ {OPEN} 
  ensure TRUE /\ {}.{CLOSE} 
  @*/
{
   loop {
      signal L;

      emit L(1);
      yield;
   }
}