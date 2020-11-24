hiphop module prg() 
/*@
  require TRUE /\ emp 
  ensure TRUE /\ ({L(1)})^w
  @*/
{
   loop {
      signal L;

      emit L(1);
      yield;
   }
}