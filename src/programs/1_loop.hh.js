hiphop module prg() {
   loop {
      signal L;

      emit L( "foo bar" );
      yield;
   }
}