struct buffer { int pos ; char buf[80]; } line;

/*@ requires 80 > line.pos >= 0 ;
  @ assigns line
  @   \from line = 
         { line \with .buf = 
                { line.buf \with [line.pos] = (char)'\0' } };
  @*/
void add_eol() {
  line.buf[line.pos] = '\0' ;
}
