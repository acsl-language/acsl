struct buffer { int pos ; char buf[80]; } line;

/*@ requires 80 > line.pos >= 0 ;
  @ assigns line
      \from line = { line for buf = { line.buf for [line.pos] = '\0' };
  @*/
void add_eol() {
  line.buf[line.pos] = '\0' ;
}
