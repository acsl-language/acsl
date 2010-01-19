/* public interface */

//@ model set<integer> forbidden = \empty;

/*@ assigns forbidden;
  @ ensures ! \subset(\result,\old(forbidden))
  @   && \subset(\result,forbidden) && \subset(\old(forbidden),forbidden);
  @*/
int gen();
