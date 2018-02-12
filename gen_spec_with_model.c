/* public interface */

//@ model set<integer> forbidden = \empty;

/*@ assigns forbidden;
  @ ensures ! (\result \in \old(forbidden))
  @   && \result \in forbidden && \subset(\old(forbidden),forbidden);
  @*/
int gen();
