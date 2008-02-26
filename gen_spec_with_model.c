/* public interface */

//@ open Set;

//@ model set<integer> forbidden = emptyset;

/*@ assigns forbidden;
  @ ensures ! in(\result,\old(forbidden) 
  @   && in(\result,forbidden) && subset(\old(forbidden),forbidden);
  @*/
int gen();
