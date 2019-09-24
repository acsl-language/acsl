//@ logic bool negate(bool b) = !b;
//@ logic boolean lnegate(boolean b) = !b;
//@ predicate P(bool b) = b;
//@ predicate LP(boolean b) = b;

void m() {

  //@ assert \true == true;
  //@ assert \false == false;
  //@ assert \null == nullptr;

  //@ assert LP(true);
  //@ assert LP(\true);
  //@ assert P(true);
  //@ assert P((bool)\true);

  //@ assert lnegate(false);
  //@ assert lnegate(\false);
  //@ assert negate(false);
  //@ assert negate((bool)\false);
}
