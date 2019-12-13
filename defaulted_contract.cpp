class C {
  public:
  //@ logic integer value;

  /*@
    @    requires \true;
    @    assigns \nothing;
    @    ensures this->value == that->value;
    @*/
  C(const C& that) = default;
};
