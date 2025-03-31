int a ;                       // a non-ghost location
/*@ ghost
  int* good0 = &a ;           // can be referenced by a pointer to non-ghost
//NOPP-BEGIN
#if !defined(ONLYGOODDECLS)
//NOPP-END
  int \ghost* bad0 = &a ;     // cannot be referenced by a pointer to ghost
//NOPP-BEGIN
#endif
//NOPP-END
*/
/*@ ghost
  int g ;                     // a ghost location
  int \ghost* good1 = &g ;    // can be referenced by a pointer to ghost
//NOPP-BEGIN
#if !defined(ONLYGOODDECLS)
//NOPP-END
  int * bad1 = &g ;           // cannot be referenced by a pointer to non-ghost
//NOPP-BEGIN
#endif
//NOPP-END
*/
