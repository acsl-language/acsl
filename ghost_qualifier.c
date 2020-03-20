int a ;                       // a non-ghost location
/*@ ghost
  int* good0 = &a ;           // can be referenced by a pointer to non-ghost
  int \ghost* bad0 = &a ;     // cannot be referenced by a pointer to ghost
*/
/*@ ghost
  int g ;                     // a ghost location
  int \ghost* good1 = &a ;    // can be referenced by a pointer to ghost
  int * bad1 = &a ;           // cannot be referenced by a pointer to non-ghost
*/
