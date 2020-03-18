int a ;                      // a non-ghost location
/*@ ghost
  int* good = &a ;           // can be referenced by a pointer to non-ghost
  int \ghost* bad = &a ;     // cannot be referenced by a pointer to ghost
*/
/*@ ghost
  int g ;                    // a ghost location
  int \ghost* good = &a ;    // can be referenced by a pointer to ghost
  int * bad = &a ;           // cannot be referenced by a pointer to non-ghost
*/
