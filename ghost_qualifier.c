int a ;
int * p ; // a pointer to non-const
p = &a ;   // can only point to a non-const location

//@ ghost int g ;
//@ ghost int \ghost * pg ; // a pointer to ghost
//@ ghost pg = &g ;          // can only point to a ghost location

int const c = 42 ;

int const* cp ;           // a pointer to a const location
cp = &c ;                 // can point either to a const location
cp = &a ;                 // or to a non const location

//@ ghost int * other ;   // a pointer to a non-ghost location
//@ ghost other = & a ;  // can point either to a non-ghost location
//@ ghost other = & g ;  // or to a ghost location

// a pointer to non-const location cannot point to a const location
int * invalid = &c ;
// a pointer to ghost location cannot point to a non-ghost location
//@ ghost int \ghost * invalid = & a ;