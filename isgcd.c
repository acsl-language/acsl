predicate is_gcd(integer a, integer b, integer d) {
  case gcd_zero: 
    \forall integer n; is_gcd(n,0,n)
  case gcd_succ: 
    \forall integer a,b,d; is_gcd(b, a % b, d) ==> is_gcd(a,b,d)
}
