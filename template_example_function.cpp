#include <type_traits>

/*@ behavior int :
  assume std::is_same_type<M,int>::value;
  ensures \result == (a > b ? a : b);
*/

template <class M> M larger(M a, M b) {
  return a > b ? a : b;
}
