#include <type_traits>

template<class T> class list {
  list<T>* next;
  T value;

public:

  //@ int length() = 1 + (next == nullptr ? 0: next.length());

  //@ ensures \result == length();
  int length();

  /*@ int intsum() =
    static_cast<int>(value) + (next == nullptr ? 0 : next.intsum());
   */

  //@ ensures std::is_same_type<T,int>::value ==> \result == intsum();
  int intsum();

}
