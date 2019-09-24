#include <list>

extern std::list<int> f(void)

void m() {
  int k = 0;
  for (int i: {1,2,3,6,7,8}) {
      k += i;
  }

  k = 0;
  std::list<int> data = f();
  for (auto value: data) {
     k += value;
  }
}
