#include <vector>
#include <algorithm>

extern std::vector<int> f(int);

int main() {
  int sum = 0;
  auto op = [=](int i) mutable { sum += i; return -i; };
  std::vector<int> a = f(0);
  std::vector<int> b = f(1);

  std::transform(a.begin(), a.end(), b.begin(), op);
}
