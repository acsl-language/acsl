#include<vector>

extern vector<int> f(int);

int main() {
  int sum = 0;
  auto op = [](int i) mutable { sum += i; return -i; }
  vector<int> a = f(0);
  vector<int> b = f(1);

  std::transform(a.begin(), a.end(), b.begin(), op);
}
