#include <list>

extern std::list<int> f(void);

void m() {
  int k = 0;
  /*@
    loop invariant 0 <= \count <= 6;
    loop invariant k == \sum(0,\count-1,\lambda integer j; \data[j]);
    loop variant 6 -\count;
  @*/
  for (int i: {1,2,3,6,7,8}) {
    k += i;
  }

  k = 0;
  std::list<int> data = f();
  size_t len = data.size();
  /*@
    loop invariant 0 <= \count <= len;
    loop invariant k == \sum(0,\count-1,
                \lambda integer j; *(\data.begin()+j));
    loop variant len - j;
  @*/
  for (auto value: data) {
    k += value;
  }
}
