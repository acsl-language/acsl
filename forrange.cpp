#include <list>
void m(std::list<int>& data) {
   for (auto value: data) {
      int i = value;
      value = i+1;
   }

   int k = 0;
   for (int j : {1,2,3,5,6,7}) {
      k += j;
   }
}

int main() {
}
