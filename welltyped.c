int* f (int x);

int main() {
  int* (*p)(int) = &f;
  //@ assert \valid_function((int* (*)(int)) p); // true
  //@ assert \valid_function((int* (*)()) p); // true (see C99 6.7.5.3:15)

  //@ assert !\valid_function((void* (*)(int)) p);
    // not compatible: void* and int* are not compatible (see C99 6.7.5.1:2)

  //@ assert !\valid_function((volatile int* (*)(int)) p);
    // not compatible: qualifiers cannot be dropped (see C99 6.7.3:9)
  return *(p(0));
}
