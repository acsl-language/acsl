class Array {
private:
  int* data;
  int data_length;

public:
  /*@
    requires 0 <= index < data_length;
    assigns \nothing;
    ensures \result == data[index];
  */
  int getValue(int index) {
    return data[index];
  }
}
