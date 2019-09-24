class Array {
private:
  int* data;
  int data_length;

public:
  /*@ // These each have a single implicit logic label {L}
    logic int length() = \this.data_length;
    logic int value(int index) = \this.data[index];
  */

  /*@
    requires 0 <= index < length();
    ensures \result == value(index);
  */
  int getValue(int index) {
    return data[index];
  }
}
