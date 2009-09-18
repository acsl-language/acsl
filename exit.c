/*@ assigns \nothing;
  @ ensures \false;
  @ exits   \result == status;
  @*/
void exit(int status);

int status;

/*@ assigns status;
  @ exits   !cond && \result == 1 && status == val;
  @*/
void may_exit(int cond, int val) {
  if (! cond) {
    status = val;
    exit(1);
    }
}
