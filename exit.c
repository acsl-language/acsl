/*@ assigns \nothing;
  @ ensures \false;
  @ exits   \exit_status == status;
  @*/
void exit(int status);

int status;

/*@ assigns status;
  @ exits   !cond && \exit_status == 1 && status == val;
  @*/
void may_exit(int cond, int val) {
  if (! cond) {
    status = val;
    exit(1);
    }
}
