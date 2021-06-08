/*@ terminates \true;
  @ assigns \nothing;
  @ ensures \false;
  @ exits   \exit_status == status;
  @*/
void exit(int status);

int status;

/*@ terminates \true;
  @ assigns status;
  @ exits   !cond && \exit_status == 1 && status == val;
  @ ensures  cond && status == \old(status);
  @*/
void may_exit(int cond, int val) {
  if (! cond) {
    status = val;
    exit(1);
    }
}
