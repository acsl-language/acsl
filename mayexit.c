//NOPP-BEGIN
int status;
//NOPP-END
/*@ behavior no_exit :
  @   assumes cond;
  @   assigns \nothing;
  @   exits   \false;
  @ behavior no_return :
  @   assumes !cond;
  @   assigns status;
  @   exits   \exit_status == 1 && status == val;
  @   ensures \false;
  @*/
void may_exit(int cond, int val) ;
