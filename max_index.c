/*@ logic int max_index{L}(int t[],int n) =
  @   (n==0) ? 0 :
  @   (t[n-1]==0) ? n : max_index(t, n-1);
  @*/
